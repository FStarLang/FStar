open Prims
type match_result =
  | MisMatch of (FStar_Syntax_Syntax.delta_depth
  FStar_Pervasives_Native.option * FStar_Syntax_Syntax.delta_depth
  FStar_Pervasives_Native.option) 
  | HeadMatch of Prims.bool 
  | FullMatch 
let (uu___is_MisMatch : match_result -> Prims.bool) =
  fun projectee ->
    match projectee with | MisMatch _0 -> true | uu___ -> false
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | MisMatch _0 -> _0
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee ->
    match projectee with | HeadMatch _0 -> true | uu___ -> false
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee -> match projectee with | HeadMatch _0 -> _0
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee -> match projectee with | FullMatch -> true | uu___ -> false
type implicit_checking_status =
  | Implicit_unresolved 
  | Implicit_checking_defers_univ_constraint 
  | Implicit_has_typing_guard of (FStar_Syntax_Syntax.term *
  FStar_Syntax_Syntax.typ) 
let (uu___is_Implicit_unresolved : implicit_checking_status -> Prims.bool) =
  fun projectee ->
    match projectee with | Implicit_unresolved -> true | uu___ -> false
let (uu___is_Implicit_checking_defers_univ_constraint :
  implicit_checking_status -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Implicit_checking_defers_univ_constraint -> true
    | uu___ -> false
let (uu___is_Implicit_has_typing_guard :
  implicit_checking_status -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Implicit_has_typing_guard _0 -> true
    | uu___ -> false
let (__proj__Implicit_has_typing_guard__item___0 :
  implicit_checking_status ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ))
  =
  fun projectee -> match projectee with | Implicit_has_typing_guard _0 -> _0
type tagged_implicits =
  (FStar_TypeChecker_Common.implicit * implicit_checking_status) Prims.list
let (is_base_type :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun env ->
    fun typ ->
      let t = FStar_TypeChecker_Normalize.unfold_whnf env typ in
      let uu___ = FStar_Syntax_Util.head_and_args t in
      match uu___ with
      | (head, args) ->
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_Syntax_Util.un_uinst head in
              FStar_Syntax_Util.unascribe uu___3 in
            uu___2.FStar_Syntax_Syntax.n in
          (match uu___1 with
           | FStar_Syntax_Syntax.Tm_name uu___2 -> true
           | FStar_Syntax_Syntax.Tm_fvar uu___2 -> true
           | FStar_Syntax_Syntax.Tm_type uu___2 -> true
           | uu___2 -> false)
let (print_ctx_uvar : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar -> FStar_Syntax_Print.ctx_uvar_to_string ctx_uvar
let (binders_as_bv_set :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.bv FStar_Compiler_Util.set)
  =
  fun bs ->
    let uu___ =
      FStar_Compiler_List.map (fun b -> b.FStar_Syntax_Syntax.binder_bv) bs in
    FStar_Compiler_Util.as_set uu___ FStar_Syntax_Syntax.order_bv
type lstring = Prims.string FStar_Thunk.t
let (mklstr : (unit -> Prims.string) -> Prims.string FStar_Thunk.thunk) =
  fun f ->
    let uf = FStar_Syntax_Unionfind.get () in
    FStar_Thunk.mk
      (fun uu___ ->
         let tx = FStar_Syntax_Unionfind.new_transaction () in
         FStar_Syntax_Unionfind.set uf;
         (let r = f () in FStar_Syntax_Unionfind.rollback tx; r))
type uvi =
  | TERM of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term) 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar *
  FStar_Syntax_Syntax.universe) 
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee -> match projectee with | TERM _0 -> true | uu___ -> false
let (__proj__TERM__item___0 :
  uvi -> (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term)) =
  fun projectee -> match projectee with | TERM _0 -> _0
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee -> match projectee with | UNIV _0 -> true | uu___ -> false
let (__proj__UNIV__item___0 :
  uvi -> (FStar_Syntax_Syntax.universe_uvar * FStar_Syntax_Syntax.universe))
  = fun projectee -> match projectee with | UNIV _0 -> _0
type defer_ok_t =
  | NoDefer 
  | DeferAny 
  | DeferFlexFlexOnly 
let (uu___is_NoDefer : defer_ok_t -> Prims.bool) =
  fun projectee -> match projectee with | NoDefer -> true | uu___ -> false
let (uu___is_DeferAny : defer_ok_t -> Prims.bool) =
  fun projectee -> match projectee with | DeferAny -> true | uu___ -> false
let (uu___is_DeferFlexFlexOnly : defer_ok_t -> Prims.bool) =
  fun projectee ->
    match projectee with | DeferFlexFlexOnly -> true | uu___ -> false
let (string_of_defer_ok : defer_ok_t -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | NoDefer -> "NoDefer"
    | DeferAny -> "DeferAny"
    | DeferFlexFlexOnly -> "DeferFlexFlexOnly"
type worklist =
  {
  attempting: FStar_TypeChecker_Common.probs ;
  wl_deferred:
    (Prims.int * FStar_TypeChecker_Common.deferred_reason * lstring *
      FStar_TypeChecker_Common.prob) Prims.list
    ;
  wl_deferred_to_tac:
    (Prims.int * FStar_TypeChecker_Common.deferred_reason * lstring *
      FStar_TypeChecker_Common.prob) Prims.list
    ;
  ctr: Prims.int ;
  defer_ok: defer_ok_t ;
  smt_ok: Prims.bool ;
  umax_heuristic_ok: Prims.bool ;
  tcenv: FStar_TypeChecker_Env.env ;
  wl_implicits: FStar_TypeChecker_Common.implicits ;
  repr_subcomp_allowed: Prims.bool }
let (__proj__Mkworklist__item__attempting :
  worklist -> FStar_TypeChecker_Common.probs) =
  fun projectee ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits; repr_subcomp_allowed;_} ->
        attempting
let (__proj__Mkworklist__item__wl_deferred :
  worklist ->
    (Prims.int * FStar_TypeChecker_Common.deferred_reason * lstring *
      FStar_TypeChecker_Common.prob) Prims.list)
  =
  fun projectee ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits; repr_subcomp_allowed;_} ->
        wl_deferred
let (__proj__Mkworklist__item__wl_deferred_to_tac :
  worklist ->
    (Prims.int * FStar_TypeChecker_Common.deferred_reason * lstring *
      FStar_TypeChecker_Common.prob) Prims.list)
  =
  fun projectee ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits; repr_subcomp_allowed;_} ->
        wl_deferred_to_tac
let (__proj__Mkworklist__item__ctr : worklist -> Prims.int) =
  fun projectee ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits; repr_subcomp_allowed;_} ->
        ctr
let (__proj__Mkworklist__item__defer_ok : worklist -> defer_ok_t) =
  fun projectee ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits; repr_subcomp_allowed;_} ->
        defer_ok
let (__proj__Mkworklist__item__smt_ok : worklist -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits; repr_subcomp_allowed;_} ->
        smt_ok
let (__proj__Mkworklist__item__umax_heuristic_ok : worklist -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits; repr_subcomp_allowed;_} ->
        umax_heuristic_ok
let (__proj__Mkworklist__item__tcenv : worklist -> FStar_TypeChecker_Env.env)
  =
  fun projectee ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits; repr_subcomp_allowed;_} ->
        tcenv
let (__proj__Mkworklist__item__wl_implicits :
  worklist -> FStar_TypeChecker_Common.implicits) =
  fun projectee ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits; repr_subcomp_allowed;_} ->
        wl_implicits
let (__proj__Mkworklist__item__repr_subcomp_allowed : worklist -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits; repr_subcomp_allowed;_} ->
        repr_subcomp_allowed
let (as_deferred :
  (Prims.int * FStar_TypeChecker_Common.deferred_reason * lstring *
    FStar_TypeChecker_Common.prob) Prims.list ->
    FStar_TypeChecker_Common.deferred)
  =
  fun wl_def ->
    FStar_Compiler_List.map
      (fun uu___ ->
         match uu___ with
         | (uu___1, reason, m, p) ->
             let uu___2 = FStar_Thunk.force m in (reason, uu___2, p)) wl_def
let (as_wl_deferred :
  worklist ->
    FStar_TypeChecker_Common.deferred ->
      (Prims.int * FStar_TypeChecker_Common.deferred_reason * lstring *
        FStar_TypeChecker_Common.prob) Prims.list)
  =
  fun wl ->
    fun d ->
      FStar_Compiler_List.map
        (fun uu___ ->
           match uu___ with
           | (reason, m, p) ->
               let uu___1 = FStar_Thunk.mkv m in
               ((wl.ctr), reason, uu___1, p)) d
let (new_uvar :
  Prims.string ->
    worklist ->
      FStar_Compiler_Range.range ->
        FStar_Syntax_Syntax.binding Prims.list ->
          FStar_Syntax_Syntax.binder Prims.list ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
              FStar_Syntax_Syntax.should_check_uvar ->
                (FStar_Syntax_Syntax.ctx_uvar FStar_Pervasives_Native.option,
                  unit) FStar_Pervasives.either ->
                  FStar_Syntax_Syntax.ctx_uvar_meta_t
                    FStar_Pervasives_Native.option ->
                    (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term
                      * worklist))
  =
  fun reason ->
    fun wl ->
      fun r ->
        fun gamma ->
          fun binders ->
            fun k ->
              fun should_check ->
                fun kind ->
                  fun meta ->
                    let decoration =
                      {
                        FStar_Syntax_Syntax.uvar_decoration_typ = k;
                        FStar_Syntax_Syntax.uvar_decoration_should_check =
                          should_check;
                        FStar_Syntax_Syntax.uvar_decoration_kind = kind
                      } in
                    let ctx_uvar =
                      let uu___ = FStar_Syntax_Unionfind.fresh decoration r in
                      {
                        FStar_Syntax_Syntax.ctx_uvar_head = uu___;
                        FStar_Syntax_Syntax.ctx_uvar_gamma = gamma;
                        FStar_Syntax_Syntax.ctx_uvar_binders = binders;
                        FStar_Syntax_Syntax.ctx_uvar_reason = reason;
                        FStar_Syntax_Syntax.ctx_uvar_range = r;
                        FStar_Syntax_Syntax.ctx_uvar_meta = meta
                      } in
                    FStar_TypeChecker_Common.check_uvar_ctx_invariant reason
                      r true gamma binders;
                    (let t =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_uvar
                            (ctx_uvar, ([], FStar_Syntax_Syntax.NoUseRange)))
                         r in
                     let imp =
                       {
                         FStar_TypeChecker_Common.imp_reason = reason;
                         FStar_TypeChecker_Common.imp_uvar = ctx_uvar;
                         FStar_TypeChecker_Common.imp_tm = t;
                         FStar_TypeChecker_Common.imp_range = r
                       } in
                     (let uu___2 =
                        FStar_TypeChecker_Env.debug wl.tcenv
                          (FStar_Options.Other "ImplicitTrace") in
                      if uu___2
                      then
                        let uu___3 =
                          FStar_Syntax_Print.uvar_to_string
                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head in
                        FStar_Compiler_Util.print1
                          "Just created uvar (Rel) {%s}\n" uu___3
                      else ());
                     (ctx_uvar, t,
                       {
                         attempting = (wl.attempting);
                         wl_deferred = (wl.wl_deferred);
                         wl_deferred_to_tac = (wl.wl_deferred_to_tac);
                         ctr = (wl.ctr);
                         defer_ok = (wl.defer_ok);
                         smt_ok = (wl.smt_ok);
                         umax_heuristic_ok = (wl.umax_heuristic_ok);
                         tcenv = (wl.tcenv);
                         wl_implicits = (imp :: (wl.wl_implicits));
                         repr_subcomp_allowed = (wl.repr_subcomp_allowed)
                       }))
let (copy_uvar :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        worklist ->
          (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term *
            worklist))
  =
  fun u ->
    fun bs ->
      fun t ->
        fun wl ->
          let env =
            let uu___ = wl.tcenv in
            {
              FStar_TypeChecker_Env.solver =
                (uu___.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax = (uu___.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
                (uu___.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
              FStar_TypeChecker_Env.universe_of =
                (uu___.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
                (uu___.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
              FStar_TypeChecker_Env.teq_nosmt_force =
                (uu___.FStar_TypeChecker_Env.teq_nosmt_force);
              FStar_TypeChecker_Env.subtype_nosmt_force =
                (uu___.FStar_TypeChecker_Env.subtype_nosmt_force);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe = (uu___.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___.FStar_TypeChecker_Env.erasable_types_tab);
              FStar_TypeChecker_Env.enable_defer_to_tac =
                (uu___.FStar_TypeChecker_Env.enable_defer_to_tac);
              FStar_TypeChecker_Env.unif_allow_ref_guards =
                (uu___.FStar_TypeChecker_Env.unif_allow_ref_guards);
              FStar_TypeChecker_Env.erase_erasable_args =
                (uu___.FStar_TypeChecker_Env.erase_erasable_args);
              FStar_TypeChecker_Env.core_check =
                (uu___.FStar_TypeChecker_Env.core_check)
            } in
          let env1 = FStar_TypeChecker_Env.push_binders env bs in
          let uu___ = FStar_TypeChecker_Env.all_binders env1 in
          let uu___1 = FStar_Syntax_Util.ctx_uvar_should_check u in
          new_uvar
            (Prims.op_Hat "copy:" u.FStar_Syntax_Syntax.ctx_uvar_reason) wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu___ t uu___1
            (FStar_Pervasives.Inl FStar_Pervasives_Native.None)
            u.FStar_Syntax_Syntax.ctx_uvar_meta
type solution =
  | Success of (FStar_TypeChecker_Common.deferred *
  FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Common.implicits) 
  | Failed of (FStar_TypeChecker_Common.prob * lstring) 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee -> match projectee with | Success _0 -> true | uu___ -> false
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Common.deferred *
      FStar_TypeChecker_Common.implicits))
  = fun projectee -> match projectee with | Success _0 -> _0
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee -> match projectee with | Failed _0 -> true | uu___ -> false
let (__proj__Failed__item___0 :
  solution -> (FStar_TypeChecker_Common.prob * lstring)) =
  fun projectee -> match projectee with | Failed _0 -> _0
let (extend_wl :
  worklist ->
    FStar_TypeChecker_Common.deferred ->
      FStar_TypeChecker_Common.deferred ->
        FStar_TypeChecker_Common.implicits -> worklist)
  =
  fun wl ->
    fun defers ->
      fun defer_to_tac ->
        fun imps ->
          let uu___ =
            let uu___1 = as_wl_deferred wl defers in
            FStar_Compiler_List.op_At wl.wl_deferred uu___1 in
          let uu___1 =
            let uu___2 = as_wl_deferred wl defer_to_tac in
            FStar_Compiler_List.op_At wl.wl_deferred_to_tac uu___2 in
          {
            attempting = (wl.attempting);
            wl_deferred = uu___;
            wl_deferred_to_tac = uu___1;
            ctr = (wl.ctr);
            defer_ok = (wl.defer_ok);
            smt_ok = (wl.smt_ok);
            umax_heuristic_ok = (wl.umax_heuristic_ok);
            tcenv = (wl.tcenv);
            wl_implicits = (FStar_Compiler_List.op_At wl.wl_implicits imps);
            repr_subcomp_allowed = (wl.repr_subcomp_allowed)
          }
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let (uu___is_COVARIANT : variance -> Prims.bool) =
  fun projectee -> match projectee with | COVARIANT -> true | uu___ -> false
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee ->
    match projectee with | CONTRAVARIANT -> true | uu___ -> false
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee -> match projectee with | INVARIANT -> true | uu___ -> false
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | FStar_TypeChecker_Common.EQ -> "="
    | FStar_TypeChecker_Common.SUB -> "<:"
    | FStar_TypeChecker_Common.SUBINV -> ":>"
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t ->
    let uu___ = FStar_Syntax_Util.head_and_args t in
    match uu___ with
    | (head, args) ->
        (match head.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u, s) ->
             let uu___1 = FStar_Syntax_Print.ctx_uvar_to_string u in
             let uu___2 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu___3 =
                     let uu___4 = FStar_Compiler_List.hd s1 in
                     FStar_Syntax_Print.subst_to_string uu___4 in
                   FStar_Compiler_Util.format1 "@<%s>" uu___3 in
             let uu___3 = FStar_Syntax_Print.args_to_string args in
             FStar_Compiler_Util.format3 "%s%s %s" uu___1 uu___2 uu___3
         | uu___1 -> FStar_Syntax_Print.term_to_string t)
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env ->
    fun uu___ ->
      match uu___ with
      | FStar_TypeChecker_Common.TProb p ->
          let uu___1 =
            let uu___2 =
              FStar_Compiler_Util.string_of_int
                p.FStar_TypeChecker_Common.pid in
            let uu___3 =
              let uu___4 = term_to_string p.FStar_TypeChecker_Common.lhs in
              let uu___5 =
                let uu___6 =
                  let uu___7 = term_to_string p.FStar_TypeChecker_Common.rhs in
                  [uu___7] in
                (rel_to_string p.FStar_TypeChecker_Common.relation) :: uu___6 in
              uu___4 :: uu___5 in
            uu___2 :: uu___3 in
          FStar_Compiler_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu___1
      | FStar_TypeChecker_Common.CProb p ->
          let uu___1 =
            FStar_Compiler_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu___2 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs in
          let uu___3 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs in
          FStar_Compiler_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu___1
            uu___2 (rel_to_string p.FStar_TypeChecker_Common.relation) uu___3
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env ->
    fun uu___ ->
      match uu___ with
      | UNIV (u, t) ->
          let x =
            let uu___1 = FStar_Options.hide_uvar_nums () in
            if uu___1
            then "?"
            else
              (let uu___3 = FStar_Syntax_Unionfind.univ_uvar_id u in
               FStar_Compiler_Effect.op_Bar_Greater uu___3
                 FStar_Compiler_Util.string_of_int) in
          let uu___1 = FStar_Syntax_Print.univ_to_string t in
          FStar_Compiler_Util.format2 "UNIV %s <- %s" x uu___1
      | TERM (u, t) ->
          let x =
            let uu___1 = FStar_Options.hide_uvar_nums () in
            if uu___1
            then "?"
            else
              (let uu___3 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head in
               FStar_Compiler_Effect.op_Bar_Greater uu___3
                 FStar_Compiler_Util.string_of_int) in
          let uu___1 = FStar_TypeChecker_Normalize.term_to_string env t in
          FStar_Compiler_Util.format2 "TERM %s <- %s" x uu___1
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env -> fun uvis -> FStar_Common.string_of_list (uvi_to_string env) uvis
let (names_to_string :
  FStar_Syntax_Syntax.bv FStar_Compiler_Util.set -> Prims.string) =
  fun nms ->
    let uu___ =
      let uu___1 = FStar_Compiler_Util.set_elements nms in
      FStar_Compiler_Effect.op_Bar_Greater uu___1
        (FStar_Compiler_List.map FStar_Syntax_Print.bv_to_string) in
    FStar_Compiler_Effect.op_Bar_Greater uu___ (FStar_String.concat ", ")
let args_to_string :
  'uuuuu . (FStar_Syntax_Syntax.term * 'uuuuu) Prims.list -> Prims.string =
  fun args ->
    let uu___ =
      FStar_Compiler_Effect.op_Bar_Greater args
        (FStar_Compiler_List.map
           (fun uu___1 ->
              match uu___1 with
              | (x, uu___2) -> FStar_Syntax_Print.term_to_string x)) in
    FStar_Compiler_Effect.op_Bar_Greater uu___ (FStar_String.concat " ")
let (empty_worklist : FStar_TypeChecker_Env.env -> worklist) =
  fun env ->
    {
      attempting = [];
      wl_deferred = [];
      wl_deferred_to_tac = [];
      ctr = Prims.int_zero;
      defer_ok = DeferAny;
      smt_ok = true;
      umax_heuristic_ok = true;
      tcenv = env;
      wl_implicits = [];
      repr_subcomp_allowed = false
    }
let (giveup :
  FStar_TypeChecker_Env.env ->
    lstring -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env ->
    fun reason ->
      fun prob ->
        (let uu___1 =
           FStar_Compiler_Effect.op_Less_Bar
             (FStar_TypeChecker_Env.debug env) (FStar_Options.Other "Rel") in
         if uu___1
         then
           let uu___2 = FStar_Thunk.force reason in
           let uu___3 = prob_to_string env prob in
           FStar_Compiler_Util.print2 "Failed %s:\n%s\n" uu___2 uu___3
         else ());
        Failed (prob, reason)
let (giveup_lit :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env ->
    fun reason ->
      fun prob ->
        let uu___ = mklstr (fun uu___1 -> reason) in giveup env uu___ prob
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___ ->
    match uu___ with
    | FStar_TypeChecker_Common.EQ -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV -> FStar_TypeChecker_Common.SUB
let invert :
  'uuuuu .
    'uuuuu FStar_TypeChecker_Common.problem ->
      'uuuuu FStar_TypeChecker_Common.problem
  =
  fun p ->
    {
      FStar_TypeChecker_Common.pid = (p.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element = (p.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (p.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (p.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason = (p.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc = (p.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank = (p.FStar_TypeChecker_Common.rank)
    }
let maybe_invert :
  'uuuuu .
    'uuuuu FStar_TypeChecker_Common.problem ->
      'uuuuu FStar_TypeChecker_Common.problem
  =
  fun p ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___ ->
    match uu___ with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_Compiler_Effect.op_Bar_Greater (maybe_invert p)
          (fun uu___1 -> FStar_TypeChecker_Common.TProb uu___1)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_Compiler_Effect.op_Bar_Greater (maybe_invert p)
          (fun uu___1 -> FStar_TypeChecker_Common.CProb uu___1)
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___ ->
    match uu___ with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          {
            FStar_TypeChecker_Common.pid = (p.FStar_TypeChecker_Common.pid);
            FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.lhs);
            FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
            FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.rhs);
            FStar_TypeChecker_Common.element =
              (p.FStar_TypeChecker_Common.element);
            FStar_TypeChecker_Common.logical_guard =
              (p.FStar_TypeChecker_Common.logical_guard);
            FStar_TypeChecker_Common.logical_guard_uvar =
              (p.FStar_TypeChecker_Common.logical_guard_uvar);
            FStar_TypeChecker_Common.reason =
              (p.FStar_TypeChecker_Common.reason);
            FStar_TypeChecker_Common.loc = (p.FStar_TypeChecker_Common.loc);
            FStar_TypeChecker_Common.rank = (p.FStar_TypeChecker_Common.rank)
          }
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          {
            FStar_TypeChecker_Common.pid = (p.FStar_TypeChecker_Common.pid);
            FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.lhs);
            FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
            FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.rhs);
            FStar_TypeChecker_Common.element =
              (p.FStar_TypeChecker_Common.element);
            FStar_TypeChecker_Common.logical_guard =
              (p.FStar_TypeChecker_Common.logical_guard);
            FStar_TypeChecker_Common.logical_guard_uvar =
              (p.FStar_TypeChecker_Common.logical_guard_uvar);
            FStar_TypeChecker_Common.reason =
              (p.FStar_TypeChecker_Common.reason);
            FStar_TypeChecker_Common.loc = (p.FStar_TypeChecker_Common.loc);
            FStar_TypeChecker_Common.rank = (p.FStar_TypeChecker_Common.rank)
          }
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel ->
    fun uu___ ->
      match uu___ with
      | INVARIANT -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT -> invert_rel rel
      | COVARIANT -> rel
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___ ->
    match uu___ with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___ ->
    match uu___ with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___ ->
    match uu___ with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Compiler_Range.range) =
  fun uu___ ->
    match uu___ with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___ ->
    match uu___ with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___ ->
    match uu___ with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___ ->
    match uu___ with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
let (def_scope_wf :
  Prims.string ->
    FStar_Compiler_Range.range ->
      FStar_Syntax_Syntax.binder Prims.list -> unit)
  =
  fun msg ->
    fun rng ->
      fun r ->
        let uu___ =
          let uu___1 = FStar_Options.defensive () in Prims.op_Negation uu___1 in
        if uu___
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | { FStar_Syntax_Syntax.binder_bv = bv;
                 FStar_Syntax_Syntax.binder_qual = uu___2;
                 FStar_Syntax_Syntax.binder_attrs = uu___3;_}::bs ->
                 (FStar_TypeChecker_Env.def_check_closed_in rng msg prev
                    bv.FStar_Syntax_Syntax.sort;
                  aux (FStar_Compiler_List.op_At prev [bv]) bs) in
           aux [] r)
let (p_scope :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binder Prims.list) =
  fun prob ->
    let r =
      match prob with
      | FStar_TypeChecker_Common.TProb p ->
          let uu___ =
            match p_element prob with
            | FStar_Pervasives_Native.None -> []
            | FStar_Pervasives_Native.Some x ->
                let uu___1 = FStar_Syntax_Syntax.mk_binder x in [uu___1] in
          FStar_Compiler_List.op_At
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu___
      | FStar_TypeChecker_Common.CProb p ->
          let uu___ =
            match p_element prob with
            | FStar_Pervasives_Native.None -> []
            | FStar_Pervasives_Native.Some x ->
                let uu___1 = FStar_Syntax_Syntax.mk_binder x in [uu___1] in
          FStar_Compiler_List.op_At
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu___ in
    def_scope_wf "p_scope" (p_loc prob) r; r
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg ->
    fun prob ->
      fun phi ->
        let uu___ =
          let uu___1 = FStar_Options.defensive () in Prims.op_Negation uu___1 in
        if uu___
        then ()
        else
          (let uu___2 =
             let uu___3 = p_scope prob in
             FStar_Compiler_Effect.op_Less_Bar
               (FStar_Compiler_List.map
                  (fun b -> b.FStar_Syntax_Syntax.binder_bv)) uu___3 in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg uu___2
             phi)
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg ->
    fun prob ->
      fun comp ->
        let uu___ =
          let uu___1 = FStar_Options.defensive () in Prims.op_Negation uu___1 in
        if uu___
        then ()
        else
          (let uu___2 = FStar_Syntax_Util.arrow [] comp in
           def_check_scoped msg prob uu___2)
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg ->
    fun prob ->
      let uu___ =
        let uu___1 = FStar_Options.defensive () in Prims.op_Negation uu___1 in
      if uu___
      then ()
      else
        (let msgf m =
           let uu___2 =
             let uu___3 =
               let uu___4 = FStar_Compiler_Util.string_of_int (p_pid prob) in
               Prims.op_Hat uu___4 (Prims.op_Hat "." m) in
             Prims.op_Hat "." uu___3 in
           Prims.op_Hat msg uu___2 in
         (let uu___3 = msgf "scope" in
          let uu___4 = p_scope prob in
          def_scope_wf uu___3 (p_loc prob) uu___4);
         (let uu___4 = msgf "guard" in
          def_check_scoped uu___4 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu___5 = msgf "lhs" in
                def_check_scoped uu___5 prob p.FStar_TypeChecker_Common.lhs);
               (let uu___5 = msgf "rhs" in
                def_check_scoped uu___5 prob p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu___5 = msgf "lhs" in
                def_check_scoped_comp uu___5 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu___5 = msgf "rhs" in
                def_check_scoped_comp uu___5 prob
                  p.FStar_TypeChecker_Common.rhs))))
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl ->
    fun prob ->
      fun smt_ok ->
        {
          attempting = [prob];
          wl_deferred = (wl.wl_deferred);
          wl_deferred_to_tac = (wl.wl_deferred_to_tac);
          ctr = (wl.ctr);
          defer_ok = (wl.defer_ok);
          smt_ok;
          umax_heuristic_ok = (wl.umax_heuristic_ok);
          tcenv = (wl.tcenv);
          wl_implicits = (wl.wl_implicits);
          repr_subcomp_allowed = (wl.repr_subcomp_allowed)
        }
let wl_of_guard :
  'uuuuu 'uuuuu1 .
    FStar_TypeChecker_Env.env ->
      ('uuuuu * 'uuuuu1 * FStar_TypeChecker_Common.prob) Prims.list ->
        worklist
  =
  fun env ->
    fun g ->
      let uu___ = empty_worklist env in
      let uu___1 =
        FStar_Compiler_List.map
          (fun uu___2 -> match uu___2 with | (uu___3, uu___4, p) -> p) g in
      {
        attempting = uu___1;
        wl_deferred = (uu___.wl_deferred);
        wl_deferred_to_tac = (uu___.wl_deferred_to_tac);
        ctr = (uu___.ctr);
        defer_ok = (uu___.defer_ok);
        smt_ok = (uu___.smt_ok);
        umax_heuristic_ok = (uu___.umax_heuristic_ok);
        tcenv = (uu___.tcenv);
        wl_implicits = (uu___.wl_implicits);
        repr_subcomp_allowed = (uu___.repr_subcomp_allowed)
      }
let (defer :
  FStar_TypeChecker_Common.deferred_reason ->
    lstring -> FStar_TypeChecker_Common.prob -> worklist -> worklist)
  =
  fun reason ->
    fun msg ->
      fun prob ->
        fun wl ->
          {
            attempting = (wl.attempting);
            wl_deferred = (((wl.ctr), reason, msg, prob) :: (wl.wl_deferred));
            wl_deferred_to_tac = (wl.wl_deferred_to_tac);
            ctr = (wl.ctr);
            defer_ok = (wl.defer_ok);
            smt_ok = (wl.smt_ok);
            umax_heuristic_ok = (wl.umax_heuristic_ok);
            tcenv = (wl.tcenv);
            wl_implicits = (wl.wl_implicits);
            repr_subcomp_allowed = (wl.repr_subcomp_allowed)
          }
let (defer_lit :
  FStar_TypeChecker_Common.deferred_reason ->
    Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist)
  =
  fun reason ->
    fun msg ->
      fun prob ->
        fun wl ->
          let uu___ = FStar_Thunk.mkv msg in defer reason uu___ prob wl
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs ->
    fun wl ->
      FStar_Compiler_List.iter (def_check_prob "attempt") probs;
      {
        attempting = (FStar_Compiler_List.op_At probs wl.attempting);
        wl_deferred = (wl.wl_deferred);
        wl_deferred_to_tac = (wl.wl_deferred_to_tac);
        ctr = (wl.ctr);
        defer_ok = (wl.defer_ok);
        smt_ok = (wl.smt_ok);
        umax_heuristic_ok = (wl.umax_heuristic_ok);
        tcenv = (wl.tcenv);
        wl_implicits = (wl.wl_implicits);
        repr_subcomp_allowed = (wl.repr_subcomp_allowed)
      }
let mk_eq2 :
  'uuuuu .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'uuuuu ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist)
  =
  fun wl ->
    fun env ->
      fun prob ->
        fun t1 ->
          fun t2 ->
            let uu___ =
              env.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                env t1 false in
            match uu___ with
            | (tt, uu___1) ->
                let u = env.FStar_TypeChecker_Env.universe_of env tt in
                let uu___2 = FStar_Syntax_Util.mk_eq2 u tt t1 t2 in
                (uu___2, wl)
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___ ->
    match uu___ with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_Compiler_Effect.op_Less_Bar
          (fun uu___1 -> FStar_TypeChecker_Common.TProb uu___1) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_Compiler_Effect.op_Less_Bar
          (fun uu___1 -> FStar_TypeChecker_Common.CProb uu___1) (invert p)
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p ->
    let uu___ =
      FStar_Compiler_Effect.op_Bar_Greater (p_reason p)
        FStar_Compiler_List.length in
    uu___ = Prims.int_one
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Compiler_Util.mk_ref Prims.int_zero in
  fun uu___ ->
    FStar_Compiler_Util.incr ctr; FStar_Compiler_Effect.op_Bang ctr
let mk_problem :
  'uuuuu .
    worklist ->
      FStar_Syntax_Syntax.binder Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'uuuuu ->
            FStar_TypeChecker_Common.rel ->
              'uuuuu ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('uuuuu FStar_TypeChecker_Common.problem * worklist)
  =
  fun wl ->
    fun scope ->
      fun orig ->
        fun lhs ->
          fun rel ->
            fun rhs ->
              fun elt ->
                fun reason ->
                  let scope1 =
                    match elt with
                    | FStar_Pervasives_Native.None -> scope
                    | FStar_Pervasives_Native.Some x ->
                        let uu___ =
                          let uu___1 = FStar_Syntax_Syntax.mk_binder x in
                          [uu___1] in
                        FStar_Compiler_List.op_At scope uu___ in
                  let bs =
                    FStar_Compiler_List.op_At
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1 in
                  let gamma =
                    let uu___ =
                      let uu___1 =
                        FStar_Compiler_List.map
                          (fun b ->
                             FStar_Syntax_Syntax.Binding_var
                               (b.FStar_Syntax_Syntax.binder_bv)) scope1 in
                      FStar_Compiler_List.rev uu___1 in
                    FStar_Compiler_List.op_At uu___
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma in
                  let uu___ =
                    new_uvar
                      (Prims.op_Hat "mk_problem: logical guard for " reason)
                      wl FStar_Compiler_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      (FStar_Syntax_Syntax.Allow_untyped "logical guard")
                      (FStar_Pervasives.Inl FStar_Pervasives_Native.None)
                      FStar_Pervasives_Native.None in
                  match uu___ with
                  | (ctx_uvar, lg, wl1) ->
                      let prob =
                        let uu___1 = next_pid () in
                        {
                          FStar_TypeChecker_Common.pid = uu___1;
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
                        } in
                      (prob, wl1)
let (mk_t_problem :
  worklist ->
    FStar_Syntax_Syntax.binder Prims.list ->
      FStar_TypeChecker_Common.prob ->
        FStar_Syntax_Syntax.typ ->
          FStar_TypeChecker_Common.rel ->
            FStar_Syntax_Syntax.typ ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                Prims.string -> (FStar_TypeChecker_Common.prob * worklist))
  =
  fun wl ->
    fun scope ->
      fun orig ->
        fun lhs ->
          fun rel ->
            fun rhs ->
              fun elt ->
                fun reason ->
                  def_check_prob (Prims.op_Hat reason ".mk_t.arg") orig;
                  (let uu___1 =
                     mk_problem wl scope orig lhs rel rhs elt reason in
                   match uu___1 with
                   | (p, wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_t")
                          (FStar_TypeChecker_Common.TProb p);
                        ((FStar_TypeChecker_Common.TProb p), wl1)))
let (mk_c_problem :
  worklist ->
    FStar_Syntax_Syntax.binder Prims.list ->
      FStar_TypeChecker_Common.prob ->
        FStar_Syntax_Syntax.comp ->
          FStar_TypeChecker_Common.rel ->
            FStar_Syntax_Syntax.comp ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                Prims.string -> (FStar_TypeChecker_Common.prob * worklist))
  =
  fun wl ->
    fun scope ->
      fun orig ->
        fun lhs ->
          fun rel ->
            fun rhs ->
              fun elt ->
                fun reason ->
                  def_check_prob (Prims.op_Hat reason ".mk_c.arg") orig;
                  (let uu___1 =
                     mk_problem wl scope orig lhs rel rhs elt reason in
                   match uu___1 with
                   | (p, wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
let new_problem :
  'uuuuu .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'uuuuu ->
          FStar_TypeChecker_Common.rel ->
            'uuuuu ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Compiler_Range.range ->
                  Prims.string ->
                    ('uuuuu FStar_TypeChecker_Common.problem * worklist)
  =
  fun wl ->
    fun env ->
      fun lhs ->
        fun rel ->
          fun rhs ->
            fun subject ->
              fun loc ->
                fun reason ->
                  let lg_ty =
                    match subject with
                    | FStar_Pervasives_Native.None ->
                        FStar_Syntax_Util.ktype0
                    | FStar_Pervasives_Native.Some x ->
                        let bs =
                          let uu___ = FStar_Syntax_Syntax.mk_binder x in
                          [uu___] in
                        let uu___ =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0 in
                        FStar_Syntax_Util.arrow bs uu___ in
                  let uu___ =
                    let uu___1 = FStar_TypeChecker_Env.all_binders env in
                    new_uvar
                      (Prims.op_Hat "new_problem: logical guard for " reason)
                      {
                        attempting = (wl.attempting);
                        wl_deferred = (wl.wl_deferred);
                        wl_deferred_to_tac = (wl.wl_deferred_to_tac);
                        ctr = (wl.ctr);
                        defer_ok = (wl.defer_ok);
                        smt_ok = (wl.smt_ok);
                        umax_heuristic_ok = (wl.umax_heuristic_ok);
                        tcenv = env;
                        wl_implicits = (wl.wl_implicits);
                        repr_subcomp_allowed = (wl.repr_subcomp_allowed)
                      } loc env.FStar_TypeChecker_Env.gamma uu___1 lg_ty
                      (FStar_Syntax_Syntax.Allow_untyped "logical guard")
                      (FStar_Pervasives.Inl FStar_Pervasives_Native.None)
                      FStar_Pervasives_Native.None in
                  match uu___ with
                  | (ctx_uvar, lg, wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu___1 =
                              let uu___2 =
                                let uu___3 = FStar_Syntax_Syntax.bv_to_name x in
                                FStar_Compiler_Effect.op_Less_Bar
                                  FStar_Syntax_Syntax.as_arg uu___3 in
                              [uu___2] in
                            FStar_Syntax_Syntax.mk_Tm_app lg uu___1 loc in
                      let prob =
                        let uu___1 = next_pid () in
                        {
                          FStar_TypeChecker_Common.pid = uu___1;
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
                        } in
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
  fun orig ->
    fun lhs ->
      fun rel ->
        fun rhs ->
          fun elt ->
            fun reason ->
              let p =
                let uu___ = next_pid () in
                {
                  FStar_TypeChecker_Common.pid = uu___;
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
                } in
              def_check_prob reason (FStar_TypeChecker_Common.TProb p); p
let guard_on_element :
  'uuuuu .
    worklist ->
      'uuuuu FStar_TypeChecker_Common.problem ->
        FStar_Syntax_Syntax.bv ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun wl ->
    fun problem ->
      fun x ->
        fun phi ->
          match problem.FStar_TypeChecker_Common.element with
          | FStar_Pervasives_Native.None ->
              let u =
                (wl.tcenv).FStar_TypeChecker_Env.universe_of wl.tcenv
                  x.FStar_Syntax_Syntax.sort in
              FStar_Syntax_Util.mk_forall u x phi
          | FStar_Pervasives_Native.Some e ->
              let uu___ =
                let uu___1 =
                  let uu___2 =
                    let uu___3 = FStar_Syntax_Syntax.bv_to_name e in
                    (x, uu___3) in
                  FStar_Syntax_Syntax.NT uu___2 in
                [uu___1] in
              FStar_Syntax_Subst.subst uu___ phi
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> lstring -> Prims.string)
  =
  fun env ->
    fun d ->
      fun s ->
        let uu___ =
          (FStar_Compiler_Effect.op_Less_Bar
             (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_Compiler_Effect.op_Less_Bar
               (FStar_TypeChecker_Env.debug env) (FStar_Options.Other "Rel")) in
        if uu___
        then
          let uu___1 =
            FStar_Compiler_Effect.op_Less_Bar
              FStar_Compiler_Range.string_of_range (p_loc d) in
          let uu___2 = prob_to_string env d in
          let uu___3 =
            FStar_Compiler_Effect.op_Bar_Greater (p_reason d)
              (FStar_String.concat "\n\t>") in
          let uu___4 = FStar_Thunk.force s in
          FStar_Compiler_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu___1 uu___2 uu___3 uu___4
        else
          (let d1 = maybe_invert_p d in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ -> "equal to"
             | FStar_TypeChecker_Common.SUB -> "a subtype of"
             | uu___2 -> failwith "impossible" in
           let uu___2 =
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
                   cp.FStar_TypeChecker_Common.rhs in
           match uu___2 with
           | (lhs, rhs) ->
               FStar_Compiler_Util.format3
                 "%s is not %s the expected type %s" lhs rel rhs)
let set_uvar :
  'uuuuu .
    'uuuuu ->
      FStar_Syntax_Syntax.ctx_uvar -> FStar_Syntax_Syntax.term -> unit
  =
  fun env ->
    fun u ->
      fun t ->
        FStar_Syntax_Util.set_uvar u.FStar_Syntax_Syntax.ctx_uvar_head t
let (mark_uvar_as_allow_untyped :
  FStar_Syntax_Syntax.ctx_uvar -> Prims.string -> unit) =
  fun u ->
    fun s ->
      let dec =
        FStar_Syntax_Unionfind.find_decoration
          u.FStar_Syntax_Syntax.ctx_uvar_head in
      (match dec.FStar_Syntax_Syntax.uvar_decoration_kind with
       | FStar_Pervasives.Inl (FStar_Pervasives_Native.Some g_uv) ->
           set_uvar () g_uv FStar_Syntax_Util.t_true
       | uu___1 -> ());
      FStar_Syntax_Unionfind.change_decoration
        u.FStar_Syntax_Syntax.ctx_uvar_head
        {
          FStar_Syntax_Syntax.uvar_decoration_typ =
            (dec.FStar_Syntax_Syntax.uvar_decoration_typ);
          FStar_Syntax_Syntax.uvar_decoration_should_check =
            (FStar_Syntax_Syntax.Allow_untyped s);
          FStar_Syntax_Syntax.uvar_decoration_kind =
            (FStar_Pervasives.Inl FStar_Pervasives_Native.None)
        }
let commit : 'uuuuu . 'uuuuu -> uvi Prims.list -> unit =
  fun env ->
    fun uvis ->
      FStar_Compiler_Effect.op_Bar_Greater uvis
        (FStar_Compiler_List.iter
           (fun uu___ ->
              match uu___ with
              | UNIV (u, t) ->
                  (match t with
                   | FStar_Syntax_Syntax.U_unif u' ->
                       FStar_Syntax_Unionfind.univ_union u u'
                   | uu___1 -> FStar_Syntax_Unionfind.univ_change u t)
              | TERM (u, t) ->
                  ((let uu___2 =
                      FStar_Compiler_List.map
                        (fun b -> b.FStar_Syntax_Syntax.binder_bv)
                        u.FStar_Syntax_Syntax.ctx_uvar_binders in
                    FStar_TypeChecker_Env.def_check_closed_in
                      t.FStar_Syntax_Syntax.pos "commit" uu___2 t);
                   set_uvar env u t)))
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv ->
    fun s ->
      FStar_Compiler_Util.find_map s
        (fun uu___ ->
           match uu___ with
           | UNIV uu___1 -> FStar_Pervasives_Native.None
           | TERM (u, t) ->
               let uu___1 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head in
               if uu___1
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None)
let (find_univ_uvar :
  FStar_Syntax_Syntax.universe_uvar ->
    uvi Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun u ->
    fun s ->
      FStar_Compiler_Util.find_map s
        (fun uu___ ->
           match uu___ with
           | UNIV (u', t) ->
               let uu___1 = FStar_Syntax_Unionfind.univ_equiv u u' in
               if uu___1
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu___1 -> FStar_Pervasives_Native.None)
let (sn' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun t ->
      let uu___ =
        let uu___1 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Reify] env t in
        FStar_Syntax_Subst.compress uu___1 in
      FStar_Compiler_Effect.op_Bar_Greater uu___ FStar_Syntax_Util.unlazy_emb
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun t ->
      let uu___ =
        let uu___1 =
          let uu___2 = FStar_TypeChecker_Env.current_module env in
          FStar_Ident.string_of_lid uu___2 in
        FStar_Pervasives_Native.Some uu___1 in
      FStar_Profiling.profile (fun uu___1 -> sn' env t) uu___
        "FStar.TypeChecker.Rel.sn"
let (norm_with_steps :
  Prims.string ->
    FStar_TypeChecker_Env.steps ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun profiling_tag ->
    fun steps ->
      fun env ->
        fun t ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_TypeChecker_Env.current_module env in
              FStar_Ident.string_of_lid uu___2 in
            FStar_Pervasives_Native.Some uu___1 in
          FStar_Profiling.profile
            (fun uu___1 -> FStar_TypeChecker_Normalize.normalize steps env t)
            uu___ profiling_tag
let (should_strongly_reduce : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu___ =
      let uu___1 =
        FStar_Compiler_Effect.op_Bar_Greater t FStar_Syntax_Util.unascribe in
      FStar_Compiler_Effect.op_Bar_Greater uu___1
        FStar_Syntax_Util.head_and_args in
    match uu___ with
    | (h, uu___1) ->
        let uu___2 =
          let uu___3 = FStar_Syntax_Subst.compress h in
          uu___3.FStar_Syntax_Syntax.n in
        (match uu___2 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify) -> true
         | uu___3 -> false)
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun t ->
      let norm steps t1 =
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStar_Compiler_Effect.op_Bar_Greater t1
                FStar_Syntax_Util.unmeta in
            FStar_Compiler_Effect.op_Bar_Greater uu___2
              (FStar_TypeChecker_Normalize.normalize steps env) in
          FStar_Compiler_Effect.op_Bar_Greater uu___1
            FStar_Syntax_Subst.compress in
        FStar_Compiler_Effect.op_Bar_Greater uu___
          FStar_Syntax_Util.unlazy_emb in
      let uu___ =
        let uu___1 =
          let uu___2 = FStar_TypeChecker_Env.current_module env in
          FStar_Ident.string_of_lid uu___2 in
        FStar_Pervasives_Native.Some uu___1 in
      FStar_Profiling.profile
        (fun uu___1 ->
           let uu___2 = should_strongly_reduce t in
           if uu___2
           then
             norm
               [FStar_TypeChecker_Env.Beta;
               FStar_TypeChecker_Env.Reify;
               FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
               FStar_TypeChecker_Env.UnfoldUntil
                 FStar_Syntax_Syntax.delta_constant] t
           else
             (let uu___4 = FStar_Syntax_Util.unmeta t in
              norm
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Reify;
                FStar_TypeChecker_Env.Weak;
                FStar_TypeChecker_Env.HNF] uu___4)) uu___
        "FStar.TypeChecker.Rel.whnf"
let norm_arg :
  'uuuuu .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'uuuuu) ->
        (FStar_Syntax_Syntax.term * 'uuuuu)
  =
  fun env ->
    fun t ->
      let uu___ = sn env (FStar_Pervasives_Native.fst t) in
      (uu___, (FStar_Pervasives_Native.snd t))
let (sn_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binder Prims.list)
  =
  fun env ->
    fun binders ->
      FStar_Compiler_Effect.op_Bar_Greater binders
        (FStar_Compiler_List.map
           (fun b ->
              let uu___ =
                let uu___1 = b.FStar_Syntax_Syntax.binder_bv in
                let uu___2 =
                  sn env
                    (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                {
                  FStar_Syntax_Syntax.ppname =
                    (uu___1.FStar_Syntax_Syntax.ppname);
                  FStar_Syntax_Syntax.index =
                    (uu___1.FStar_Syntax_Syntax.index);
                  FStar_Syntax_Syntax.sort = uu___2
                } in
              {
                FStar_Syntax_Syntax.binder_bv = uu___;
                FStar_Syntax_Syntax.binder_qual =
                  (b.FStar_Syntax_Syntax.binder_qual);
                FStar_Syntax_Syntax.binder_attrs =
                  (b.FStar_Syntax_Syntax.binder_attrs)
              }))
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl ->
    fun u ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu___ = aux u3 in FStar_Syntax_Syntax.U_succ uu___
        | FStar_Syntax_Syntax.U_max us ->
            let uu___ = FStar_Compiler_List.map aux us in
            FStar_Syntax_Syntax.U_max uu___
        | uu___ -> u2 in
      let uu___ = aux u in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu___
let (normalize_refinement :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun steps ->
    fun env ->
      fun t0 ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStar_TypeChecker_Env.current_module env in
            FStar_Ident.string_of_lid uu___2 in
          FStar_Pervasives_Native.Some uu___1 in
        FStar_Profiling.profile
          (fun uu___1 ->
             FStar_TypeChecker_Normalize.normalize_refinement steps env t0)
          uu___ "FStar.TypeChecker.Rel.normalize_refinement"
let (base_and_refinement_maybe_delta :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.bv *
          FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option))
  =
  fun should_delta ->
    fun env ->
      fun t1 ->
        let norm_refinement env1 t =
          let steps =
            if should_delta
            then
              [FStar_TypeChecker_Env.Weak;
              FStar_TypeChecker_Env.HNF;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant]
            else [FStar_TypeChecker_Env.Weak; FStar_TypeChecker_Env.HNF] in
          normalize_refinement steps env1 t in
        let rec aux norm t11 =
          let t12 = FStar_Syntax_Util.unmeta t11 in
          match t12.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x, phi) ->
              if norm
              then
                ((x.FStar_Syntax_Syntax.sort),
                  (FStar_Pervasives_Native.Some (x, phi)))
              else
                (let uu___1 = norm_refinement env t12 in
                 match uu___1 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1, phi1);
                     FStar_Syntax_Syntax.pos = uu___2;
                     FStar_Syntax_Syntax.vars = uu___3;
                     FStar_Syntax_Syntax.hash_code = uu___4;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu___2 =
                       let uu___3 = FStar_Syntax_Print.term_to_string tt in
                       let uu___4 = FStar_Syntax_Print.tag_of_term tt in
                       FStar_Compiler_Util.format2
                         "impossible: Got %s ... %s\n" uu___3 uu___4 in
                     failwith uu___2)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu___ = FStar_Syntax_Util.unfold_lazy i in aux norm uu___
          | FStar_Syntax_Syntax.Tm_uinst uu___ ->
              if norm
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12 in
                 let uu___2 =
                   let uu___3 = FStar_Syntax_Subst.compress t1' in
                   uu___3.FStar_Syntax_Syntax.n in
                 match uu___2 with
                 | FStar_Syntax_Syntax.Tm_refine uu___3 -> aux true t1'
                 | uu___3 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu___ ->
              if norm
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12 in
                 let uu___2 =
                   let uu___3 = FStar_Syntax_Subst.compress t1' in
                   uu___3.FStar_Syntax_Syntax.n in
                 match uu___2 with
                 | FStar_Syntax_Syntax.Tm_refine uu___3 -> aux true t1'
                 | uu___3 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu___ ->
              if norm
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12 in
                 let uu___2 =
                   let uu___3 = FStar_Syntax_Subst.compress t1' in
                   uu___3.FStar_Syntax_Syntax.n in
                 match uu___2 with
                 | FStar_Syntax_Syntax.Tm_refine uu___3 -> aux true t1'
                 | uu___3 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu___ ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu___ ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu___ ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu___ ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu___ ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu___ ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu___ ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu___ ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu___ ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu___ ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu___ ->
              let uu___1 =
                let uu___2 = FStar_Syntax_Print.term_to_string t12 in
                let uu___3 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Compiler_Util.format2
                  "impossible (outer): Got %s ... %s\n" uu___2 uu___3 in
              failwith uu___1
          | FStar_Syntax_Syntax.Tm_ascribed uu___ ->
              let uu___1 =
                let uu___2 = FStar_Syntax_Print.term_to_string t12 in
                let uu___3 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Compiler_Util.format2
                  "impossible (outer): Got %s ... %s\n" uu___2 uu___3 in
              failwith uu___1
          | FStar_Syntax_Syntax.Tm_delayed uu___ ->
              let uu___1 =
                let uu___2 = FStar_Syntax_Print.term_to_string t12 in
                let uu___3 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Compiler_Util.format2
                  "impossible (outer): Got %s ... %s\n" uu___2 uu___3 in
              failwith uu___1
          | FStar_Syntax_Syntax.Tm_unknown ->
              let uu___ =
                let uu___1 = FStar_Syntax_Print.term_to_string t12 in
                let uu___2 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Compiler_Util.format2
                  "impossible (outer): Got %s ... %s\n" uu___1 uu___2 in
              failwith uu___ in
        let uu___ = whnf env t1 in aux false uu___
let (base_and_refinement :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option))
  = fun env -> fun t -> base_and_refinement_maybe_delta false env t
let (unrefine :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun env ->
    fun t ->
      let uu___ = base_and_refinement env t in
      FStar_Compiler_Effect.op_Bar_Greater uu___ FStar_Pervasives_Native.fst
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t ->
    let uu___ = FStar_Syntax_Syntax.null_bv t in
    (uu___, FStar_Syntax_Util.t_true)
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta ->
    fun env ->
      fun t ->
        let uu___ = base_and_refinement_maybe_delta delta env t in
        match uu___ with
        | (t_base, refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x, phi) -> (x, phi))
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu___ ->
    match uu___ with
    | (t_base, refopt) ->
        let uu___1 =
          match refopt with
          | FStar_Pervasives_Native.Some (y, phi) -> (y, phi)
          | FStar_Pervasives_Native.None -> trivial_refinement t_base in
        (match uu___1 with
         | (y, phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               t_base.FStar_Syntax_Syntax.pos)
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl -> fun prob -> prob_to_string wl.tcenv prob
let (wl_to_string : worklist -> Prims.string) =
  fun wl ->
    let probs_to_string ps =
      let uu___ = FStar_Compiler_List.map (wl_prob_to_string wl) ps in
      FStar_Compiler_Effect.op_Bar_Greater uu___ (FStar_String.concat "\n\t") in
    let uu___ = probs_to_string wl.attempting in
    let uu___1 =
      let uu___2 =
        FStar_Compiler_List.map
          (fun uu___3 -> match uu___3 with | (uu___4, uu___5, uu___6, x) -> x)
          wl.wl_deferred in
      probs_to_string uu___2 in
    FStar_Compiler_Util.format2
      "{ attempting = [ %s ];\ndeferred = [ %s ] }\n" uu___ uu___1
type flex_t =
  | Flex of (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar *
  FStar_Syntax_Syntax.args) 
let (uu___is_Flex : flex_t -> Prims.bool) = fun projectee -> true
let (__proj__Flex__item___0 :
  flex_t ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar *
      FStar_Syntax_Syntax.args))
  = fun projectee -> match projectee with | Flex _0 -> _0
let (flex_reason : flex_t -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | Flex (uu___1, u, uu___2) -> u.FStar_Syntax_Syntax.ctx_uvar_reason
let (flex_uvar : flex_t -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___ -> match uu___ with | Flex (uu___1, u, uu___2) -> u
let (flex_uvar_has_meta_tac : FStar_Syntax_Syntax.ctx_uvar -> Prims.bool) =
  fun u ->
    match u.FStar_Syntax_Syntax.ctx_uvar_meta with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Ctx_uvar_meta_tac
        uu___) -> true
    | uu___ -> false
let (flex_t_to_string : flex_t -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | Flex (uu___1, c, args) ->
        let uu___2 = print_ctx_uvar c in
        let uu___3 = FStar_Syntax_Print.args_to_string args in
        FStar_Compiler_Util.format2 "%s [%s]" uu___2 uu___3
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu___ = FStar_Syntax_Util.head_and_args t in
    match uu___ with
    | (head, _args) ->
        let uu___1 =
          let uu___2 = FStar_Syntax_Subst.compress head in
          uu___2.FStar_Syntax_Syntax.n in
        (match uu___1 with
         | FStar_Syntax_Syntax.Tm_uvar uu___2 -> true
         | uu___2 -> false)
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t ->
    let uu___ = FStar_Syntax_Util.head_and_args t in
    match uu___ with
    | (head, _args) ->
        let uu___1 =
          let uu___2 = FStar_Syntax_Subst.compress head in
          uu___2.FStar_Syntax_Syntax.n in
        (match uu___1 with
         | FStar_Syntax_Syntax.Tm_uvar (u, uu___2) -> u
         | uu___2 -> failwith "Not a flex-uvar")
let (ensure_no_uvar_subst :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      worklist -> (FStar_Syntax_Syntax.term * worklist))
  =
  fun env ->
    fun t0 ->
      fun wl ->
        let bv_not_affected_by s x =
          let t_x = FStar_Syntax_Syntax.bv_to_name x in
          let t_x' = FStar_Syntax_Subst.subst' s t_x in
          let uu___ =
            let uu___1 = FStar_Syntax_Subst.compress t_x' in
            uu___1.FStar_Syntax_Syntax.n in
          match uu___ with
          | FStar_Syntax_Syntax.Tm_name y -> FStar_Syntax_Syntax.bv_eq x y
          | uu___1 -> false in
        let binding_not_affected_by s b =
          match b with
          | FStar_Syntax_Syntax.Binding_var x -> bv_not_affected_by s x
          | uu___ -> true in
        let uu___ = FStar_Syntax_Util.head_and_args t0 in
        match uu___ with
        | (head, args) ->
            let uu___1 =
              let uu___2 = FStar_Syntax_Subst.compress head in
              uu___2.FStar_Syntax_Syntax.n in
            (match uu___1 with
             | FStar_Syntax_Syntax.Tm_uvar (uv, ([], uu___2)) -> (t0, wl)
             | FStar_Syntax_Syntax.Tm_uvar (uv, uu___2) when
                 FStar_Compiler_List.isEmpty
                   uv.FStar_Syntax_Syntax.ctx_uvar_binders
                 -> (t0, wl)
             | FStar_Syntax_Syntax.Tm_uvar (uv, s) ->
                 let uu___2 =
                   FStar_Common.max_suffix (binding_not_affected_by s)
                     uv.FStar_Syntax_Syntax.ctx_uvar_gamma in
                 (match uu___2 with
                  | (gamma_aff, new_gamma) ->
                      (match gamma_aff with
                       | [] -> (t0, wl)
                       | uu___3 ->
                           let dom_binders =
                             FStar_TypeChecker_Env.binders_of_bindings
                               gamma_aff in
                           let v_k =
                             let uu___4 = FStar_Syntax_Util.ctx_uvar_kind uv in
                             match uu___4 with
                             | FStar_Pervasives.Inl uu___5 ->
                                 FStar_Pervasives.Inl
                                   FStar_Pervasives_Native.None
                             | uu___5 ->
                                 failwith
                                   "Did not expect to create a new uvar for guard uvar" in
                           let uu___4 =
                             let uu___5 =
                               FStar_TypeChecker_Env.binders_of_bindings
                                 new_gamma in
                             let uu___6 =
                               let uu___7 =
                                 let uu___8 =
                                   FStar_Syntax_Util.ctx_uvar_typ uv in
                                 FStar_Syntax_Syntax.mk_Total uu___8 in
                               FStar_Syntax_Util.arrow dom_binders uu___7 in
                             let uu___7 =
                               FStar_Syntax_Util.ctx_uvar_should_check uv in
                             new_uvar
                               (Prims.op_Hat
                                  uv.FStar_Syntax_Syntax.ctx_uvar_reason
                                  "; force delayed") wl
                               t0.FStar_Syntax_Syntax.pos new_gamma uu___5
                               uu___6 uu___7 v_k
                               uv.FStar_Syntax_Syntax.ctx_uvar_meta in
                           (match uu___4 with
                            | (v, t_v, wl1) ->
                                let args_sol =
                                  FStar_Compiler_List.map
                                    FStar_Syntax_Util.arg_of_non_null_binder
                                    dom_binders in
                                let sol =
                                  FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                                    t0.FStar_Syntax_Syntax.pos in
                                ((let uu___6 =
                                    FStar_Compiler_Effect.op_Less_Bar
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu___6
                                  then
                                    let uu___7 =
                                      FStar_Syntax_Print.ctx_uvar_to_string
                                        uv in
                                    let uu___8 =
                                      FStar_Syntax_Print.term_to_string sol in
                                    FStar_Compiler_Util.print2
                                      "ensure_no_uvar_subst solving %s with %s\n"
                                      uu___7 uu___8
                                  else ());
                                 set_uvar env uv sol;
                                 mark_uvar_as_allow_untyped uv
                                   "sol is a new uvar that will be checked";
                                 (let args_sol_s =
                                    FStar_Compiler_List.map
                                      (fun uu___8 ->
                                         match uu___8 with
                                         | (a, i) ->
                                             let uu___9 =
                                               FStar_Syntax_Subst.subst' s a in
                                             (uu___9, i)) args_sol in
                                  let t =
                                    FStar_Syntax_Syntax.mk_Tm_app t_v
                                      (FStar_Compiler_List.op_At args_sol_s
                                         args) t0.FStar_Syntax_Syntax.pos in
                                  (t, wl1))))))
             | uu___2 ->
                 let uu___3 =
                   let uu___4 = FStar_Syntax_Print.tag_of_term t0 in
                   let uu___5 = FStar_Syntax_Print.tag_of_term head in
                   let uu___6 =
                     let uu___7 = FStar_Syntax_Subst.compress head in
                     FStar_Syntax_Print.tag_of_term uu___7 in
                   FStar_Compiler_Util.format3
                     "ensure_no_uvar_subst: expected a uvar at the head (%s-%s-%s)"
                     uu___4 uu___5 uu___6 in
                 failwith uu___3)
let (no_free_uvars : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    (let uu___ = FStar_Syntax_Free.uvars t in
     FStar_Compiler_Util.set_is_empty uu___) &&
      (let uu___ = FStar_Syntax_Free.univs t in
       FStar_Compiler_Util.set_is_empty uu___)
let rec (may_relate_with_logical_guard :
  FStar_TypeChecker_Env.env ->
    Prims.bool -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env ->
    fun is_eq ->
      fun head ->
        let uu___ =
          let uu___1 = FStar_Syntax_Subst.compress head in
          uu___1.FStar_Syntax_Syntax.n in
        match uu___ with
        | FStar_Syntax_Syntax.Tm_name uu___1 -> true
        | FStar_Syntax_Syntax.Tm_match uu___1 -> true
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            let uu___1 = FStar_TypeChecker_Env.delta_depth_of_fv env fv in
            (match uu___1 with
             | FStar_Syntax_Syntax.Delta_equational_at_level uu___2 -> true
             | FStar_Syntax_Syntax.Delta_abstract uu___2 -> is_eq
             | uu___2 -> false)
        | FStar_Syntax_Syntax.Tm_ascribed (t, uu___1, uu___2) ->
            may_relate_with_logical_guard env is_eq t
        | FStar_Syntax_Syntax.Tm_uinst (t, uu___1) ->
            may_relate_with_logical_guard env is_eq t
        | FStar_Syntax_Syntax.Tm_meta (t, uu___1) ->
            may_relate_with_logical_guard env is_eq t
        | uu___1 -> false
let (may_relate :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.rel -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env ->
    fun prel ->
      fun head ->
        may_relate_with_logical_guard env
          (FStar_TypeChecker_Common.uu___is_EQ prel) head
let (destruct_flex_t' : FStar_Syntax_Syntax.term -> flex_t) =
  fun t ->
    let uu___ = FStar_Syntax_Util.head_and_args t in
    match uu___ with
    | (head, args) ->
        let uu___1 =
          let uu___2 = FStar_Syntax_Subst.compress head in
          uu___2.FStar_Syntax_Syntax.n in
        (match uu___1 with
         | FStar_Syntax_Syntax.Tm_uvar (uv, s) -> Flex (t, uv, args)
         | uu___2 -> failwith "Not a flex-uvar")
let (destruct_flex_t :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> worklist -> (flex_t * worklist))
  =
  fun env ->
    fun t ->
      fun wl ->
        let uu___ = ensure_no_uvar_subst env t wl in
        match uu___ with
        | (t1, wl1) -> let uu___1 = destruct_flex_t' t1 in (uu___1, wl1)
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k ->
    fun ys ->
      fun t ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStar_Syntax_Subst.compress k in
            uu___2.FStar_Syntax_Syntax.n in
          match uu___1 with
          | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
              if
                (FStar_Compiler_List.length bs) =
                  (FStar_Compiler_List.length ys)
              then
                let uu___2 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu___2)
              else
                (let uu___3 = FStar_Syntax_Util.abs_formals t in
                 match uu___3 with
                 | (ys', t1, uu___4) ->
                     let uu___5 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_Compiler_List.op_At ys ys'), t1), uu___5))
          | uu___2 ->
              let uu___3 =
                let uu___4 = FStar_Syntax_Syntax.mk_Total k in ([], uu___4) in
              ((ys, t), uu___3) in
        match uu___ with
        | ((ys1, t1), (xs, c)) ->
            if
              (FStar_Compiler_List.length xs) <>
                (FStar_Compiler_List.length ys1)
            then
              FStar_Syntax_Util.abs ys1 t1
                (FStar_Pervasives_Native.Some
                   (FStar_Syntax_Util.mk_residual_comp
                      FStar_Parser_Const.effect_Tot_lid
                      FStar_Pervasives_Native.None []))
            else
              (let c1 =
                 let uu___2 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu___2 c in
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
  fun resolve_ok ->
    fun prob ->
      fun logical_guard ->
        fun uvis ->
          fun wl ->
            def_check_prob "solve_prob'" prob;
            (let phi =
               match logical_guard with
               | FStar_Pervasives_Native.None -> FStar_Syntax_Util.t_true
               | FStar_Pervasives_Native.Some phi1 -> phi1 in
             let assign_solution xs uv phi1 =
               (let uu___2 =
                  FStar_Compiler_Effect.op_Less_Bar
                    (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel") in
                if uu___2
                then
                  let uu___3 = FStar_Compiler_Util.string_of_int (p_pid prob) in
                  let uu___4 = print_ctx_uvar uv in
                  let uu___5 = FStar_Syntax_Print.term_to_string phi1 in
                  FStar_Compiler_Util.print3
                    "Solving %s (%s) with formula %s\n" uu___3 uu___4 uu___5
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0)) in
                (let uu___3 =
                   let uu___4 =
                     FStar_Compiler_Util.string_of_int (p_pid prob) in
                   Prims.op_Hat "solve_prob'.sol." uu___4 in
                 let uu___4 =
                   let uu___5 = p_scope prob in
                   FStar_Compiler_Effect.op_Less_Bar
                     (FStar_Compiler_List.map
                        (fun b -> b.FStar_Syntax_Syntax.binder_bv)) uu___5 in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu___3 uu___4 phi2);
                set_uvar wl.tcenv uv phi2) in
             let uv = p_guard_uvar prob in
             let fail uu___1 =
               let uu___2 =
                 let uu___3 = FStar_Syntax_Print.ctx_uvar_to_string uv in
                 let uu___4 =
                   FStar_Syntax_Print.term_to_string (p_guard prob) in
                 FStar_Compiler_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu___3 uu___4 in
               failwith uu___2 in
             let args_as_binders args =
               FStar_Compiler_Effect.op_Bar_Greater args
                 (FStar_Compiler_List.collect
                    (fun uu___1 ->
                       match uu___1 with
                       | (a, i) ->
                           let uu___2 =
                             let uu___3 = FStar_Syntax_Subst.compress a in
                             uu___3.FStar_Syntax_Syntax.n in
                           (match uu___2 with
                            | FStar_Syntax_Syntax.Tm_name x ->
                                let uu___3 =
                                  FStar_Syntax_Util.bqual_and_attrs_of_aqual
                                    i in
                                (match uu___3 with
                                 | (q, attrs) ->
                                     let uu___4 =
                                       FStar_Syntax_Syntax.mk_binder_with_attrs
                                         x q attrs in
                                     [uu___4])
                            | uu___3 -> (fail (); [])))) in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob) in
               let uu___1 =
                 let uu___2 = is_flex g in Prims.op_Negation uu___2 in
               if uu___1
               then (if resolve_ok then wl else (fail (); wl))
               else
                 (let uu___3 = destruct_flex_t wl.tcenv g wl in
                  match uu___3 with
                  | (Flex (uu___4, uv1, args), wl2) ->
                      ((let uu___6 = args_as_binders args in
                        assign_solution uu___6 uv1 phi);
                       wl2)) in
             commit wl1.tcenv uvis;
             {
               attempting = (wl1.attempting);
               wl_deferred = (wl1.wl_deferred);
               wl_deferred_to_tac = (wl1.wl_deferred_to_tac);
               ctr = (wl1.ctr + Prims.int_one);
               defer_ok = (wl1.defer_ok);
               smt_ok = (wl1.smt_ok);
               umax_heuristic_ok = (wl1.umax_heuristic_ok);
               tcenv = (wl1.tcenv);
               wl_implicits = (wl1.wl_implicits);
               repr_subcomp_allowed = (wl1.repr_subcomp_allowed)
             })
let (extend_universe_solution :
  Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid ->
    fun sol ->
      fun wl ->
        (let uu___1 =
           FStar_Compiler_Effect.op_Less_Bar
             (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel") in
         if uu___1
         then
           let uu___2 = FStar_Compiler_Util.string_of_int pid in
           let uu___3 = uvis_to_string wl.tcenv sol in
           FStar_Compiler_Util.print2 "Solving %s: with [%s]\n" uu___2 uu___3
         else ());
        commit wl.tcenv sol;
        {
          attempting = (wl.attempting);
          wl_deferred = (wl.wl_deferred);
          wl_deferred_to_tac = (wl.wl_deferred_to_tac);
          ctr = (wl.ctr + Prims.int_one);
          defer_ok = (wl.defer_ok);
          smt_ok = (wl.smt_ok);
          umax_heuristic_ok = (wl.umax_heuristic_ok);
          tcenv = (wl.tcenv);
          wl_implicits = (wl.wl_implicits);
          repr_subcomp_allowed = (wl.repr_subcomp_allowed)
        }
let (solve_prob :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      uvi Prims.list -> worklist -> worklist)
  =
  fun prob ->
    fun logical_guard ->
      fun uvis ->
        fun wl ->
          def_check_prob "solve_prob.prob" prob;
          FStar_Compiler_Util.iter_opt logical_guard
            (def_check_scoped "solve_prob.guard" prob);
          (let uu___3 =
             FStar_Compiler_Effect.op_Less_Bar
               (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "Rel") in
           if uu___3
           then
             let uu___4 =
               FStar_Compiler_Effect.op_Less_Bar
                 FStar_Compiler_Util.string_of_int (p_pid prob) in
             let uu___5 = uvis_to_string wl.tcenv uvis in
             FStar_Compiler_Util.print2 "Solving %s: with %s\n" uu___4 uu___5
           else ());
          solve_prob' false prob logical_guard uvis wl
let (occurs :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.ctx_uvar Prims.list * Prims.bool))
  =
  fun uk ->
    fun t ->
      let uvars =
        let uu___ = FStar_Syntax_Free.uvars t in
        FStar_Compiler_Effect.op_Bar_Greater uu___
          FStar_Compiler_Util.set_elements in
      let occurs1 =
        FStar_Compiler_Effect.op_Bar_Greater uvars
          (FStar_Compiler_Util.for_some
             (fun uv ->
                FStar_Syntax_Unionfind.equiv
                  uv.FStar_Syntax_Syntax.ctx_uvar_head
                  uk.FStar_Syntax_Syntax.ctx_uvar_head)) in
      (uvars, occurs1)
let (occurs_check :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.ctx_uvar Prims.list * Prims.bool * Prims.string
        FStar_Pervasives_Native.option))
  =
  fun uk ->
    fun t ->
      let uu___ = occurs uk t in
      match uu___ with
      | (uvars, occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu___2 =
                 let uu___3 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head in
                 let uu___4 = FStar_Syntax_Print.term_to_string t in
                 FStar_Compiler_Util.format2
                   "occurs-check failed (%s occurs in %s)" uu___3 uu___4 in
               FStar_Pervasives_Native.Some uu___2) in
          (uvars, (Prims.op_Negation occurs1), msg)
let (occurs_full :
  FStar_Syntax_Syntax.ctx_uvar -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun uk ->
    fun t ->
      let uvars =
        let uu___ = FStar_Syntax_Free.uvars_full t in
        FStar_Compiler_Effect.op_Bar_Greater uu___
          FStar_Compiler_Util.set_elements in
      let occurs1 =
        FStar_Compiler_Effect.op_Bar_Greater uvars
          (FStar_Compiler_Util.for_some
             (fun uv ->
                FStar_Syntax_Unionfind.equiv
                  uv.FStar_Syntax_Syntax.ctx_uvar_head
                  uk.FStar_Syntax_Syntax.ctx_uvar_head)) in
      occurs1
let rec (maximal_prefix :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * (FStar_Syntax_Syntax.binders *
        FStar_Syntax_Syntax.binders)))
  =
  fun bs ->
    fun bs' ->
      match (bs, bs') with
      | (binder1::bs_tail,
         { FStar_Syntax_Syntax.binder_bv = b';
           FStar_Syntax_Syntax.binder_qual = i';
           FStar_Syntax_Syntax.binder_attrs = uu___;_}::bs'_tail)
          ->
          let uu___1 =
            FStar_Syntax_Syntax.bv_eq binder1.FStar_Syntax_Syntax.binder_bv
              b' in
          if uu___1
          then
            let uu___2 = maximal_prefix bs_tail bs'_tail in
            (match uu___2 with | (pfx, rest) -> ((binder1 :: pfx), rest))
          else ([], (bs, bs'))
      | uu___ -> ([], (bs, bs'))
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g ->
    fun bs ->
      FStar_Compiler_List.fold_left
        (fun g1 ->
           fun uu___ ->
             match uu___ with
             | { FStar_Syntax_Syntax.binder_bv = x;
                 FStar_Syntax_Syntax.binder_qual = uu___1;
                 FStar_Syntax_Syntax.binder_attrs = uu___2;_} ->
                 (FStar_Syntax_Syntax.Binding_var x) :: g1) g bs
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g ->
    fun bs ->
      let uu___ = FStar_Compiler_List.last_opt bs in
      match uu___ with
      | FStar_Pervasives_Native.None -> []
      | FStar_Pervasives_Native.Some
          { FStar_Syntax_Syntax.binder_bv = x;
            FStar_Syntax_Syntax.binder_qual = uu___1;
            FStar_Syntax_Syntax.binder_attrs = uu___2;_}
          ->
          let uu___3 =
            FStar_Compiler_Util.prefix_until
              (fun uu___4 ->
                 match uu___4 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu___5 -> false) g in
          (match uu___3 with
           | FStar_Pervasives_Native.None -> []
           | FStar_Pervasives_Native.Some (uu___4, bx, rest) -> bx :: rest)
let (restrict_ctx :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.ctx_uvar ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun env ->
    fun tgt ->
      fun bs ->
        fun src ->
          fun wl ->
            let uu___ =
              maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
                src.FStar_Syntax_Syntax.ctx_uvar_binders in
            match uu___ with
            | (pfx, uu___1) ->
                let g =
                  gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx in
                let aux t f =
                  let uu___2 =
                    let uu___3 = FStar_Syntax_Util.ctx_uvar_kind src in
                    FStar_Pervasives.uu___is_Inl uu___3 in
                  if uu___2
                  then
                    let uu___3 =
                      let uu___4 =
                        let uu___5 =
                          FStar_Syntax_Print.uvar_to_string
                            src.FStar_Syntax_Syntax.ctx_uvar_head in
                        Prims.op_Hat "restricted " uu___5 in
                      let uu___5 =
                        FStar_Syntax_Util.ctx_uvar_should_check src in
                      new_uvar uu___4 wl
                        src.FStar_Syntax_Syntax.ctx_uvar_range g pfx t uu___5
                        (FStar_Pervasives.Inl FStar_Pervasives_Native.None)
                        src.FStar_Syntax_Syntax.ctx_uvar_meta in
                    match uu___3 with
                    | (uu___4, src', wl1) ->
                        ((let uu___6 = f src' in set_uvar env src uu___6);
                         mark_uvar_as_allow_untyped src
                           "assigned solution will be checked";
                         wl1)
                  else wl in
                let bs1 =
                  FStar_Compiler_Effect.op_Bar_Greater bs
                    (FStar_Compiler_List.filter
                       (fun uu___2 ->
                          match uu___2 with
                          | { FStar_Syntax_Syntax.binder_bv = bv1;
                              FStar_Syntax_Syntax.binder_qual = uu___3;
                              FStar_Syntax_Syntax.binder_attrs = uu___4;_} ->
                              (FStar_Compiler_Effect.op_Bar_Greater
                                 src.FStar_Syntax_Syntax.ctx_uvar_binders
                                 (FStar_Compiler_List.existsb
                                    (fun uu___5 ->
                                       match uu___5 with
                                       | {
                                           FStar_Syntax_Syntax.binder_bv =
                                             bv2;
                                           FStar_Syntax_Syntax.binder_qual =
                                             uu___6;
                                           FStar_Syntax_Syntax.binder_attrs =
                                             uu___7;_}
                                           ->
                                           FStar_Syntax_Syntax.bv_eq bv1 bv2)))
                                &&
                                (let uu___5 =
                                   FStar_Compiler_Effect.op_Bar_Greater pfx
                                     (FStar_Compiler_List.existsb
                                        (fun uu___6 ->
                                           match uu___6 with
                                           | {
                                               FStar_Syntax_Syntax.binder_bv
                                                 = bv2;
                                               FStar_Syntax_Syntax.binder_qual
                                                 = uu___7;
                                               FStar_Syntax_Syntax.binder_attrs
                                                 = uu___8;_}
                                               ->
                                               FStar_Syntax_Syntax.bv_eq bv1
                                                 bv2)) in
                                 Prims.op_Negation uu___5))) in
                if (FStar_Compiler_List.length bs1) = Prims.int_zero
                then
                  let uu___2 = FStar_Syntax_Util.ctx_uvar_typ src in
                  aux uu___2 (fun src' -> src')
                else
                  (let uu___3 =
                     let t = FStar_Syntax_Util.ctx_uvar_typ src in
                     let uu___4 =
                       let uu___5 =
                         let uu___6 =
                           FStar_Compiler_Effect.op_Bar_Greater t
                             (env.FStar_TypeChecker_Env.universe_of env) in
                         FStar_Compiler_Effect.op_Bar_Greater uu___6
                           (fun uu___7 -> FStar_Pervasives_Native.Some uu___7) in
                       FStar_Compiler_Effect.op_Bar_Greater uu___5
                         (FStar_Syntax_Syntax.mk_Total' t) in
                     FStar_Compiler_Effect.op_Bar_Greater uu___4
                       (FStar_Syntax_Util.arrow bs1) in
                   aux uu___3
                     (fun src' ->
                        let uu___4 =
                          let uu___5 =
                            FStar_Compiler_Effect.op_Bar_Greater bs1
                              FStar_Syntax_Syntax.binders_to_names in
                          FStar_Compiler_Effect.op_Bar_Greater uu___5
                            (FStar_Compiler_List.map
                               FStar_Syntax_Syntax.as_arg) in
                        FStar_Syntax_Syntax.mk_Tm_app src' uu___4
                          src.FStar_Syntax_Syntax.ctx_uvar_range))
let (restrict_all_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.ctx_uvar ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.ctx_uvar Prims.list -> worklist -> worklist)
  =
  fun env ->
    fun tgt ->
      fun bs ->
        fun sources ->
          fun wl ->
            match bs with
            | [] ->
                let ctx_tgt =
                  binders_as_bv_set tgt.FStar_Syntax_Syntax.ctx_uvar_binders in
                FStar_Compiler_List.fold_right
                  (fun src ->
                     fun wl1 ->
                       let ctx_src =
                         binders_as_bv_set
                           src.FStar_Syntax_Syntax.ctx_uvar_binders in
                       let uu___ =
                         FStar_Compiler_Util.set_is_subset_of ctx_src ctx_tgt in
                       if uu___ then wl1 else restrict_ctx env tgt [] src wl1)
                  sources wl
            | uu___ ->
                FStar_Compiler_List.fold_right (restrict_ctx env tgt bs)
                  sources wl
let (intersect_binders :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun g ->
    fun v1 ->
      fun v2 ->
        let as_set v =
          FStar_Compiler_Effect.op_Bar_Greater v
            (FStar_Compiler_List.fold_left
               (fun out ->
                  fun x ->
                    FStar_Compiler_Util.set_add
                      x.FStar_Syntax_Syntax.binder_bv out)
               FStar_Syntax_Syntax.no_names) in
        let v1_set = as_set v1 in
        let ctx_binders =
          FStar_Compiler_List.fold_left
            (fun out ->
               fun b ->
                 match b with
                 | FStar_Syntax_Syntax.Binding_var x ->
                     FStar_Compiler_Util.set_add x out
                 | uu___ -> out) FStar_Syntax_Syntax.no_names g in
        let uu___ =
          FStar_Compiler_Effect.op_Bar_Greater v2
            (FStar_Compiler_List.fold_left
               (fun uu___1 ->
                  fun b ->
                    match uu___1 with
                    | (isect, isect_set) ->
                        let uu___2 =
                          ((b.FStar_Syntax_Syntax.binder_bv),
                            (b.FStar_Syntax_Syntax.binder_qual)) in
                        (match uu___2 with
                         | (x, imp) ->
                             let uu___3 =
                               let uu___4 =
                                 FStar_Compiler_Util.set_mem x v1_set in
                               FStar_Compiler_Effect.op_Less_Bar
                                 Prims.op_Negation uu___4 in
                             if uu___3
                             then (isect, isect_set)
                             else
                               (let fvs =
                                  FStar_Syntax_Free.names
                                    x.FStar_Syntax_Syntax.sort in
                                let uu___5 =
                                  FStar_Compiler_Util.set_is_subset_of fvs
                                    isect_set in
                                if uu___5
                                then
                                  let uu___6 =
                                    FStar_Compiler_Util.set_add x isect_set in
                                  ((b :: isect), uu___6)
                                else (isect, isect_set)))) ([], ctx_binders)) in
        match uu___ with | (isect, uu___1) -> FStar_Compiler_List.rev isect
let (binders_eq :
  FStar_Syntax_Syntax.binder Prims.list ->
    FStar_Syntax_Syntax.binder Prims.list -> Prims.bool)
  =
  fun v1 ->
    fun v2 ->
      ((FStar_Compiler_List.length v1) = (FStar_Compiler_List.length v2)) &&
        (FStar_Compiler_List.forall2
           (fun uu___ ->
              fun uu___1 ->
                match (uu___, uu___1) with
                | ({ FStar_Syntax_Syntax.binder_bv = a;
                     FStar_Syntax_Syntax.binder_qual = uu___2;
                     FStar_Syntax_Syntax.binder_attrs = uu___3;_},
                   { FStar_Syntax_Syntax.binder_bv = b;
                     FStar_Syntax_Syntax.binder_qual = uu___4;
                     FStar_Syntax_Syntax.binder_attrs = uu___5;_})
                    -> FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let (name_exists_in_binders :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.binder Prims.list -> Prims.bool)
  =
  fun x ->
    fun bs ->
      FStar_Compiler_Util.for_some
        (fun uu___ ->
           match uu___ with
           | { FStar_Syntax_Syntax.binder_bv = y;
               FStar_Syntax_Syntax.binder_qual = uu___1;
               FStar_Syntax_Syntax.binder_attrs = uu___2;_} ->
               FStar_Syntax_Syntax.bv_eq x y) bs
let (pat_vars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binder Prims.list ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual) Prims.list ->
        FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option)
  =
  fun env ->
    fun ctx ->
      fun args ->
        let rec aux seen args1 =
          match args1 with
          | [] -> FStar_Pervasives_Native.Some (FStar_Compiler_List.rev seen)
          | (arg, i)::args2 ->
              let hd = sn env arg in
              (match hd.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_name a ->
                   let uu___ =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx) in
                   if uu___
                   then FStar_Pervasives_Native.None
                   else
                     (let uu___2 =
                        FStar_Syntax_Util.bqual_and_attrs_of_aqual i in
                      match uu___2 with
                      | (bq, attrs) ->
                          let uu___3 =
                            let uu___4 =
                              FStar_Syntax_Syntax.mk_binder_with_attrs a bq
                                attrs in
                            uu___4 :: seen in
                          aux uu___3 args2)
               | uu___ -> FStar_Pervasives_Native.None) in
        aux [] args
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | MisMatch (d1, d2) ->
        let uu___1 =
          let uu___2 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1 in
          let uu___3 =
            let uu___4 =
              let uu___5 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2 in
              Prims.op_Hat uu___5 ")" in
            Prims.op_Hat ") (" uu___4 in
          Prims.op_Hat uu___2 uu___3 in
        Prims.op_Hat "MisMatch (" uu___1
    | HeadMatch u ->
        let uu___1 = FStar_Compiler_Util.string_of_bool u in
        Prims.op_Hat "HeadMatch " uu___1
    | FullMatch -> "FullMatch"
let (head_match : match_result -> match_result) =
  fun uu___ ->
    match uu___ with
    | MisMatch (i, j) -> MisMatch (i, j)
    | HeadMatch (true) -> HeadMatch true
    | uu___1 -> HeadMatch false
let (fv_delta_depth :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth)
  =
  fun env ->
    fun fv ->
      let d = FStar_TypeChecker_Env.delta_depth_of_fv env fv in
      match d with
      | FStar_Syntax_Syntax.Delta_abstract d1 ->
          let uu___ =
            (let uu___1 =
               FStar_Ident.string_of_lid env.FStar_TypeChecker_Env.curmodule in
             let uu___2 =
               FStar_Ident.nsstr
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
             uu___1 = uu___2) &&
              (Prims.op_Negation env.FStar_TypeChecker_Env.is_iface) in
          if uu___ then d1 else FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Delta_constant_at_level i when i > Prims.int_zero
          ->
          let uu___ =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu___ with
           | FStar_Pervasives_Native.None ->
               FStar_Syntax_Syntax.delta_constant
           | uu___1 -> d)
      | d1 -> d1
let rec (delta_depth_of_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t ->
      let t1 = FStar_Syntax_Util.unmeta t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta uu___ ->
          failwith "Impossible (delta depth of term)"
      | FStar_Syntax_Syntax.Tm_delayed uu___ ->
          failwith "Impossible (delta depth of term)"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu___ = FStar_Syntax_Util.unfold_lazy i in
          delta_depth_of_term env uu___
      | FStar_Syntax_Syntax.Tm_unknown -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu___ -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu___ -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu___ -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu___ -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu___ -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2, uu___) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2, uu___, uu___1) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2, uu___) -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu___;
             FStar_Syntax_Syntax.index = uu___1;
             FStar_Syntax_Syntax.sort = t2;_},
           uu___2)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu___ ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu___ ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu___ ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu___ ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu___ ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu___ = fv_delta_depth env fv in
          FStar_Pervasives_Native.Some uu___
let (universe_has_max :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.universe -> Prims.bool) =
  fun env ->
    fun u ->
      let u1 = FStar_TypeChecker_Normalize.normalize_universe env u in
      match u1 with
      | FStar_Syntax_Syntax.U_max uu___ -> true
      | uu___ -> false
let rec (head_matches :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> match_result)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let t11 = FStar_Syntax_Util.unmeta t1 in
        let t21 = FStar_Syntax_Util.unmeta t2 in
        match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n)) with
        | (FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu___;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu___1;
             FStar_Syntax_Syntax.ltyp = uu___2;
             FStar_Syntax_Syntax.rng = uu___3;_},
           uu___4) ->
            let uu___5 = FStar_Syntax_Util.unlazy t11 in
            head_matches env uu___5 t21
        | (uu___, FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu___1;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu___2;
             FStar_Syntax_Syntax.ltyp = uu___3;
             FStar_Syntax_Syntax.rng = uu___4;_})
            ->
            let uu___5 = FStar_Syntax_Util.unlazy t21 in
            head_matches env t11 uu___5
        | (FStar_Syntax_Syntax.Tm_name x, FStar_Syntax_Syntax.Tm_name y) ->
            let uu___ = FStar_Syntax_Syntax.bv_eq x y in
            if uu___
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f, FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu___ = FStar_Syntax_Syntax.fv_eq f g in
            if uu___
            then FullMatch
            else
              (let uu___2 =
                 let uu___3 =
                   let uu___4 = fv_delta_depth env f in
                   FStar_Pervasives_Native.Some uu___4 in
                 let uu___4 =
                   let uu___5 = fv_delta_depth env g in
                   FStar_Pervasives_Native.Some uu___5 in
                 (uu___3, uu___4) in
               MisMatch uu___2)
        | (FStar_Syntax_Syntax.Tm_uinst (f, uu___),
           FStar_Syntax_Syntax.Tm_uinst (g, uu___1)) ->
            let uu___2 = head_matches env f g in
            FStar_Compiler_Effect.op_Bar_Greater uu___2 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify),
           FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify)) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), uu___)
            -> HeadMatch true
        | (uu___, FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify))
            -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c, FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu___ = FStar_Const.eq_const c d in
            if uu___
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar (uv, uu___),
           FStar_Syntax_Syntax.Tm_uvar (uv', uu___1)) ->
            let uu___2 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head in
            if uu___2
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine (x, uu___),
           FStar_Syntax_Syntax.Tm_refine (y, uu___1)) ->
            let uu___2 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_Compiler_Effect.op_Bar_Greater uu___2 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x, uu___), uu___1) ->
            let uu___2 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_Compiler_Effect.op_Bar_Greater uu___2 head_match
        | (uu___, FStar_Syntax_Syntax.Tm_refine (x, uu___1)) ->
            let uu___2 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_Compiler_Effect.op_Bar_Greater uu___2 head_match
        | (FStar_Syntax_Syntax.Tm_type uu___, FStar_Syntax_Syntax.Tm_type
           uu___1) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow uu___, FStar_Syntax_Syntax.Tm_arrow
           uu___1) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app (head, uu___),
           FStar_Syntax_Syntax.Tm_app (head', uu___1)) ->
            let uu___2 = head_matches env head head' in
            FStar_Compiler_Effect.op_Bar_Greater uu___2 head_match
        | (FStar_Syntax_Syntax.Tm_app (head, uu___), uu___1) ->
            let uu___2 = head_matches env head t21 in
            FStar_Compiler_Effect.op_Bar_Greater uu___2 head_match
        | (uu___, FStar_Syntax_Syntax.Tm_app (head, uu___1)) ->
            let uu___2 = head_matches env t11 head in
            FStar_Compiler_Effect.op_Bar_Greater uu___2 head_match
        | (FStar_Syntax_Syntax.Tm_let uu___, FStar_Syntax_Syntax.Tm_let
           uu___1) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match uu___, FStar_Syntax_Syntax.Tm_match
           uu___1) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu___, FStar_Syntax_Syntax.Tm_abs
           uu___1) -> HeadMatch true
        | uu___ ->
            let uu___1 =
              let uu___2 = delta_depth_of_term env t11 in
              let uu___3 = delta_depth_of_term env t21 in (uu___2, uu___3) in
            MisMatch uu___1
let (head_matches_delta :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          (match_result * (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ)
            FStar_Pervasives_Native.option))
  =
  fun env ->
    fun smt_ok ->
      fun t1 ->
        fun t2 ->
          let maybe_inline t =
            let head =
              let uu___ = unrefine env t in FStar_Syntax_Util.head_of uu___ in
            (let uu___1 =
               FStar_Compiler_Effect.op_Less_Bar
                 (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta") in
             if uu___1
             then
               let uu___2 = FStar_Syntax_Print.term_to_string t in
               let uu___3 = FStar_Syntax_Print.term_to_string head in
               FStar_Compiler_Util.print2 "Head of %s is %s\n" uu___2 uu___3
             else ());
            (let uu___1 =
               let uu___2 = FStar_Syntax_Util.un_uinst head in
               uu___2.FStar_Syntax_Syntax.n in
             match uu___1 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu___2 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                 (match uu___2 with
                  | FStar_Pervasives_Native.None ->
                      ((let uu___4 =
                          FStar_Compiler_Effect.op_Less_Bar
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta") in
                        if uu___4
                        then
                          let uu___5 = FStar_Syntax_Print.term_to_string head in
                          FStar_Compiler_Util.print1
                            "No definition found for %s\n" uu___5
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu___3 ->
                      let basic_steps =
                        [FStar_TypeChecker_Env.UnfoldUntil
                           FStar_Syntax_Syntax.delta_constant;
                        FStar_TypeChecker_Env.Weak;
                        FStar_TypeChecker_Env.HNF;
                        FStar_TypeChecker_Env.Primops;
                        FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.Eager_unfolding;
                        FStar_TypeChecker_Env.Iota] in
                      let steps =
                        if smt_ok
                        then basic_steps
                        else
                          (FStar_TypeChecker_Env.Exclude
                             FStar_TypeChecker_Env.Zeta)
                          :: basic_steps in
                      let t' =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.1" steps env
                          t in
                      let uu___4 =
                        let uu___5 = FStar_Syntax_Util.eq_tm t t' in
                        uu___5 = FStar_Syntax_Util.Equal in
                      if uu___4
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu___7 =
                            FStar_Compiler_Effect.op_Less_Bar
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta") in
                          if uu___7
                          then
                            let uu___8 = FStar_Syntax_Print.term_to_string t in
                            let uu___9 = FStar_Syntax_Print.term_to_string t' in
                            FStar_Compiler_Util.print2 "Inlined %s to %s\n"
                              uu___8 uu___9
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu___2 -> FStar_Pervasives_Native.None) in
          let success d r t11 t21 =
            (r,
              (if d > Prims.int_zero
               then FStar_Pervasives_Native.Some (t11, t21)
               else FStar_Pervasives_Native.None)) in
          let fail d r t11 t21 =
            (r,
              (if d > Prims.int_zero
               then FStar_Pervasives_Native.Some (t11, t21)
               else FStar_Pervasives_Native.None)) in
          let made_progress t t' =
            let uu___ =
              let uu___1 =
                let uu___2 = FStar_Syntax_Util.head_and_args t in
                FStar_Compiler_Effect.op_Bar_Greater uu___2
                  FStar_Pervasives_Native.fst in
              let uu___2 =
                let uu___3 = FStar_Syntax_Util.head_and_args t' in
                FStar_Compiler_Effect.op_Bar_Greater uu___3
                  FStar_Pervasives_Native.fst in
              (uu___1, uu___2) in
            match uu___ with
            | (head, head') ->
                let uu___1 =
                  let uu___2 = FStar_Syntax_Util.eq_tm head head' in
                  uu___2 = FStar_Syntax_Util.Equal in
                Prims.op_Negation uu___1 in
          let rec aux retry n_delta t11 t21 =
            let r = head_matches env t11 t21 in
            (let uu___1 =
               FStar_Compiler_Effect.op_Less_Bar
                 (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta") in
             if uu___1
             then
               let uu___2 = FStar_Syntax_Print.term_to_string t11 in
               let uu___3 = FStar_Syntax_Print.term_to_string t21 in
               let uu___4 = string_of_match_result r in
               FStar_Compiler_Util.print3 "head_matches (%s, %s) = %s\n"
                 uu___2 uu___3 uu___4
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2 in
               let uu___1 =
                 if d1_greater_than_d2
                 then
                   let t1' =
                     normalize_refinement
                       [FStar_TypeChecker_Env.UnfoldUntil d2;
                       FStar_TypeChecker_Env.Weak;
                       FStar_TypeChecker_Env.HNF] env t11 in
                   let uu___2 = made_progress t11 t1' in (t1', t21, uu___2)
                 else
                   (let t2' =
                      normalize_refinement
                        [FStar_TypeChecker_Env.UnfoldUntil d1;
                        FStar_TypeChecker_Env.Weak;
                        FStar_TypeChecker_Env.HNF] env t21 in
                    let uu___3 = made_progress t21 t2' in (t11, t2', uu___3)) in
               match uu___1 with
               | (t12, t22, made_progress1) ->
                   if made_progress1
                   then aux retry (n_delta + Prims.int_one) t12 t22
                   else fail n_delta r t12 t22 in
             let reduce_both_and_try_again d r1 =
               let uu___1 = FStar_TypeChecker_Common.decr_delta_depth d in
               match uu___1 with
               | FStar_Pervasives_Native.None -> fail n_delta r1 t11 t21
               | FStar_Pervasives_Native.Some d1 ->
                   let t1' =
                     normalize_refinement
                       [FStar_TypeChecker_Env.UnfoldUntil d1;
                       FStar_TypeChecker_Env.Weak;
                       FStar_TypeChecker_Env.HNF] env t11 in
                   let t2' =
                     normalize_refinement
                       [FStar_TypeChecker_Env.UnfoldUntil d1;
                       FStar_TypeChecker_Env.Weak;
                       FStar_TypeChecker_Env.HNF] env t21 in
                   let uu___2 =
                     (made_progress t11 t1') && (made_progress t21 t2') in
                   if uu___2
                   then aux retry (n_delta + Prims.int_one) t1' t2'
                   else fail n_delta r1 t11 t21 in
             match r with
             | MisMatch
                 (FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level i),
                  FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level j))
                 when
                 ((i > Prims.int_zero) || (j > Prims.int_zero)) && (i <> j)
                 ->
                 reduce_one_and_try_again
                   (FStar_Syntax_Syntax.Delta_equational_at_level i)
                   (FStar_Syntax_Syntax.Delta_equational_at_level j)
             | MisMatch
                 (FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu___1),
                  uu___2)
                 ->
                 if Prims.op_Negation retry
                 then fail n_delta r t11 t21
                 else
                   (let uu___4 =
                      let uu___5 = maybe_inline t11 in
                      let uu___6 = maybe_inline t21 in (uu___5, uu___6) in
                    match uu___4 with
                    | (FStar_Pervasives_Native.None,
                       FStar_Pervasives_Native.None) ->
                        fail n_delta r t11 t21
                    | (FStar_Pervasives_Native.Some t12,
                       FStar_Pervasives_Native.None) ->
                        aux false (n_delta + Prims.int_one) t12 t21
                    | (FStar_Pervasives_Native.None,
                       FStar_Pervasives_Native.Some t22) ->
                        aux false (n_delta + Prims.int_one) t11 t22
                    | (FStar_Pervasives_Native.Some t12,
                       FStar_Pervasives_Native.Some t22) ->
                        aux false (n_delta + Prims.int_one) t12 t22)
             | MisMatch
                 (uu___1, FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu___2))
                 ->
                 if Prims.op_Negation retry
                 then fail n_delta r t11 t21
                 else
                   (let uu___4 =
                      let uu___5 = maybe_inline t11 in
                      let uu___6 = maybe_inline t21 in (uu___5, uu___6) in
                    match uu___4 with
                    | (FStar_Pervasives_Native.None,
                       FStar_Pervasives_Native.None) ->
                        fail n_delta r t11 t21
                    | (FStar_Pervasives_Native.Some t12,
                       FStar_Pervasives_Native.None) ->
                        aux false (n_delta + Prims.int_one) t12 t21
                    | (FStar_Pervasives_Native.None,
                       FStar_Pervasives_Native.Some t22) ->
                        aux false (n_delta + Prims.int_one) t11 t22
                    | (FStar_Pervasives_Native.Some t12,
                       FStar_Pervasives_Native.Some t22) ->
                        aux false (n_delta + Prims.int_one) t12 t22)
             | MisMatch
                 (FStar_Pervasives_Native.Some d1,
                  FStar_Pervasives_Native.Some d2)
                 when d1 = d2 -> reduce_both_and_try_again d1 r
             | MisMatch
                 (FStar_Pervasives_Native.Some d1,
                  FStar_Pervasives_Native.Some d2)
                 -> reduce_one_and_try_again d1 d2
             | MisMatch uu___1 -> fail n_delta r t11 t21
             | uu___1 -> success n_delta r t11 t21) in
          let r = aux true Prims.int_zero t1 t2 in
          (let uu___1 =
             FStar_Compiler_Effect.op_Less_Bar
               (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta") in
           if uu___1
           then
             let uu___2 = FStar_Syntax_Print.term_to_string t1 in
             let uu___3 = FStar_Syntax_Print.term_to_string t2 in
             let uu___4 =
               string_of_match_result (FStar_Pervasives_Native.fst r) in
             let uu___5 =
               if
                 FStar_Compiler_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu___7 =
                    FStar_Compiler_Effect.op_Bar_Greater
                      (FStar_Pervasives_Native.snd r)
                      FStar_Compiler_Util.must in
                  FStar_Compiler_Effect.op_Bar_Greater uu___7
                    (fun uu___8 ->
                       match uu___8 with
                       | (t11, t21) ->
                           let uu___9 = FStar_Syntax_Print.term_to_string t11 in
                           let uu___10 =
                             let uu___11 =
                               FStar_Syntax_Print.term_to_string t21 in
                             Prims.op_Hat "; " uu___11 in
                           Prims.op_Hat uu___9 uu___10)) in
             FStar_Compiler_Util.print4
               "head_matches_delta (%s, %s) = %s (%s)\n" uu___2 uu___3 uu___4
               uu___5
           else ());
          r
let (kind_type :
  FStar_Syntax_Syntax.binders ->
    FStar_Compiler_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders ->
    fun r ->
      let uu___ = FStar_Syntax_Util.type_u () in
      FStar_Compiler_Effect.op_Bar_Greater uu___ FStar_Pervasives_Native.fst
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___ ->
    match uu___ with
    | FStar_TypeChecker_Common.Rigid_rigid -> Prims.int_zero
    | FStar_TypeChecker_Common.Flex_rigid_eq -> Prims.int_one
    | FStar_TypeChecker_Common.Flex_flex_pattern_eq -> (Prims.of_int (2))
    | FStar_TypeChecker_Common.Flex_rigid -> (Prims.of_int (3))
    | FStar_TypeChecker_Common.Rigid_flex -> (Prims.of_int (4))
    | FStar_TypeChecker_Common.Flex_flex -> (Prims.of_int (5))
let (rank_leq :
  FStar_TypeChecker_Common.rank_t ->
    FStar_TypeChecker_Common.rank_t -> Prims.bool)
  = fun r1 -> fun r2 -> (rank_t_num r1) <= (rank_t_num r2)
let (rank_less_than :
  FStar_TypeChecker_Common.rank_t ->
    FStar_TypeChecker_Common.rank_t -> Prims.bool)
  = fun r1 -> fun r2 -> (r1 <> r2) && ((rank_t_num r1) <= (rank_t_num r2))
let (compress_tprob :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_TypeChecker_Common.problem ->
      FStar_Syntax_Syntax.term FStar_TypeChecker_Common.problem)
  =
  fun tcenv ->
    fun p ->
      let uu___ = whnf tcenv p.FStar_TypeChecker_Common.lhs in
      let uu___1 = whnf tcenv p.FStar_TypeChecker_Common.rhs in
      {
        FStar_TypeChecker_Common.pid = (p.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu___;
        FStar_TypeChecker_Common.relation =
          (p.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu___1;
        FStar_TypeChecker_Common.element =
          (p.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (p.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (p.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason = (p.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc = (p.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank = (p.FStar_TypeChecker_Common.rank)
      }
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv ->
    fun p ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu___ = compress_tprob tcenv p1 in
          FStar_Compiler_Effect.op_Bar_Greater uu___
            (fun uu___1 -> FStar_TypeChecker_Common.TProb uu___1)
      | FStar_TypeChecker_Common.CProb uu___ -> p
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv ->
    fun pr ->
      let prob =
        let uu___ = compress_prob tcenv pr in
        FStar_Compiler_Effect.op_Bar_Greater uu___ maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu___ =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu___ with
           | (lh, lhs_args) ->
               let uu___1 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu___1 with
                | (rh, rhs_args) ->
                    let uu___2 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar uu___3,
                         FStar_Syntax_Syntax.Tm_uvar uu___4) ->
                          (match (lhs_args, rhs_args) with
                           | ([], []) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu___5 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu___3, uu___4) when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu___3, FStar_Syntax_Syntax.Tm_uvar uu___4) when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu___3,
                         FStar_Syntax_Syntax.Tm_arrow uu___4) ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            {
                              FStar_TypeChecker_Common.pid =
                                (tp.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (tp.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (tp.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (tp.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (tp.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (tp.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (tp.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (tp.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (tp.FStar_TypeChecker_Common.rank)
                            })
                      | (FStar_Syntax_Syntax.Tm_uvar uu___3,
                         FStar_Syntax_Syntax.Tm_type uu___4) ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            {
                              FStar_TypeChecker_Common.pid =
                                (tp.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (tp.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (tp.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (tp.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (tp.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (tp.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (tp.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (tp.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (tp.FStar_TypeChecker_Common.rank)
                            })
                      | (FStar_Syntax_Syntax.Tm_type uu___3,
                         FStar_Syntax_Syntax.Tm_uvar uu___4) ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            {
                              FStar_TypeChecker_Common.pid =
                                (tp.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (tp.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (tp.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (tp.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (tp.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (tp.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (tp.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (tp.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (tp.FStar_TypeChecker_Common.rank)
                            })
                      | (uu___3, FStar_Syntax_Syntax.Tm_uvar uu___4) ->
                          (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu___3, uu___4) ->
                          (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu___3, FStar_Syntax_Syntax.Tm_uvar uu___4) ->
                          (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu___3, uu___4) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp) in
                    (match uu___2 with
                     | (rank1, tp1) ->
                         let uu___3 =
                           FStar_Compiler_Effect.op_Bar_Greater
                             {
                               FStar_TypeChecker_Common.pid =
                                 (tp1.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (tp1.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 (tp1.FStar_TypeChecker_Common.relation);
                               FStar_TypeChecker_Common.rhs =
                                 (tp1.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (tp1.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (tp1.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (tp1.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (tp1.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (tp1.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (FStar_Pervasives_Native.Some rank1)
                             }
                             (fun uu___4 ->
                                FStar_TypeChecker_Common.TProb uu___4) in
                         (rank1, uu___3))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu___ =
            FStar_Compiler_Effect.op_Bar_Greater
              {
                FStar_TypeChecker_Common.pid =
                  (cp.FStar_TypeChecker_Common.pid);
                FStar_TypeChecker_Common.lhs =
                  (cp.FStar_TypeChecker_Common.lhs);
                FStar_TypeChecker_Common.relation =
                  (cp.FStar_TypeChecker_Common.relation);
                FStar_TypeChecker_Common.rhs =
                  (cp.FStar_TypeChecker_Common.rhs);
                FStar_TypeChecker_Common.element =
                  (cp.FStar_TypeChecker_Common.element);
                FStar_TypeChecker_Common.logical_guard =
                  (cp.FStar_TypeChecker_Common.logical_guard);
                FStar_TypeChecker_Common.logical_guard_uvar =
                  (cp.FStar_TypeChecker_Common.logical_guard_uvar);
                FStar_TypeChecker_Common.reason =
                  (cp.FStar_TypeChecker_Common.reason);
                FStar_TypeChecker_Common.loc =
                  (cp.FStar_TypeChecker_Common.loc);
                FStar_TypeChecker_Common.rank =
                  (FStar_Pervasives_Native.Some
                     FStar_TypeChecker_Common.Rigid_rigid)
              } (fun uu___1 -> FStar_TypeChecker_Common.CProb uu___1) in
          (FStar_TypeChecker_Common.Rigid_rigid, uu___)
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl ->
    let rec aux uu___ probs =
      match uu___ with
      | (min_rank, min, out) ->
          (match probs with
           | [] ->
               (match (min, min_rank) with
                | (FStar_Pervasives_Native.Some p,
                   FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu___1 -> FStar_Pervasives_Native.None)
           | hd::tl ->
               let uu___1 = rank wl.tcenv hd in
               (match uu___1 with
                | (rank1, hd1) ->
                    if rank_leq rank1 FStar_TypeChecker_Common.Flex_rigid_eq
                    then
                      (match min with
                       | FStar_Pervasives_Native.None ->
                           FStar_Pervasives_Native.Some
                             (hd1, (FStar_Compiler_List.op_At out tl), rank1)
                       | FStar_Pervasives_Native.Some m ->
                           FStar_Pervasives_Native.Some
                             (hd1, (FStar_Compiler_List.op_At out (m :: tl)),
                               rank1))
                    else
                      (let uu___3 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu___4 = FStar_Compiler_Option.get min_rank in
                            rank_less_than rank1 uu___4) in
                       if uu___3
                       then
                         match min with
                         | FStar_Pervasives_Native.None ->
                             aux
                               ((FStar_Pervasives_Native.Some rank1),
                                 (FStar_Pervasives_Native.Some hd1), out) tl
                         | FStar_Pervasives_Native.Some m ->
                             aux
                               ((FStar_Pervasives_Native.Some rank1),
                                 (FStar_Pervasives_Native.Some hd1), (m ::
                                 out)) tl
                       else aux (min_rank, min, (hd1 :: out)) tl))) in
    aux (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None, [])
      wl.attempting
let (flex_prob_closing :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Common.prob -> Prims.bool)
  =
  fun tcenv ->
    fun bs ->
      fun p ->
        let flex_will_be_closed t =
          let uu___ = FStar_Syntax_Util.head_and_args t in
          match uu___ with
          | (hd, uu___1) ->
              let uu___2 =
                let uu___3 = FStar_Syntax_Subst.compress hd in
                uu___3.FStar_Syntax_Syntax.n in
              (match uu___2 with
               | FStar_Syntax_Syntax.Tm_uvar (u, uu___3) ->
                   FStar_Compiler_Effect.op_Bar_Greater
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Compiler_Util.for_some
                        (fun uu___4 ->
                           match uu___4 with
                           | { FStar_Syntax_Syntax.binder_bv = y;
                               FStar_Syntax_Syntax.binder_qual = uu___5;
                               FStar_Syntax_Syntax.binder_attrs = uu___6;_}
                               ->
                               FStar_Compiler_Effect.op_Bar_Greater bs
                                 (FStar_Compiler_Util.for_some
                                    (fun uu___7 ->
                                       match uu___7 with
                                       | { FStar_Syntax_Syntax.binder_bv = x;
                                           FStar_Syntax_Syntax.binder_qual =
                                             uu___8;
                                           FStar_Syntax_Syntax.binder_attrs =
                                             uu___9;_}
                                           -> FStar_Syntax_Syntax.bv_eq x y))))
               | uu___3 -> false) in
        let uu___ = rank tcenv p in
        match uu___ with
        | (r, p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu___1 -> true
             | FStar_TypeChecker_Common.TProb p2 ->
                 (match r with
                  | FStar_TypeChecker_Common.Rigid_rigid -> true
                  | FStar_TypeChecker_Common.Flex_rigid_eq -> true
                  | FStar_TypeChecker_Common.Flex_flex_pattern_eq -> true
                  | FStar_TypeChecker_Common.Flex_rigid ->
                      flex_will_be_closed p2.FStar_TypeChecker_Common.lhs
                  | FStar_TypeChecker_Common.Rigid_flex ->
                      flex_will_be_closed p2.FStar_TypeChecker_Common.rhs
                  | FStar_TypeChecker_Common.Flex_flex ->
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
  fun projectee ->
    match projectee with | UDeferred _0 -> true | uu___ -> false
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee -> match projectee with | UDeferred _0 -> _0
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee -> match projectee with | USolved _0 -> true | uu___ -> false
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee -> match projectee with | USolved _0 -> _0
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee -> match projectee with | UFailed _0 -> true | uu___ -> false
let (__proj__UFailed__item___0 : univ_eq_sol -> lstring) =
  fun projectee -> match projectee with | UFailed _0 -> _0
let (ufailed_simple : Prims.string -> univ_eq_sol) =
  fun s -> let uu___ = FStar_Thunk.mkv s in UFailed uu___
let (ufailed_thunk : (unit -> Prims.string) -> univ_eq_sol) =
  fun s -> let uu___ = mklstr s in UFailed uu___
let rec (really_solve_universe_eq :
  Prims.int ->
    worklist ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> univ_eq_sol)
  =
  fun pid_orig ->
    fun wl ->
      fun u1 ->
        fun u2 ->
          let u11 =
            FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u1 in
          let u21 =
            FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u2 in
          let rec occurs_univ v1 u =
            match u with
            | FStar_Syntax_Syntax.U_max us ->
                FStar_Compiler_Effect.op_Bar_Greater us
                  (FStar_Compiler_Util.for_some
                     (fun u3 ->
                        let uu___ = FStar_Syntax_Util.univ_kernel u3 in
                        match uu___ with
                        | (k, uu___1) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu___2 -> false)))
            | uu___ -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_Compiler_Effect.op_Bar_Greater u12
                (FStar_Compiler_List.fold_left
                   (fun uvs ->
                      fun uv1 ->
                        let uu___ =
                          FStar_Compiler_Effect.op_Bar_Greater u22
                            (FStar_Compiler_List.existsML
                               (fun uv2 -> FStar_Syntax_Util.eq_univs uv1 uv2)) in
                        if uu___ then uv1 :: uvs else uvs) []) in
            let filter =
              FStar_Compiler_List.filter
                (fun u ->
                   let uu___ =
                     FStar_Compiler_Effect.op_Bar_Greater common_elts
                       (FStar_Compiler_List.existsML
                          (fun u' -> FStar_Syntax_Util.eq_univs u u')) in
                   Prims.op_Negation uu___) in
            let uu___ = filter u12 in
            let uu___1 = filter u22 in (uu___, uu___1) in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then ufailed_simple "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1, FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu___1 = filter_out_common_univs us1 us2 in
                   (match uu___1 with
                    | (us11, us21) ->
                        if
                          (FStar_Compiler_List.length us11) =
                            (FStar_Compiler_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13, u23::us23) ->
                                let uu___2 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23 in
                                (match uu___2 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu___2 -> USolved wl1 in
                          aux wl us11 us21
                        else
                          ufailed_thunk
                            (fun uu___3 ->
                               let uu___4 =
                                 FStar_Syntax_Print.univ_to_string u12 in
                               let uu___5 =
                                 FStar_Syntax_Print.univ_to_string u22 in
                               FStar_Compiler_Util.format2
                                 "Unable to unify universes: %s and %s"
                                 uu___4 uu___5))
               | (FStar_Syntax_Syntax.U_max us, u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu___1 =
                           really_solve_universe_eq pid_orig wl1 u u' in
                         (match uu___1 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed) in
                   aux wl us
               | (u', FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu___1 =
                           really_solve_universe_eq pid_orig wl1 u u' in
                         (match uu___1 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed) in
                   aux wl us
               | uu___1 ->
                   ufailed_thunk
                     (fun uu___2 ->
                        let uu___3 = FStar_Syntax_Print.univ_to_string u12 in
                        let uu___4 = FStar_Syntax_Print.univ_to_string u22 in
                        FStar_Compiler_Util.format3
                          "Unable to unify universes: %s and %s (%s)" uu___3
                          uu___4 msg)) in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu___, uu___1) ->
              let uu___2 =
                let uu___3 = FStar_Syntax_Print.univ_to_string u11 in
                let uu___4 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Compiler_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu___3 uu___4 in
              failwith uu___2
          | (FStar_Syntax_Syntax.U_unknown, uu___) ->
              let uu___1 =
                let uu___2 = FStar_Syntax_Print.univ_to_string u11 in
                let uu___3 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Compiler_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu___2 uu___3 in
              failwith uu___1
          | (uu___, FStar_Syntax_Syntax.U_bvar uu___1) ->
              let uu___2 =
                let uu___3 = FStar_Syntax_Print.univ_to_string u11 in
                let uu___4 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Compiler_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu___3 uu___4 in
              failwith uu___2
          | (uu___, FStar_Syntax_Syntax.U_unknown) ->
              let uu___1 =
                let uu___2 = FStar_Syntax_Print.univ_to_string u11 in
                let uu___3 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Compiler_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu___2 uu___3 in
              failwith uu___1
          | (FStar_Syntax_Syntax.U_name x, FStar_Syntax_Syntax.U_name y) ->
              let uu___ =
                let uu___1 = FStar_Ident.string_of_id x in
                let uu___2 = FStar_Ident.string_of_id y in uu___1 = uu___2 in
              if uu___
              then USolved wl
              else ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12, FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1, FStar_Syntax_Syntax.U_unif v2) ->
              let uu___ = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu___
              then USolved wl
              else
                (let wl1 =
                   extend_universe_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1, u) ->
              let u3 = norm_univ wl u in
              let uu___ = occurs_univ v1 u3 in
              if uu___
              then
                let uu___1 =
                  let uu___2 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu___3 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Compiler_Util.format2
                    "Failed occurs check: %s occurs in %s" uu___2 uu___3 in
                try_umax_components u11 u21 uu___1
              else
                (let uu___2 =
                   extend_universe_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu___2)
          | (u, FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu___ = occurs_univ v1 u3 in
              if uu___
              then
                let uu___1 =
                  let uu___2 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu___3 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Compiler_Util.format2
                    "Failed occurs check: %s occurs in %s" uu___2 uu___3 in
                try_umax_components u11 u21 uu___1
              else
                (let uu___2 =
                   extend_universe_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu___2)
          | (FStar_Syntax_Syntax.U_max uu___, uu___1) ->
              if wl.defer_ok = DeferAny
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu___3 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu___3
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu___, FStar_Syntax_Syntax.U_max uu___1) ->
              if wl.defer_ok = DeferAny
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu___3 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu___3
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu___, FStar_Syntax_Syntax.U_zero) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu___, FStar_Syntax_Syntax.U_name
             uu___1) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_succ uu___) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_name uu___) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu___, FStar_Syntax_Syntax.U_succ
             uu___1) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu___, FStar_Syntax_Syntax.U_zero) ->
              ufailed_simple "Incompatible universes"
let (solve_universe_eq :
  Prims.int ->
    worklist ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> univ_eq_sol)
  =
  fun orig ->
    fun wl ->
      fun u1 ->
        fun u2 ->
          if (wl.tcenv).FStar_TypeChecker_Env.lax_universes
          then USolved wl
          else really_solve_universe_eq orig wl u1 u2
let match_num_binders :
  'a 'b .
    ('a Prims.list * ('a Prims.list -> 'b)) ->
      ('a Prims.list * ('a Prims.list -> 'b)) ->
        (('a Prims.list * 'b) * ('a Prims.list * 'b))
  =
  fun bc1 ->
    fun bc2 ->
      let uu___ = bc1 in
      match uu___ with
      | (bs1, mk_cod1) ->
          let uu___1 = bc2 in
          (match uu___1 with
           | (bs2, mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs, y::ys) ->
                     let uu___2 = aux xs ys in
                     (match uu___2 with
                      | ((xs1, xr), (ys1, yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs, ys) ->
                     let uu___2 = let uu___3 = mk_cod1 xs in ([], uu___3) in
                     let uu___3 = let uu___4 = mk_cod2 ys in ([], uu___4) in
                     (uu___2, uu___3) in
               aux bs1 bs2)
let (guard_of_prob :
  FStar_TypeChecker_Env.env ->
    worklist ->
      tprob ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist))
  =
  fun env ->
    fun wl ->
      fun problem ->
        fun t1 ->
          fun t2 ->
            let has_type_guard t11 t21 =
              match problem.FStar_TypeChecker_Common.element with
              | FStar_Pervasives_Native.Some t ->
                  let uu___ = FStar_Syntax_Syntax.bv_to_name t in
                  FStar_Syntax_Util.mk_has_type t11 uu___ t21
              | FStar_Pervasives_Native.None ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11 in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11 in
                  let uu___ =
                    let uu___1 = FStar_Syntax_Syntax.bv_to_name x in
                    FStar_Syntax_Util.mk_has_type t11 uu___1 t21 in
                  FStar_Syntax_Util.mk_forall u_x x uu___ in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB ->
                let uu___ = has_type_guard t1 t2 in (uu___, wl)
            | FStar_TypeChecker_Common.SUBINV ->
                let uu___ = has_type_guard t2 t1 in (uu___, wl)
let (is_flex_pat : flex_t -> Prims.bool) =
  fun uu___ ->
    match uu___ with | Flex (uu___1, uu___2, []) -> true | uu___1 -> false
let (should_defer_flex_to_user_tac :
  FStar_TypeChecker_Env.env -> worklist -> flex_t -> Prims.bool) =
  fun env ->
    fun wl ->
      fun f ->
        let uu___ = f in
        match uu___ with
        | Flex (uu___1, u, uu___2) ->
            let b =
              FStar_TypeChecker_DeferredImplicits.should_defer_uvar_to_user_tac
                wl.tcenv u in
            ((let uu___4 =
                FStar_Compiler_Effect.op_Less_Bar
                  (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ResolveImplicitsHook") in
              if uu___4
              then
                let uu___5 =
                  FStar_Syntax_Print.ctx_uvar_to_string_no_reason u in
                let uu___6 = FStar_Compiler_Util.string_of_bool b in
                let uu___7 =
                  FStar_Compiler_Util.string_of_bool
                    env.FStar_TypeChecker_Env.enable_defer_to_tac in
                FStar_Compiler_Util.print3
                  "Rel.should_defer_flex_to_user_tac for %s returning %s (env.enable_defer_to_tac: %s)\n"
                  uu___5 uu___6 uu___7
              else ());
             b)
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env ->
    fun f ->
      let uu___ = f in
      match uu___ with
      | Flex (uu___1, ctx_uvar, args) ->
          let t_hd = FStar_Syntax_Util.ctx_uvar_typ ctx_uvar in
          let ctx = ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders in
          let name_exists_in x bs =
            FStar_Compiler_Util.for_some
              (fun uu___2 ->
                 match uu___2 with
                 | { FStar_Syntax_Syntax.binder_bv = y;
                     FStar_Syntax_Syntax.binder_qual = uu___3;
                     FStar_Syntax_Syntax.binder_attrs = uu___4;_} ->
                     FStar_Syntax_Syntax.bv_eq x y) bs in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([], []) ->
                let uu___2 =
                  let uu___3 =
                    let uu___4 = FStar_Syntax_Syntax.mk_Total t_res in
                    FStar_Syntax_Util.arrow formals uu___4 in
                  ((FStar_Compiler_List.rev pat_binders), uu___3) in
                FStar_Pervasives_Native.Some uu___2
            | (uu___2, []) ->
                let uu___3 =
                  let uu___4 =
                    let uu___5 = FStar_Syntax_Syntax.mk_Total t_res in
                    FStar_Syntax_Util.arrow formals uu___5 in
                  ((FStar_Compiler_List.rev pat_binders), uu___4) in
                FStar_Pervasives_Native.Some uu___3
            | (fml::formals1, (a, a_imp)::args2) ->
                let uu___2 =
                  ((fml.FStar_Syntax_Syntax.binder_bv),
                    (fml.FStar_Syntax_Syntax.binder_qual)) in
                (match uu___2 with
                 | (formal, formal_imp) ->
                     let uu___3 =
                       let uu___4 = FStar_Syntax_Subst.compress a in
                       uu___4.FStar_Syntax_Syntax.n in
                     (match uu___3 with
                      | FStar_Syntax_Syntax.Tm_name x ->
                          let uu___4 =
                            (name_exists_in x ctx) ||
                              (name_exists_in x pat_binders) in
                          if uu___4
                          then aux (fml :: pat_binders) formals1 t_res args2
                          else
                            (let x1 =
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (x.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (x.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort =
                                   (formal.FStar_Syntax_Syntax.sort)
                               } in
                             let subst =
                               let uu___6 =
                                 let uu___7 =
                                   let uu___8 =
                                     FStar_Syntax_Syntax.bv_to_name x1 in
                                   (formal, uu___8) in
                                 FStar_Syntax_Syntax.NT uu___7 in
                               [uu___6] in
                             let formals2 =
                               FStar_Syntax_Subst.subst_binders subst
                                 formals1 in
                             let t_res1 =
                               FStar_Syntax_Subst.subst subst t_res in
                             let uu___6 =
                               FStar_Syntax_Util.bqual_and_attrs_of_aqual
                                 a_imp in
                             match uu___6 with
                             | (q, uu___7) ->
                                 let uu___8 =
                                   let uu___9 =
                                     FStar_Syntax_Syntax.mk_binder_with_attrs
                                       {
                                         FStar_Syntax_Syntax.ppname =
                                           (x1.FStar_Syntax_Syntax.ppname);
                                         FStar_Syntax_Syntax.index =
                                           (x1.FStar_Syntax_Syntax.index);
                                         FStar_Syntax_Syntax.sort =
                                           (formal.FStar_Syntax_Syntax.sort)
                                       } q
                                       fml.FStar_Syntax_Syntax.binder_attrs in
                                   uu___9 :: pat_binders in
                                 aux uu___8 formals2 t_res1 args2)
                      | uu___4 ->
                          aux (fml :: pat_binders) formals1 t_res args2))
            | ([], args2) ->
                let uu___2 =
                  let uu___3 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res in
                  FStar_Syntax_Util.arrow_formals uu___3 in
                (match uu___2 with
                 | (more_formals, t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu___3 -> aux pat_binders more_formals t_res1 args2)) in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu___2 ->
               let uu___3 = FStar_Syntax_Util.arrow_formals t_hd in
               (match uu___3 with
                | (formals, t_res) -> aux [] formals t_res args))
let (run_meta_arg_tac :
  FStar_Syntax_Syntax.ctx_uvar -> FStar_Syntax_Syntax.term) =
  fun ctx_u ->
    match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Ctx_uvar_meta_tac
        (env_dyn, tau)) ->
        let env = FStar_Compiler_Dyn.undyn env_dyn in
        ((let uu___1 =
            FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
          if uu___1
          then
            let uu___2 = FStar_Syntax_Print.ctx_uvar_to_string ctx_u in
            FStar_Compiler_Util.print1 "Running tactic for meta-arg %s\n"
              uu___2
          else ());
         FStar_Errors.with_ctx "Running tactic for meta-arg"
           (fun uu___1 ->
              let uu___2 = FStar_Syntax_Util.ctx_uvar_typ ctx_u in
              env.FStar_TypeChecker_Env.synth_hook env uu___2 tau))
    | uu___ ->
        failwith
          "run_meta_arg_tac must have been called with a uvar that has a meta tac"
let (simplify_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun g ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          ((let uu___1 =
              FStar_Compiler_Effect.op_Less_Bar
                (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu___1
            then
              let uu___2 = FStar_Syntax_Print.term_to_string f in
              FStar_Compiler_Util.print1 "Simplifying guard %s\n" uu___2
            else ());
           (let f1 =
              norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.6"
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f in
            (let uu___2 =
               FStar_Compiler_Effect.op_Less_Bar
                 (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu___2
             then
               let uu___3 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Compiler_Util.print1 "Simplified guard to %s\n" uu___3
             else ());
            (let f2 = FStar_Syntax_Util.unmeta f1 in
             let f3 =
               let uu___2 = FStar_Syntax_Util.un_squash f2 in
               match uu___2 with
               | FStar_Pervasives_Native.Some f4 -> f4
               | uu___3 -> f2 in
             let f4 =
               let uu___2 =
                 let uu___3 = FStar_Syntax_Util.unmeta f3 in
                 uu___3.FStar_Syntax_Syntax.n in
               match uu___2 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu___3 -> FStar_TypeChecker_Common.NonTrivial f3 in
             {
               FStar_TypeChecker_Common.guard_f = f4;
               FStar_TypeChecker_Common.deferred_to_tac =
                 (g.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (g.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (g.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (g.FStar_TypeChecker_Common.implicits)
             })))
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env ->
    fun probs ->
      (let uu___1 =
         FStar_Compiler_Effect.op_Less_Bar (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel") in
       if uu___1
       then
         let uu___2 = wl_to_string probs in
         FStar_Compiler_Util.print1 "solve:\n\t%s\n" uu___2
       else ());
      (let uu___2 =
         FStar_Compiler_Effect.op_Less_Bar (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ImplicitTrace") in
       if uu___2
       then
         let uu___3 =
           FStar_TypeChecker_Common.implicits_to_string probs.wl_implicits in
         FStar_Compiler_Util.print1 "solve: wl_implicits = %s\n" uu___3
       else ());
      (let uu___2 = next_prob probs in
       match uu___2 with
       | FStar_Pervasives_Native.Some (hd, tl, rank1) ->
           let probs1 =
             {
               attempting = tl;
               wl_deferred = (probs.wl_deferred);
               wl_deferred_to_tac = (probs.wl_deferred_to_tac);
               ctr = (probs.ctr);
               defer_ok = (probs.defer_ok);
               smt_ok = (probs.smt_ok);
               umax_heuristic_ok = (probs.umax_heuristic_ok);
               tcenv = (probs.tcenv);
               wl_implicits = (probs.wl_implicits);
               repr_subcomp_allowed = (probs.repr_subcomp_allowed)
             } in
           (def_check_prob "solve,hd" hd;
            (match hd with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu___4 =
                   FStar_Compiler_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs in
                 if uu___4
                 then
                   let uu___5 =
                     solve_prob hd FStar_Pervasives_Native.None [] probs1 in
                   solve env uu___5
                 else
                   if
                     (rank1 = FStar_TypeChecker_Common.Rigid_rigid) ||
                       ((tp.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                          && (rank1 <> FStar_TypeChecker_Common.Flex_flex))
                   then solve_t' env tp probs1
                   else
                     if probs1.defer_ok = DeferAny
                     then
                       maybe_defer_to_user_tac env tp
                         "deferring flex_rigid or flex_flex subtyping" probs1
                     else
                       if rank1 = FStar_TypeChecker_Common.Flex_flex
                       then
                         solve_t' env
                           {
                             FStar_TypeChecker_Common.pid =
                               (tp.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs =
                               (tp.FStar_TypeChecker_Common.lhs);
                             FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.EQ;
                             FStar_TypeChecker_Common.rhs =
                               (tp.FStar_TypeChecker_Common.rhs);
                             FStar_TypeChecker_Common.element =
                               (tp.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (tp.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.logical_guard_uvar =
                               (tp.FStar_TypeChecker_Common.logical_guard_uvar);
                             FStar_TypeChecker_Common.reason =
                               (tp.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (tp.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (tp.FStar_TypeChecker_Common.rank)
                           } probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None ->
           (match probs.wl_deferred with
            | [] ->
                let uu___3 =
                  let uu___4 = as_deferred probs.wl_deferred_to_tac in
                  ([], uu___4, (probs.wl_implicits)) in
                Success uu___3
            | uu___3 ->
                let uu___4 =
                  FStar_Compiler_Effect.op_Bar_Greater probs.wl_deferred
                    (FStar_Compiler_List.partition
                       (fun uu___5 ->
                          match uu___5 with
                          | (c, uu___6, uu___7, uu___8) -> c < probs.ctr)) in
                (match uu___4 with
                 | (attempt1, rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu___5 =
                            let uu___6 = as_deferred probs.wl_deferred in
                            let uu___7 = as_deferred probs.wl_deferred_to_tac in
                            (uu___6, uu___7, (probs.wl_implicits)) in
                          Success uu___5
                      | uu___5 ->
                          let uu___6 =
                            let uu___7 =
                              FStar_Compiler_Effect.op_Bar_Greater attempt1
                                (FStar_Compiler_List.map
                                   (fun uu___8 ->
                                      match uu___8 with
                                      | (uu___9, uu___10, uu___11, y) -> y)) in
                            {
                              attempting = uu___7;
                              wl_deferred = rest;
                              wl_deferred_to_tac = (probs.wl_deferred_to_tac);
                              ctr = (probs.ctr);
                              defer_ok = (probs.defer_ok);
                              smt_ok = (probs.smt_ok);
                              umax_heuristic_ok = (probs.umax_heuristic_ok);
                              tcenv = (probs.tcenv);
                              wl_implicits = (probs.wl_implicits);
                              repr_subcomp_allowed =
                                (probs.repr_subcomp_allowed)
                            } in
                          solve env uu___6))))
and (solve_one_universe_eq :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> worklist -> solution)
  =
  fun env ->
    fun orig ->
      fun u1 ->
        fun u2 ->
          fun wl ->
            let uu___ = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu___ with
            | USolved wl1 ->
                let uu___1 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                solve env uu___1
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 ->
                let uu___1 =
                  defer_lit FStar_TypeChecker_Common.Deferred_univ_constraint
                    "" orig wl1 in
                solve env uu___1
and (solve_maybe_uinsts :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> worklist -> univ_eq_sol)
  =
  fun env ->
    fun orig ->
      fun t1 ->
        fun t2 ->
          fun wl ->
            let rec aux wl1 us1 us2 =
              match (us1, us2) with
              | ([], []) -> USolved wl1
              | (u1::us11, u2::us21) ->
                  let uu___ = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu___ with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu___ -> ufailed_simple "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu___;
                  FStar_Syntax_Syntax.vars = uu___1;
                  FStar_Syntax_Syntax.hash_code = uu___2;_},
                us1),
               FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu___3;
                  FStar_Syntax_Syntax.vars = uu___4;
                  FStar_Syntax_Syntax.hash_code = uu___5;_},
                us2)) ->
                let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu___, uu___1) ->
                failwith "Impossible: expect head symbols to match"
            | (uu___, FStar_Syntax_Syntax.Tm_uinst uu___1) ->
                failwith "Impossible: expect head symbols to match"
            | uu___ -> USolved wl
and (giveup_or_defer :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      worklist ->
        FStar_TypeChecker_Common.deferred_reason -> lstring -> solution)
  =
  fun env ->
    fun orig ->
      fun wl ->
        fun reason ->
          fun msg ->
            if wl.defer_ok = DeferAny
            then
              ((let uu___1 =
                  FStar_Compiler_Effect.op_Less_Bar
                    (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel") in
                if uu___1
                then
                  let uu___2 = prob_to_string env orig in
                  let uu___3 = FStar_Thunk.force msg in
                  FStar_Compiler_Util.print2
                    "\n\t\tDeferring %s\n\t\tBecause %s\n" uu___2 uu___3
                else ());
               solve env (defer reason msg orig wl))
            else giveup env msg orig
and (giveup_or_defer_flex_flex :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      worklist ->
        FStar_TypeChecker_Common.deferred_reason -> lstring -> solution)
  =
  fun env ->
    fun orig ->
      fun wl ->
        fun reason ->
          fun msg ->
            if wl.defer_ok <> NoDefer
            then
              ((let uu___1 =
                  FStar_Compiler_Effect.op_Less_Bar
                    (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel") in
                if uu___1
                then
                  let uu___2 = prob_to_string env orig in
                  let uu___3 = FStar_Thunk.force msg in
                  FStar_Compiler_Util.print2
                    "\n\t\tDeferring %s\n\t\tBecause %s\n" uu___2 uu___3
                else ());
               solve env (defer reason msg orig wl))
            else giveup env msg orig
and (defer_to_user_tac :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.string -> worklist -> solution)
  =
  fun env ->
    fun orig ->
      fun reason ->
        fun wl ->
          (let uu___1 =
             FStar_Compiler_Effect.op_Less_Bar
               (FStar_TypeChecker_Env.debug env) (FStar_Options.Other "Rel") in
           if uu___1
           then
             let uu___2 = prob_to_string env orig in
             FStar_Compiler_Util.print1 "\n\t\tDeferring %s to a tactic\n"
               uu___2
           else ());
          (let wl1 = solve_prob orig FStar_Pervasives_Native.None [] wl in
           let wl2 =
             let uu___1 =
               let uu___2 =
                 let uu___3 = FStar_Thunk.mkv reason in
                 ((wl1.ctr), FStar_TypeChecker_Common.Deferred_to_user_tac,
                   uu___3, orig) in
               uu___2 :: (wl1.wl_deferred_to_tac) in
             {
               attempting = (wl1.attempting);
               wl_deferred = (wl1.wl_deferred);
               wl_deferred_to_tac = uu___1;
               ctr = (wl1.ctr);
               defer_ok = (wl1.defer_ok);
               smt_ok = (wl1.smt_ok);
               umax_heuristic_ok = (wl1.umax_heuristic_ok);
               tcenv = (wl1.tcenv);
               wl_implicits = (wl1.wl_implicits);
               repr_subcomp_allowed = (wl1.repr_subcomp_allowed)
             } in
           solve env wl2)
and (maybe_defer_to_user_tac :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem ->
      Prims.string -> worklist -> solution)
  =
  fun env ->
    fun prob ->
      fun reason ->
        fun wl ->
          match prob.FStar_TypeChecker_Common.relation with
          | FStar_TypeChecker_Common.EQ ->
              let should_defer_tac t =
                let uu___ = FStar_Syntax_Util.head_and_args t in
                match uu___ with
                | (head, uu___1) ->
                    let uu___2 =
                      let uu___3 = FStar_Syntax_Subst.compress head in
                      uu___3.FStar_Syntax_Syntax.n in
                    (match uu___2 with
                     | FStar_Syntax_Syntax.Tm_uvar (uv, uu___3) ->
                         let uu___4 =
                           FStar_TypeChecker_DeferredImplicits.should_defer_uvar_to_user_tac
                             wl.tcenv uv in
                         (uu___4, (uv.FStar_Syntax_Syntax.ctx_uvar_reason))
                     | uu___3 -> (false, "")) in
              let uu___ = should_defer_tac prob.FStar_TypeChecker_Common.lhs in
              (match uu___ with
               | (l1, r1) ->
                   let uu___1 =
                     should_defer_tac prob.FStar_TypeChecker_Common.rhs in
                   (match uu___1 with
                    | (l2, r2) ->
                        if l1 || l2
                        then
                          defer_to_user_tac env
                            (FStar_TypeChecker_Common.TProb prob)
                            (Prims.op_Hat r1 (Prims.op_Hat ", " r2)) wl
                        else
                          (let uu___3 =
                             defer_lit FStar_TypeChecker_Common.Deferred_flex
                               reason (FStar_TypeChecker_Common.TProb prob)
                               wl in
                           solve env uu___3)))
          | uu___ ->
              let uu___1 =
                defer_lit FStar_TypeChecker_Common.Deferred_flex reason
                  (FStar_TypeChecker_Common.TProb prob) wl in
              solve env uu___1
and (solve_rigid_flex_or_flex_rigid_subtyping :
  FStar_TypeChecker_Common.rank_t ->
    FStar_TypeChecker_Env.env -> tprob -> worklist -> solution)
  =
  fun rank1 ->
    fun env ->
      fun tp ->
        fun wl ->
          def_check_prob "solve_rigid_flex_or_flex_rigid_subtyping"
            (FStar_TypeChecker_Common.TProb tp);
          (let flip = rank1 = FStar_TypeChecker_Common.Flex_rigid in
           let meet_or_join op ts env1 wl1 =
             let eq_prob t1 t2 wl2 =
               let uu___1 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements" in
               match uu___1 with
               | (p, wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3)) in
             let pairwise t1 t2 wl2 =
               (let uu___2 =
                  FStar_Compiler_Effect.op_Less_Bar
                    (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel") in
                if uu___2
                then
                  let uu___3 = FStar_Syntax_Print.term_to_string t1 in
                  let uu___4 = FStar_Syntax_Print.term_to_string t2 in
                  FStar_Compiler_Util.print2
                    "[meet/join]: pairwise: %s and %s\n" uu___3 uu___4
                else ());
               (let uu___2 = head_matches_delta env1 wl2.smt_ok t1 t2 in
                match uu___2 with
                | (mr, ts1) ->
                    (match mr with
                     | HeadMatch (true) ->
                         let uu___3 = eq_prob t1 t2 wl2 in
                         (match uu___3 with | (p, wl3) -> (t1, [p], wl3))
                     | MisMatch uu___3 ->
                         let uu___4 = eq_prob t1 t2 wl2 in
                         (match uu___4 with | (p, wl3) -> (t1, [p], wl3))
                     | FullMatch ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11, t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false) ->
                         let uu___3 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11, t21) ->
                               let uu___4 = FStar_Syntax_Subst.compress t11 in
                               let uu___5 = FStar_Syntax_Subst.compress t21 in
                               (uu___4, uu___5)
                           | FStar_Pervasives_Native.None ->
                               let uu___4 = FStar_Syntax_Subst.compress t1 in
                               let uu___5 = FStar_Syntax_Subst.compress t2 in
                               (uu___4, uu___5) in
                         (match uu___3 with
                          | (t11, t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu___4 =
                                  FStar_Syntax_Util.head_and_args t12 in
                                match uu___4 with
                                | (t1_hd, t1_args) ->
                                    let uu___5 =
                                      FStar_Syntax_Util.head_and_args t22 in
                                    (match uu___5 with
                                     | (t2_hd, t2_args) ->
                                         if
                                           (FStar_Compiler_List.length
                                              t1_args)
                                             <>
                                             (FStar_Compiler_List.length
                                                t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu___7 =
                                              let uu___8 =
                                                let uu___9 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd in
                                                uu___9 :: t1_args in
                                              let uu___9 =
                                                let uu___10 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd in
                                                uu___10 :: t2_args in
                                              FStar_Compiler_List.fold_left2
                                                (fun uu___10 ->
                                                   fun uu___11 ->
                                                     fun uu___12 ->
                                                       match (uu___10,
                                                               uu___11,
                                                               uu___12)
                                                       with
                                                       | ((probs, wl4),
                                                          (a1, uu___13),
                                                          (a2, uu___14)) ->
                                                           let uu___15 =
                                                             eq_prob a1 a2
                                                               wl4 in
                                                           (match uu___15
                                                            with
                                                            | (p, wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu___8 uu___9 in
                                            match uu___7 with
                                            | (probs, wl4) ->
                                                let wl' =
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    wl_deferred_to_tac =
                                                      (wl4.wl_deferred_to_tac);
                                                    ctr = (wl4.ctr);
                                                    defer_ok = NoDefer;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (wl4.umax_heuristic_ok);
                                                    tcenv = (wl4.tcenv);
                                                    wl_implicits = [];
                                                    repr_subcomp_allowed =
                                                      (wl4.repr_subcomp_allowed)
                                                  } in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    () in
                                                let uu___8 = solve env1 wl' in
                                                (match uu___8 with
                                                 | Success
                                                     (uu___9, defer_to_tac,
                                                      imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      (let uu___11 =
                                                         extend_wl wl4 []
                                                           defer_to_tac imps in
                                                       FStar_Pervasives_Native.Some
                                                         uu___11))
                                                 | Failed uu___9 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None)))) in
                              let combine t12 t22 wl3 =
                                let uu___4 =
                                  base_and_refinement_maybe_delta false env1
                                    t12 in
                                match uu___4 with
                                | (t1_base, p1_opt) ->
                                    let uu___5 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22 in
                                    (match uu___5 with
                                     | (t2_base, p2_opt) ->
                                         let apply_op op1 phi1 phi2 =
                                           let squash phi =
                                             let uu___6 =
                                               env1.FStar_TypeChecker_Env.universe_of
                                                 env1 phi in
                                             match uu___6 with
                                             | FStar_Syntax_Syntax.U_zero ->
                                                 phi
                                             | u ->
                                                 FStar_Syntax_Util.mk_squash
                                                   u phi in
                                           let uu___6 = squash phi1 in
                                           let uu___7 = squash phi2 in
                                           op1 uu___6 uu___7 in
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine x t =
                                             let uu___6 =
                                               FStar_Syntax_Util.is_t_true t in
                                             if uu___6
                                             then x.FStar_Syntax_Syntax.sort
                                             else
                                               FStar_Syntax_Util.refine x t in
                                           match (p1_opt1, p2_opt1) with
                                           | (FStar_Pervasives_Native.Some
                                              (x, phi1),
                                              FStar_Pervasives_Native.Some
                                              (y, phi2)) ->
                                               let x1 =
                                                 FStar_Syntax_Syntax.freshen_bv
                                                   x in
                                               let subst =
                                                 [FStar_Syntax_Syntax.DB
                                                    (Prims.int_zero, x1)] in
                                               let phi11 =
                                                 FStar_Syntax_Subst.subst
                                                   subst phi1 in
                                               let phi21 =
                                                 FStar_Syntax_Subst.subst
                                                   subst phi2 in
                                               let uu___6 =
                                                 apply_op op phi11 phi21 in
                                               refine x1 uu___6
                                           | (FStar_Pervasives_Native.None,
                                              FStar_Pervasives_Native.Some
                                              (x, phi)) ->
                                               let x1 =
                                                 FStar_Syntax_Syntax.freshen_bv
                                                   x in
                                               let subst =
                                                 [FStar_Syntax_Syntax.DB
                                                    (Prims.int_zero, x1)] in
                                               let phi1 =
                                                 FStar_Syntax_Subst.subst
                                                   subst phi in
                                               let uu___6 =
                                                 apply_op op
                                                   FStar_Syntax_Util.t_true
                                                   phi1 in
                                               refine x1 uu___6
                                           | (FStar_Pervasives_Native.Some
                                              (x, phi),
                                              FStar_Pervasives_Native.None)
                                               ->
                                               let x1 =
                                                 FStar_Syntax_Syntax.freshen_bv
                                                   x in
                                               let subst =
                                                 [FStar_Syntax_Syntax.DB
                                                    (Prims.int_zero, x1)] in
                                               let phi1 =
                                                 FStar_Syntax_Subst.subst
                                                   subst phi in
                                               let uu___6 =
                                                 apply_op op
                                                   FStar_Syntax_Util.t_true
                                                   phi1 in
                                               refine x1 uu___6
                                           | uu___6 -> t_base in
                                         let uu___6 =
                                           try_eq t1_base t2_base wl3 in
                                         (match uu___6 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu___7 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt in
                                              (uu___7, [], wl4)
                                          | FStar_Pervasives_Native.None ->
                                              let uu___7 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12 in
                                              (match uu___7 with
                                               | (t1_base1, p1_opt1) ->
                                                   let uu___8 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22 in
                                                   (match uu___8 with
                                                    | (t2_base1, p2_opt1) ->
                                                        let uu___9 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3 in
                                                        (match uu___9 with
                                                         | (p, wl4) ->
                                                             let t =
                                                               combine_refinements
                                                                 t1_base1
                                                                 p1_opt1
                                                                 p2_opt1 in
                                                             (t, [p], wl4)))))) in
                              let uu___4 = combine t11 t21 wl2 in
                              (match uu___4 with
                               | (t12, ps, wl3) ->
                                   ((let uu___6 =
                                       FStar_Compiler_Effect.op_Less_Bar
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel") in
                                     if uu___6
                                     then
                                       let uu___7 =
                                         FStar_Syntax_Print.term_to_string
                                           t12 in
                                       FStar_Compiler_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu___7
                                     else ());
                                    (t12, ps, wl3)))))) in
             let rec aux uu___1 ts1 =
               match uu___1 with
               | (out, probs, wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu___2 = pairwise out t wl2 in
                        (match uu___2 with
                         | (out1, probs', wl3) ->
                             aux
                               (out1,
                                 (FStar_Compiler_List.op_At probs probs'),
                                 wl3) ts2)) in
             let uu___1 =
               let uu___2 = FStar_Compiler_List.hd ts in (uu___2, [], wl1) in
             let uu___2 = FStar_Compiler_List.tl ts in aux uu___1 uu___2 in
           let uu___1 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs)) in
           match uu___1 with
           | (this_flex, this_rigid) ->
               let uu___2 =
                 let uu___3 = FStar_Syntax_Subst.compress this_rigid in
                 uu___3.FStar_Syntax_Syntax.n in
               (match uu___2 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs, comp) ->
                    let uu___3 = FStar_Syntax_Util.is_tot_or_gtot_comp comp in
                    if uu___3
                    then
                      let uu___4 = destruct_flex_t env this_flex wl in
                      (match uu___4 with
                       | (flex, wl1) ->
                           let uu___5 = quasi_pattern env flex in
                           (match uu___5 with
                            | FStar_Pervasives_Native.None ->
                                giveup_lit env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs, flex_t1)
                                ->
                                ((let uu___7 =
                                    FStar_Compiler_Effect.op_Less_Bar
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu___7
                                  then
                                    let uu___8 =
                                      FStar_Compiler_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid in
                                    FStar_Compiler_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu___8
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t1
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu___5 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              {
                                FStar_TypeChecker_Common.pid =
                                  (tp.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (tp.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ;
                                FStar_TypeChecker_Common.rhs =
                                  (tp.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (tp.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (tp.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (tp.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (tp.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (tp.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (tp.FStar_TypeChecker_Common.rank)
                              }] wl in
                       solve env uu___5)
                | uu___3 ->
                    ((let uu___5 =
                        FStar_Compiler_Effect.op_Less_Bar
                          (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel") in
                      if uu___5
                      then
                        let uu___6 =
                          FStar_Compiler_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid in
                        FStar_Compiler_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu___6
                      else ());
                     (let uu___5 = FStar_Syntax_Util.head_and_args this_flex in
                      match uu___5 with
                      | (u, _args) ->
                          let uu___6 =
                            let uu___7 = FStar_Syntax_Subst.compress u in
                            uu___7.FStar_Syntax_Syntax.n in
                          (match uu___6 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar, _subst)
                               ->
                               let equiv t =
                                 let uu___7 =
                                   FStar_Syntax_Util.head_and_args t in
                                 match uu___7 with
                                 | (u', uu___8) ->
                                     let uu___9 =
                                       let uu___10 = whnf env u' in
                                       uu___10.FStar_Syntax_Syntax.n in
                                     (match uu___9 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar', _subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu___10 -> false) in
                               let uu___7 =
                                 FStar_Compiler_Effect.op_Bar_Greater
                                   wl.attempting
                                   (FStar_Compiler_List.partition
                                      (fun uu___8 ->
                                         match uu___8 with
                                         | FStar_TypeChecker_Common.TProb tp1
                                             ->
                                             let tp2 = maybe_invert tp1 in
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
                                              | uu___9 -> false)
                                         | uu___9 -> false)) in
                               (match uu___7 with
                                | (bounds_probs, rest) ->
                                    let bounds_typs =
                                      let uu___8 = whnf env this_rigid in
                                      let uu___9 =
                                        FStar_Compiler_List.collect
                                          (fun uu___10 ->
                                             match uu___10 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu___11 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs in
                                                 [uu___11]
                                             | uu___11 -> []) bounds_probs in
                                      uu___8 :: uu___9 in
                                    let uu___8 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl in
                                    (match uu___8 with
                                     | (bound, sub_probs, wl1) ->
                                         let uu___9 =
                                           let flex_u =
                                             flex_uvar_head this_flex in
                                           let bound1 =
                                             let uu___10 =
                                               let uu___11 =
                                                 FStar_Syntax_Subst.compress
                                                   bound in
                                               uu___11.FStar_Syntax_Syntax.n in
                                             match uu___10 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x, phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu___11 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort in
                                                    FStar_Pervasives_Native.snd
                                                      uu___11)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu___11 -> bound in
                                           let uu___10 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements") in
                                           (bound1, uu___10) in
                                         (match uu___9 with
                                          | (bound_typ, (eq_prob, wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu___12 =
                                                  FStar_Compiler_Effect.op_Less_Bar
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel") in
                                                if uu___12
                                                then
                                                  let wl'1 =
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (wl1.wl_deferred);
                                                      wl_deferred_to_tac =
                                                        (wl1.wl_deferred_to_tac);
                                                      ctr = (wl1.ctr);
                                                      defer_ok =
                                                        (wl1.defer_ok);
                                                      smt_ok = (wl1.smt_ok);
                                                      umax_heuristic_ok =
                                                        (wl1.umax_heuristic_ok);
                                                      tcenv = (wl1.tcenv);
                                                      wl_implicits =
                                                        (wl1.wl_implicits);
                                                      repr_subcomp_allowed =
                                                        (wl1.repr_subcomp_allowed)
                                                    } in
                                                  let uu___13 =
                                                    wl_to_string wl'1 in
                                                  FStar_Compiler_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu___13
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    () in
                                                let uu___12 =
                                                  solve_t env eq_prob
                                                    {
                                                      attempting = sub_probs;
                                                      wl_deferred = [];
                                                      wl_deferred_to_tac =
                                                        (wl'.wl_deferred_to_tac);
                                                      ctr = (wl'.ctr);
                                                      defer_ok = NoDefer;
                                                      smt_ok = (wl'.smt_ok);
                                                      umax_heuristic_ok =
                                                        (wl'.umax_heuristic_ok);
                                                      tcenv = (wl'.tcenv);
                                                      wl_implicits = [];
                                                      repr_subcomp_allowed =
                                                        (wl'.repr_subcomp_allowed)
                                                    } in
                                                match uu___12 with
                                                | Success
                                                    (uu___13, defer_to_tac,
                                                     imps)
                                                    ->
                                                    let wl2 =
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (wl'.wl_deferred);
                                                        wl_deferred_to_tac =
                                                          (wl'.wl_deferred_to_tac);
                                                        ctr = (wl'.ctr);
                                                        defer_ok =
                                                          (wl'.defer_ok);
                                                        smt_ok = (wl'.smt_ok);
                                                        umax_heuristic_ok =
                                                          (wl'.umax_heuristic_ok);
                                                        tcenv = (wl'.tcenv);
                                                        wl_implicits =
                                                          (wl'.wl_implicits);
                                                        repr_subcomp_allowed
                                                          =
                                                          (wl'.repr_subcomp_allowed)
                                                      } in
                                                    let wl3 =
                                                      extend_wl wl2 []
                                                        defer_to_tac imps in
                                                    let g =
                                                      FStar_Compiler_List.fold_left
                                                        (fun g1 ->
                                                           fun p ->
                                                             FStar_Syntax_Util.mk_conj
                                                               g1 (p_guard p))
                                                        eq_prob.FStar_TypeChecker_Common.logical_guard
                                                        sub_probs in
                                                    let wl4 =
                                                      solve_prob' false
                                                        (FStar_TypeChecker_Common.TProb
                                                           tp)
                                                        (FStar_Pervasives_Native.Some
                                                           g) [] wl3 in
                                                    let uu___14 =
                                                      FStar_Compiler_List.fold_left
                                                        (fun wl5 ->
                                                           fun p ->
                                                             solve_prob' true
                                                               p
                                                               FStar_Pervasives_Native.None
                                                               [] wl5) wl4
                                                        bounds_probs in
                                                    (FStar_Syntax_Unionfind.commit
                                                       tx;
                                                     solve env wl4)
                                                | Failed (p, msg) ->
                                                    ((let uu___14 =
                                                        FStar_Compiler_Effect.op_Less_Bar
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel") in
                                                      if uu___14
                                                      then
                                                        let uu___15 =
                                                          let uu___16 =
                                                            FStar_Compiler_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs) in
                                                          FStar_Compiler_Effect.op_Bar_Greater
                                                            uu___16
                                                            (FStar_String.concat
                                                               "\n") in
                                                        FStar_Compiler_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu___15
                                                      else ());
                                                     (let uu___14 =
                                                        let uu___15 =
                                                          base_and_refinement
                                                            env bound_typ in
                                                        (rank1, uu___15) in
                                                      match uu___14 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex,
                                                         (t_base,
                                                          FStar_Pervasives_Native.Some
                                                          uu___15)) ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu___17 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping" in
                                                            match uu___17
                                                            with
                                                            | (eq_prob1, wl2)
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
                                                                    [] wl2 in
                                                                  let uu___19
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3 in
                                                                  solve env
                                                                    uu___19))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid,
                                                         (t_base,
                                                          FStar_Pervasives_Native.Some
                                                          (x, phi))) ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu___16 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping" in
                                                            match uu___16
                                                            with
                                                            | (eq_prob1, wl2)
                                                                ->
                                                                (def_check_prob
                                                                   "meet_or_join4"
                                                                   (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1);
                                                                 (let phi1 =
                                                                    guard_on_element
                                                                    wl2 tp x
                                                                    phi in
                                                                  let wl3 =
                                                                    let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1)) in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___19 in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu___18
                                                                    [] wl2 in
                                                                  let uu___18
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3 in
                                                                  solve env
                                                                    uu___18))))
                                                      | uu___15 ->
                                                          let uu___16 =
                                                            FStar_Thunk.map
                                                              (fun s ->
                                                                 Prims.op_Hat
                                                                   "failed to solve the sub-problems: "
                                                                   s) msg in
                                                          giveup env uu___16
                                                            p)))))))
                           | uu___7 when flip ->
                               let uu___8 =
                                 let uu___9 =
                                   FStar_Compiler_Util.string_of_int
                                     (rank_t_num rank1) in
                                 let uu___10 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp) in
                                 FStar_Compiler_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu___9 uu___10 in
                               failwith uu___8
                           | uu___7 ->
                               let uu___8 =
                                 let uu___9 =
                                   FStar_Compiler_Util.string_of_int
                                     (rank_t_num rank1) in
                                 let uu___10 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp) in
                                 FStar_Compiler_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu___9 uu___10 in
                               failwith uu___8)))))
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
  fun orig ->
    fun env ->
      fun wl ->
        fun lhs ->
          fun bs_lhs ->
            fun t_res_lhs ->
              fun rel ->
                fun arrow ->
                  let bs_lhs_args =
                    FStar_Compiler_List.map
                      (fun uu___ ->
                         match uu___ with
                         | { FStar_Syntax_Syntax.binder_bv = x;
                             FStar_Syntax_Syntax.binder_qual = i;
                             FStar_Syntax_Syntax.binder_attrs = uu___1;_} ->
                             let uu___2 = FStar_Syntax_Syntax.bv_to_name x in
                             (uu___2, i)) bs_lhs in
                  let uu___ = lhs in
                  match uu___ with
                  | Flex (uu___1, u_lhs, uu___2) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu___3 =
                            match uopt with
                            | FStar_Pervasives_Native.None ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu___4 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    t.FStar_Syntax_Syntax.pos in
                                (uu___4, univ) in
                          match uu___3 with
                          | (k, univ) ->
                              let uu___4 =
                                copy_uvar u_lhs
                                  (FStar_Compiler_List.op_At bs_lhs bs) k wl2 in
                              (match uu___4 with
                               | (uu___5, u, wl3) ->
                                   let uu___6 =
                                     f u (FStar_Pervasives_Native.Some univ) in
                                   (uu___6, wl3)) in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t, uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t, uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu___3 =
                              let uu___4 =
                                let uu___5 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ in
                                uu___5 ::
                                  (ct.FStar_Syntax_Syntax.effect_args) in
                              FStar_Compiler_List.fold_right
                                (fun uu___5 ->
                                   fun uu___6 ->
                                     match (uu___5, uu___6) with
                                     | ((a, i), (out_args, wl2)) ->
                                         let uu___7 =
                                           let uu___8 =
                                             let uu___9 =
                                               FStar_Syntax_Util.type_u () in
                                             FStar_Compiler_Effect.op_Less_Bar
                                               FStar_Pervasives_Native.fst
                                               uu___9 in
                                           copy_uvar u_lhs [] uu___8 wl2 in
                                         (match uu___7 with
                                          | (uu___8, t_a, wl3) ->
                                              let uu___9 =
                                                copy_uvar u_lhs bs t_a wl3 in
                                              (match uu___9 with
                                               | (uu___10, a', wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu___4 ([], wl1) in
                            (match uu___3 with
                             | (out_args, wl2) ->
                                 let nodec flags =
                                   FStar_Compiler_List.filter
                                     (fun uu___4 ->
                                        match uu___4 with
                                        | FStar_Syntax_Syntax.DECREASES
                                            uu___5 -> false
                                        | uu___5 -> true) flags in
                                 let ct' =
                                   let uu___4 =
                                     let uu___5 =
                                       FStar_Compiler_List.hd out_args in
                                     FStar_Pervasives_Native.fst uu___5 in
                                   let uu___5 =
                                     FStar_Compiler_List.tl out_args in
                                   let uu___6 =
                                     nodec ct.FStar_Syntax_Syntax.flags in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (ct.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (ct.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ = uu___4;
                                     FStar_Syntax_Syntax.effect_args = uu___5;
                                     FStar_Syntax_Syntax.flags = uu___6
                                   } in
                                 ({
                                    FStar_Syntax_Syntax.n =
                                      (FStar_Syntax_Syntax.Comp ct');
                                    FStar_Syntax_Syntax.pos =
                                      (c.FStar_Syntax_Syntax.pos);
                                    FStar_Syntax_Syntax.vars =
                                      (c.FStar_Syntax_Syntax.vars);
                                    FStar_Syntax_Syntax.hash_code =
                                      (c.FStar_Syntax_Syntax.hash_code)
                                  }, wl2)) in
                      let uu___3 = FStar_Syntax_Util.arrow_formals_comp arrow in
                      (match uu___3 with
                       | (formals, c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu___4 = imitate_comp bs bs_terms c wl1 in
                                 (match uu___4 with
                                  | (c', wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c' in
                                      let sol =
                                        let uu___5 =
                                          let uu___6 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs)) in
                                          (u_lhs, uu___6) in
                                        TERM uu___5 in
                                      let uu___5 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow FStar_Pervasives_Native.None
                                          "arrow imitation" in
                                      (match uu___5 with
                                       | (sub_prob, wl3) ->
                                           let uu___6 =
                                             let uu___7 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3 in
                                             attempt [sub_prob] uu___7 in
                                           solve env uu___6))
                             | { FStar_Syntax_Syntax.binder_bv = x;
                                 FStar_Syntax_Syntax.binder_qual = imp;
                                 FStar_Syntax_Syntax.binder_attrs = attrs;_}::formals2
                                 ->
                                 let uu___4 =
                                   let uu___5 =
                                     let uu___6 = FStar_Syntax_Util.type_u () in
                                     FStar_Compiler_Effect.op_Bar_Greater
                                       uu___6 FStar_Pervasives_Native.fst in
                                   copy_uvar u_lhs
                                     (FStar_Compiler_List.op_At bs_lhs bs)
                                     uu___5 wl1 in
                                 (match uu___4 with
                                  | (_ctx_u_x, u_x, wl2) ->
                                      let y =
                                        let uu___5 =
                                          let uu___6 =
                                            FStar_Syntax_Syntax.range_of_bv x in
                                          FStar_Pervasives_Native.Some uu___6 in
                                        FStar_Syntax_Syntax.new_bv uu___5 u_x in
                                      let b =
                                        FStar_Syntax_Syntax.mk_binder_with_attrs
                                          y imp attrs in
                                      let uu___5 =
                                        let uu___6 =
                                          let uu___7 =
                                            FStar_Syntax_Util.arg_of_non_null_binder
                                              b in
                                          [uu___7] in
                                        FStar_Compiler_List.op_At bs_terms
                                          uu___6 in
                                      aux (FStar_Compiler_List.op_At bs [b])
                                        uu___5 formals2 wl2) in
                           let uu___4 = occurs_check u_lhs arrow in
                           (match uu___4 with
                            | (uu___5, occurs_ok, msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu___6 =
                                    mklstr
                                      (fun uu___7 ->
                                         let uu___8 =
                                           FStar_Compiler_Option.get msg in
                                         Prims.op_Hat "occurs-check failed: "
                                           uu___8) in
                                  giveup_or_defer env orig wl
                                    FStar_TypeChecker_Common.Deferred_occur_check_failed
                                    uu___6
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
  fun env ->
    fun bs1 ->
      fun bs2 ->
        fun orig ->
          fun wl ->
            fun rhs ->
              (let uu___1 =
                 FStar_Compiler_Effect.op_Less_Bar
                   (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel") in
               if uu___1
               then
                 let uu___2 = FStar_Syntax_Print.binders_to_string ", " bs1 in
                 let uu___3 = FStar_Syntax_Print.binders_to_string ", " bs2 in
                 FStar_Compiler_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu___2 (rel_to_string (p_rel orig)) uu___3
               else ());
              (let eq_bqual a1 a2 =
                 match (a1, a2) with
                 | (FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit b1),
                    FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit b2)) ->
                     FStar_Syntax_Util.Equal
                 | uu___1 -> FStar_Syntax_Util.eq_bqual a1 a2 in
               let rec aux wl1 scope env1 subst xs ys =
                 match (xs, ys) with
                 | ([], []) ->
                     let uu___1 = rhs wl1 scope env1 subst in
                     (match uu___1 with
                      | (rhs_prob, wl2) ->
                          ((let uu___3 =
                              FStar_Compiler_Effect.op_Less_Bar
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel") in
                            if uu___3
                            then
                              let uu___4 = prob_to_string env1 rhs_prob in
                              FStar_Compiler_Util.print1 "rhs_prob = %s\n"
                                uu___4
                            else ());
                           (let formula = p_guard rhs_prob in
                            (env1,
                              (FStar_Pervasives.Inl ([rhs_prob], formula)),
                              wl2))))
                 | (x::xs1, y::ys1) when
                     let uu___1 =
                       eq_bqual x.FStar_Syntax_Syntax.binder_qual
                         y.FStar_Syntax_Syntax.binder_qual in
                     uu___1 = FStar_Syntax_Util.Equal ->
                     let uu___1 =
                       ((x.FStar_Syntax_Syntax.binder_bv),
                         (x.FStar_Syntax_Syntax.binder_qual)) in
                     (match uu___1 with
                      | (hd1, imp) ->
                          let uu___2 =
                            ((y.FStar_Syntax_Syntax.binder_bv),
                              (y.FStar_Syntax_Syntax.binder_qual)) in
                          (match uu___2 with
                           | (hd2, imp') ->
                               let hd11 =
                                 let uu___3 =
                                   FStar_Syntax_Subst.subst subst
                                     hd1.FStar_Syntax_Syntax.sort in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (hd1.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (hd1.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu___3
                                 } in
                               let hd21 =
                                 let uu___3 =
                                   FStar_Syntax_Subst.subst subst
                                     hd2.FStar_Syntax_Syntax.sort in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (hd2.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (hd2.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu___3
                                 } in
                               let uu___3 =
                                 let uu___4 =
                                   FStar_Compiler_Effect.op_Less_Bar
                                     invert_rel (p_rel orig) in
                                 mk_t_problem wl1 scope orig
                                   hd11.FStar_Syntax_Syntax.sort uu___4
                                   hd21.FStar_Syntax_Syntax.sort
                                   FStar_Pervasives_Native.None
                                   "Formal parameter" in
                               (match uu___3 with
                                | (prob, wl2) ->
                                    let hd12 =
                                      FStar_Syntax_Syntax.freshen_bv hd11 in
                                    let subst1 =
                                      let uu___4 =
                                        FStar_Syntax_Subst.shift_subst
                                          Prims.int_one subst in
                                      (FStar_Syntax_Syntax.DB
                                         (Prims.int_zero, hd12))
                                        :: uu___4 in
                                    let env2 =
                                      FStar_TypeChecker_Env.push_bv env1 hd12 in
                                    let uu___4 =
                                      aux wl2
                                        (FStar_Compiler_List.op_At scope
                                           [{
                                              FStar_Syntax_Syntax.binder_bv =
                                                hd12;
                                              FStar_Syntax_Syntax.binder_qual
                                                =
                                                (x.FStar_Syntax_Syntax.binder_qual);
                                              FStar_Syntax_Syntax.binder_attrs
                                                =
                                                (x.FStar_Syntax_Syntax.binder_attrs)
                                            }]) env2 subst1 xs1 ys1 in
                                    (match uu___4 with
                                     | (env3, FStar_Pervasives.Inl
                                        (sub_probs, phi), wl3) ->
                                         let phi1 =
                                           let uu___5 =
                                             FStar_TypeChecker_Env.close_forall
                                               env3
                                               [{
                                                  FStar_Syntax_Syntax.binder_bv
                                                    = hd12;
                                                  FStar_Syntax_Syntax.binder_qual
                                                    =
                                                    (x.FStar_Syntax_Syntax.binder_qual);
                                                  FStar_Syntax_Syntax.binder_attrs
                                                    =
                                                    (x.FStar_Syntax_Syntax.binder_attrs)
                                                }] phi in
                                           FStar_Syntax_Util.mk_conj
                                             (p_guard prob) uu___5 in
                                         ((let uu___6 =
                                             FStar_Compiler_Effect.op_Less_Bar
                                               (FStar_TypeChecker_Env.debug
                                                  env3)
                                               (FStar_Options.Other "Rel") in
                                           if uu___6
                                           then
                                             let uu___7 =
                                               FStar_Syntax_Print.term_to_string
                                                 phi1 in
                                             let uu___8 =
                                               FStar_Syntax_Print.bv_to_string
                                                 hd12 in
                                             FStar_Compiler_Util.print2
                                               "Formula is %s\n\thd1=%s\n"
                                               uu___7 uu___8
                                           else ());
                                          (env3,
                                            (FStar_Pervasives.Inl
                                               ((prob :: sub_probs), phi1)),
                                            wl3))
                                     | fail -> fail))))
                 | uu___1 ->
                     (env1,
                       (FStar_Pervasives.Inr
                          "arity or argument-qualifier mismatch"), wl1) in
               let uu___1 = aux wl [] env [] bs1 bs2 in
               match uu___1 with
               | (env1, FStar_Pervasives.Inr msg, wl1) ->
                   giveup_lit env1 msg orig
               | (env1, FStar_Pervasives.Inl (sub_probs, phi), wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1 in
                   let uu___2 = attempt sub_probs wl2 in solve env1 uu___2)
and (try_solve_without_smt_or_else :
  FStar_TypeChecker_Env.env ->
    worklist ->
      (FStar_TypeChecker_Env.env -> worklist -> solution) ->
        (FStar_TypeChecker_Env.env ->
           worklist -> (FStar_TypeChecker_Common.prob * lstring) -> solution)
          -> solution)
  =
  fun env ->
    fun wl ->
      fun try_solve ->
        fun else_solve ->
          let wl' =
            {
              attempting = [];
              wl_deferred = [];
              wl_deferred_to_tac = (wl.wl_deferred_to_tac);
              ctr = (wl.ctr);
              defer_ok = NoDefer;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (wl.tcenv);
              wl_implicits = [];
              repr_subcomp_allowed = (wl.repr_subcomp_allowed)
            } in
          let tx = FStar_Syntax_Unionfind.new_transaction () in
          let uu___ = try_solve env wl' in
          match uu___ with
          | Success (uu___1, defer_to_tac, imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 = extend_wl wl [] defer_to_tac imps in solve env wl1))
          | Failed (p, s) ->
              (FStar_Syntax_Unionfind.rollback tx; else_solve env wl (p, s))
and (try_solve_then_or_else :
  FStar_TypeChecker_Env.env ->
    worklist ->
      (FStar_TypeChecker_Env.env -> worklist -> solution) ->
        (FStar_TypeChecker_Env.env -> worklist -> solution) ->
          (FStar_TypeChecker_Env.env -> worklist -> solution) -> solution)
  =
  fun env ->
    fun wl ->
      fun try_solve ->
        fun then_solve ->
          fun else_solve ->
            let empty_wl =
              {
                attempting = [];
                wl_deferred = [];
                wl_deferred_to_tac = (wl.wl_deferred_to_tac);
                ctr = (wl.ctr);
                defer_ok = NoDefer;
                smt_ok = (wl.smt_ok);
                umax_heuristic_ok = (wl.umax_heuristic_ok);
                tcenv = (wl.tcenv);
                wl_implicits = [];
                repr_subcomp_allowed = (wl.repr_subcomp_allowed)
              } in
            let tx = FStar_Syntax_Unionfind.new_transaction () in
            let uu___ = try_solve env empty_wl in
            match uu___ with
            | Success (uu___1, defer_to_tac, imps) ->
                (FStar_Syntax_Unionfind.commit tx;
                 (let wl1 = extend_wl wl [] defer_to_tac imps in
                  then_solve env wl1))
            | Failed (p, s) ->
                (FStar_Syntax_Unionfind.rollback tx; else_solve env wl)
and (try_solve_probs_without_smt :
  FStar_TypeChecker_Env.env ->
    worklist ->
      (worklist -> (FStar_TypeChecker_Common.probs * worklist)) ->
        (worklist, lstring) FStar_Pervasives.either)
  =
  fun env ->
    fun wl ->
      fun probs ->
        let uu___ = probs wl in
        match uu___ with
        | (probs1, wl') ->
            let wl'1 =
              {
                attempting = probs1;
                wl_deferred = [];
                wl_deferred_to_tac = (wl.wl_deferred_to_tac);
                ctr = (wl.ctr);
                defer_ok = NoDefer;
                smt_ok = false;
                umax_heuristic_ok = false;
                tcenv = (wl.tcenv);
                wl_implicits = [];
                repr_subcomp_allowed = (wl.repr_subcomp_allowed)
              } in
            let uu___1 = solve env wl'1 in
            (match uu___1 with
             | Success (uu___2, defer_to_tac, imps) ->
                 let wl1 = extend_wl wl [] defer_to_tac imps in
                 FStar_Pervasives.Inl wl1
             | Failed (uu___2, ls) -> FStar_Pervasives.Inr ls)
and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env ->
    fun problem ->
      fun wl ->
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu___1 = compress_tprob wl.tcenv problem in
         solve_t' env uu___1 wl)
and (solve_t_flex_rigid_eq :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      worklist -> flex_t -> FStar_Syntax_Syntax.term -> solution)
  =
  fun env ->
    fun orig ->
      fun wl ->
        fun lhs ->
          fun rhs ->
            (let uu___1 =
               FStar_Compiler_Effect.op_Less_Bar
                 (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Rel") in
             if uu___1
             then FStar_Compiler_Util.print_string "solve_t_flex_rigid_eq\n"
             else ());
            (let uu___1 = should_defer_flex_to_user_tac env wl lhs in
             if uu___1
             then defer_to_user_tac env orig (flex_reason lhs) wl
             else
               (let mk_solution env1 lhs1 bs rhs1 =
                  let bs_orig = bs in
                  let rhs_orig = rhs1 in
                  let uu___3 = lhs1 in
                  match uu___3 with
                  | Flex (uu___4, ctx_u, args) ->
                      let uu___5 =
                        let bv_not_free_in_arg x arg =
                          let uu___6 =
                            let uu___7 =
                              FStar_Syntax_Free.names
                                (FStar_Pervasives_Native.fst arg) in
                            FStar_Compiler_Util.set_mem x uu___7 in
                          Prims.op_Negation uu___6 in
                        let bv_not_free_in_args x args1 =
                          FStar_Compiler_Util.for_all (bv_not_free_in_arg x)
                            args1 in
                        let binder_matches_aqual b aq =
                          match ((b.FStar_Syntax_Syntax.binder_qual), aq)
                          with
                          | (FStar_Pervasives_Native.None,
                             FStar_Pervasives_Native.None) -> true
                          | (FStar_Pervasives_Native.Some
                             (FStar_Syntax_Syntax.Implicit uu___6),
                             FStar_Pervasives_Native.Some a) ->
                              a.FStar_Syntax_Syntax.aqual_implicit &&
                                (FStar_Syntax_Util.eqlist
                                   (fun x ->
                                      fun y ->
                                        let uu___7 =
                                          FStar_Syntax_Util.eq_tm x y in
                                        uu___7 = FStar_Syntax_Util.Equal)
                                   b.FStar_Syntax_Syntax.binder_attrs
                                   a.FStar_Syntax_Syntax.aqual_attributes)
                          | uu___6 -> false in
                        let rec remove_matching_prefix lhs_binders rhs_args =
                          match (lhs_binders, rhs_args) with
                          | ([], uu___6) -> (lhs_binders, rhs_args)
                          | (uu___6, []) -> (lhs_binders, rhs_args)
                          | (b::lhs_tl, (t, aq)::rhs_tl) ->
                              let uu___6 =
                                let uu___7 = FStar_Syntax_Subst.compress t in
                                uu___7.FStar_Syntax_Syntax.n in
                              (match uu___6 with
                               | FStar_Syntax_Syntax.Tm_name x when
                                   ((FStar_Syntax_Syntax.bv_eq
                                       b.FStar_Syntax_Syntax.binder_bv x)
                                      && (binder_matches_aqual b aq))
                                     &&
                                     (bv_not_free_in_args
                                        b.FStar_Syntax_Syntax.binder_bv
                                        rhs_tl)
                                   -> remove_matching_prefix lhs_tl rhs_tl
                               | uu___7 -> (lhs_binders, rhs_args)) in
                        let uu___6 = FStar_Syntax_Util.head_and_args rhs1 in
                        match uu___6 with
                        | (rhs_hd, rhs_args) ->
                            let uu___7 =
                              let uu___8 =
                                remove_matching_prefix
                                  (FStar_Compiler_List.rev bs_orig)
                                  (FStar_Compiler_List.rev rhs_args) in
                              FStar_Compiler_Effect.op_Bar_Greater uu___8
                                (fun uu___9 ->
                                   match uu___9 with
                                   | (bs_rev, args_rev) ->
                                       ((FStar_Compiler_List.rev bs_rev),
                                         (FStar_Compiler_List.rev args_rev))) in
                            (match uu___7 with
                             | (bs1, rhs_args1) ->
                                 let uu___8 =
                                   FStar_Syntax_Syntax.mk_Tm_app rhs_hd
                                     rhs_args1 rhs1.FStar_Syntax_Syntax.pos in
                                 (bs1, uu___8)) in
                      (match uu___5 with
                       | (bs1, rhs2) ->
                           let sol =
                             match bs1 with
                             | [] -> rhs2
                             | uu___6 ->
                                 let uu___7 =
                                   FStar_Syntax_Util.ctx_uvar_typ ctx_u in
                                 let uu___8 = sn_binders env1 bs1 in
                                 u_abs uu___7 uu___8 rhs2 in
                           [TERM (ctx_u, sol)]) in
                let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
                  (let uu___4 =
                     FStar_Compiler_Effect.op_Less_Bar
                       (FStar_TypeChecker_Env.debug env1)
                       (FStar_Options.Other "Rel") in
                   if uu___4
                   then
                     FStar_Compiler_Util.print_string "try_quasi_pattern\n"
                   else ());
                  (let uu___4 = quasi_pattern env1 lhs1 in
                   match uu___4 with
                   | FStar_Pervasives_Native.None ->
                       ((FStar_Pervasives.Inl "Not a quasi-pattern"), wl1)
                   | FStar_Pervasives_Native.Some (bs, uu___5) ->
                       let uu___6 = lhs1 in
                       (match uu___6 with
                        | Flex (t_lhs, ctx_u, args) ->
                            let uu___7 = occurs_check ctx_u rhs1 in
                            (match uu___7 with
                             | (uvars, occurs_ok, msg) ->
                                 if Prims.op_Negation occurs_ok
                                 then
                                   let uu___8 =
                                     let uu___9 =
                                       let uu___10 =
                                         FStar_Compiler_Option.get msg in
                                       Prims.op_Hat
                                         "quasi-pattern, occurs-check failed: "
                                         uu___10 in
                                     FStar_Pervasives.Inl uu___9 in
                                   (uu___8, wl1)
                                 else
                                   (let fvs_lhs =
                                      binders_as_bv_set
                                        (FStar_Compiler_List.op_At
                                           ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                           bs) in
                                    let fvs_rhs =
                                      FStar_Syntax_Free.names rhs1 in
                                    let uu___9 =
                                      let uu___10 =
                                        FStar_Compiler_Util.set_is_subset_of
                                          fvs_rhs fvs_lhs in
                                      Prims.op_Negation uu___10 in
                                    if uu___9
                                    then
                                      ((FStar_Pervasives.Inl
                                          "quasi-pattern, free names on the RHS are not included in the LHS"),
                                        wl1)
                                    else
                                      (let uu___11 =
                                         let uu___12 =
                                           mk_solution env1 lhs1 bs rhs1 in
                                         FStar_Pervasives.Inr uu___12 in
                                       let uu___12 =
                                         restrict_all_uvars env1 ctx_u []
                                           uvars wl1 in
                                       (uu___11, uu___12)))))) in
                let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
                  let uu___3 = FStar_Syntax_Util.head_and_args rhs1 in
                  match uu___3 with
                  | (rhs_hd, args) ->
                      let uu___4 = FStar_Compiler_Util.prefix args in
                      (match uu___4 with
                       | (args_rhs, last_arg_rhs) ->
                           let rhs' =
                             FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                               rhs1.FStar_Syntax_Syntax.pos in
                           let uu___5 = lhs1 in
                           (match uu___5 with
                            | Flex (t_lhs, u_lhs, _lhs_args) ->
                                let uu___6 =
                                  let uu___7 =
                                    env1.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (env1.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (env1.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (env1.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (env1.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (env1.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (env1.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (env1.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          FStar_Pervasives_Native.None;
                                        FStar_TypeChecker_Env.sigtab =
                                          (env1.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (env1.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (env1.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (env1.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (env1.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (env1.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (env1.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (env1.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq_strict =
                                          (env1.FStar_TypeChecker_Env.use_eq_strict);
                                        FStar_TypeChecker_Env.is_iface =
                                          (env1.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (env1.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (env1.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (env1.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (env1.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (env1.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (env1.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (env1.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.typeof_tot_or_gtot_term
                                          =
                                          (env1.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                                        FStar_TypeChecker_Env.universe_of =
                                          (env1.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                          =
                                          (env1.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                        FStar_TypeChecker_Env.teq_nosmt_force
                                          =
                                          (env1.FStar_TypeChecker_Env.teq_nosmt_force);
                                        FStar_TypeChecker_Env.subtype_nosmt_force
                                          =
                                          (env1.FStar_TypeChecker_Env.subtype_nosmt_force);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          true;
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (env1.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (env1.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (env1.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (env1.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (env1.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (env1.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (env1.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (env1.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (env1.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (env1.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (env1.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (env1.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (env1.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (env1.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (env1.FStar_TypeChecker_Env.erasable_types_tab);
                                        FStar_TypeChecker_Env.enable_defer_to_tac
                                          =
                                          (env1.FStar_TypeChecker_Env.enable_defer_to_tac);
                                        FStar_TypeChecker_Env.unif_allow_ref_guards
                                          =
                                          (env1.FStar_TypeChecker_Env.unif_allow_ref_guards);
                                        FStar_TypeChecker_Env.erase_erasable_args
                                          =
                                          (env1.FStar_TypeChecker_Env.erase_erasable_args);
                                        FStar_TypeChecker_Env.core_check =
                                          (env1.FStar_TypeChecker_Env.core_check)
                                      }
                                      (FStar_Pervasives_Native.fst
                                         last_arg_rhs) false in
                                  match uu___7 with
                                  | (t_last_arg, uu___8) ->
                                      let uu___9 =
                                        let b =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg in
                                        let uu___10 =
                                          let uu___11 =
                                            let uu___12 =
                                              let uu___13 =
                                                FStar_Compiler_Effect.op_Bar_Greater
                                                  t_res_lhs
                                                  (env1.FStar_TypeChecker_Env.universe_of
                                                     env1) in
                                              FStar_Compiler_Effect.op_Bar_Greater
                                                uu___13
                                                (fun uu___14 ->
                                                   FStar_Pervasives_Native.Some
                                                     uu___14) in
                                            FStar_Compiler_Effect.op_Bar_Greater
                                              uu___12
                                              (FStar_Syntax_Syntax.mk_Total'
                                                 t_res_lhs) in
                                          FStar_Compiler_Effect.op_Bar_Greater
                                            uu___11
                                            (FStar_Syntax_Util.arrow [b]) in
                                        copy_uvar u_lhs
                                          (FStar_Compiler_List.op_At bs_lhs
                                             [b]) uu___10 wl1 in
                                      (match uu___9 with
                                       | (uu___10, lhs', wl2) ->
                                           let uu___11 =
                                             copy_uvar u_lhs bs_lhs
                                               t_last_arg wl2 in
                                           (match uu___11 with
                                            | (uu___12, lhs'_last_arg, wl3)
                                                -> (lhs', lhs'_last_arg, wl3))) in
                                (match uu___6 with
                                 | (lhs', lhs'_last_arg, wl2) ->
                                     let sol =
                                       let uu___7 =
                                         let uu___8 =
                                           let uu___9 =
                                             let uu___10 =
                                               FStar_Syntax_Syntax.mk_Tm_app
                                                 lhs'
                                                 [(lhs'_last_arg,
                                                    (FStar_Pervasives_Native.snd
                                                       last_arg_rhs))]
                                                 t_lhs.FStar_Syntax_Syntax.pos in
                                             FStar_Syntax_Util.abs bs_lhs
                                               uu___10
                                               (FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Util.residual_tot
                                                     t_res_lhs)) in
                                           (u_lhs, uu___9) in
                                         TERM uu___8 in
                                       [uu___7] in
                                     let uu___7 =
                                       let uu___8 =
                                         mk_t_problem wl2 [] orig1 lhs'
                                           FStar_TypeChecker_Common.EQ rhs'
                                           FStar_Pervasives_Native.None
                                           "first-order lhs" in
                                       match uu___8 with
                                       | (p1, wl3) ->
                                           let uu___9 =
                                             mk_t_problem wl3 [] orig1
                                               lhs'_last_arg
                                               FStar_TypeChecker_Common.EQ
                                               (FStar_Pervasives_Native.fst
                                                  last_arg_rhs)
                                               FStar_Pervasives_Native.None
                                               "first-order rhs" in
                                           (match uu___9 with
                                            | (p2, wl4) -> ([p1; p2], wl4)) in
                                     (match uu___7 with
                                      | (sub_probs, wl3) ->
                                          let uu___8 =
                                            let uu___9 =
                                              solve_prob orig1
                                                FStar_Pervasives_Native.None
                                                sol wl3 in
                                            attempt sub_probs uu___9 in
                                          solve env1 uu___8)))) in
                let imitate orig1 env1 wl1 lhs1 rhs1 =
                  (let uu___4 =
                     FStar_Compiler_Effect.op_Less_Bar
                       (FStar_TypeChecker_Env.debug env1)
                       (FStar_Options.Other "Rel") in
                   if uu___4
                   then FStar_Compiler_Util.print_string "imitate\n"
                   else ());
                  (let is_app rhs2 =
                     let uu___4 = FStar_Syntax_Util.head_and_args rhs2 in
                     match uu___4 with
                     | (uu___5, args) ->
                         (match args with | [] -> false | uu___6 -> true) in
                   let is_arrow rhs2 =
                     let uu___4 =
                       let uu___5 = FStar_Syntax_Subst.compress rhs2 in
                       uu___5.FStar_Syntax_Syntax.n in
                     match uu___4 with
                     | FStar_Syntax_Syntax.Tm_arrow uu___5 -> true
                     | uu___5 -> false in
                   let uu___4 = quasi_pattern env1 lhs1 in
                   match uu___4 with
                   | FStar_Pervasives_Native.None ->
                       let msg =
                         mklstr
                           (fun uu___5 ->
                              let uu___6 = prob_to_string env1 orig1 in
                              FStar_Compiler_Util.format1
                                "imitate heuristic cannot solve %s; lhs not a quasi-pattern"
                                uu___6) in
                       giveup_or_defer env1 orig1 wl1
                         FStar_TypeChecker_Common.Deferred_first_order_heuristic_failed
                         msg
                   | FStar_Pervasives_Native.Some (bs_lhs, t_res_lhs) ->
                       let uu___5 = is_app rhs1 in
                       if uu___5
                       then
                         imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                           rhs1
                       else
                         (let uu___7 = is_arrow rhs1 in
                          if uu___7
                          then
                            imitate_arrow orig1 env1 wl1 lhs1 bs_lhs
                              t_res_lhs FStar_TypeChecker_Common.EQ rhs1
                          else
                            (let msg =
                               mklstr
                                 (fun uu___9 ->
                                    let uu___10 = prob_to_string env1 orig1 in
                                    FStar_Compiler_Util.format1
                                      "imitate heuristic cannot solve %s; rhs not an app or arrow"
                                      uu___10) in
                             giveup_or_defer env1 orig1 wl1
                               FStar_TypeChecker_Common.Deferred_first_order_heuristic_failed
                               msg))) in
                let try_first_order orig1 env1 wl1 lhs1 rhs1 =
                  let inapplicable msg lstring_opt =
                    (let uu___4 =
                       FStar_Compiler_Effect.op_Less_Bar
                         (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel") in
                     if uu___4
                     then
                       let extra_msg =
                         match lstring_opt with
                         | FStar_Pervasives_Native.None -> ""
                         | FStar_Pervasives_Native.Some l ->
                             FStar_Thunk.force l in
                       FStar_Compiler_Util.print2
                         "try_first_order failed because: %s\n%s\n" msg
                         extra_msg
                     else ());
                    FStar_Pervasives.Inl "first_order doesn't apply" in
                  (let uu___4 =
                     FStar_Compiler_Effect.op_Less_Bar
                       (FStar_TypeChecker_Env.debug env1)
                       (FStar_Options.Other "Rel") in
                   if uu___4
                   then
                     let uu___5 = flex_t_to_string lhs1 in
                     let uu___6 = FStar_Syntax_Print.term_to_string rhs1 in
                     FStar_Compiler_Util.print2
                       "try_first_order\n\tlhs=%s\n\trhs=%s\n" uu___5 uu___6
                   else ());
                  (let uu___4 = lhs1 in
                   match uu___4 with
                   | Flex (_t1, ctx_uv, args_lhs) ->
                       let n_args_lhs = FStar_Compiler_List.length args_lhs in
                       let uu___5 = FStar_Syntax_Util.head_and_args rhs1 in
                       (match uu___5 with
                        | (head, args_rhs) ->
                            let n_args_rhs =
                              FStar_Compiler_List.length args_rhs in
                            if n_args_lhs > n_args_rhs
                            then
                              inapplicable "not enough args"
                                FStar_Pervasives_Native.None
                            else
                              (let i = n_args_rhs - n_args_lhs in
                               let uu___7 =
                                 FStar_Compiler_List.splitAt i args_rhs in
                               match uu___7 with
                               | (prefix, args_rhs1) ->
                                   let head1 =
                                     FStar_Syntax_Syntax.mk_Tm_app head
                                       prefix head.FStar_Syntax_Syntax.pos in
                                   let uu___8 = occurs_check ctx_uv head1 in
                                   (match uu___8 with
                                    | (uvars_head, occurs_ok, uu___9) ->
                                        if Prims.op_Negation occurs_ok
                                        then
                                          inapplicable "occurs check failed"
                                            FStar_Pervasives_Native.None
                                        else
                                          (let uu___11 =
                                             let uu___12 =
                                               let uu___13 =
                                                 FStar_Syntax_Free.names
                                                   head1 in
                                               let uu___14 =
                                                 binders_as_bv_set
                                                   ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders in
                                               FStar_Compiler_Util.set_is_subset_of
                                                 uu___13 uu___14 in
                                             Prims.op_Negation uu___12 in
                                           if uu___11
                                           then
                                             inapplicable
                                               "free name inclusion failed"
                                               FStar_Pervasives_Native.None
                                           else
                                             (let uu___13 =
                                                env1.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                                  {
                                                    FStar_TypeChecker_Env.solver
                                                      =
                                                      (env1.FStar_TypeChecker_Env.solver);
                                                    FStar_TypeChecker_Env.range
                                                      =
                                                      (env1.FStar_TypeChecker_Env.range);
                                                    FStar_TypeChecker_Env.curmodule
                                                      =
                                                      (env1.FStar_TypeChecker_Env.curmodule);
                                                    FStar_TypeChecker_Env.gamma
                                                      =
                                                      (env1.FStar_TypeChecker_Env.gamma);
                                                    FStar_TypeChecker_Env.gamma_sig
                                                      =
                                                      (env1.FStar_TypeChecker_Env.gamma_sig);
                                                    FStar_TypeChecker_Env.gamma_cache
                                                      =
                                                      (env1.FStar_TypeChecker_Env.gamma_cache);
                                                    FStar_TypeChecker_Env.modules
                                                      =
                                                      (env1.FStar_TypeChecker_Env.modules);
                                                    FStar_TypeChecker_Env.expected_typ
                                                      =
                                                      FStar_Pervasives_Native.None;
                                                    FStar_TypeChecker_Env.sigtab
                                                      =
                                                      (env1.FStar_TypeChecker_Env.sigtab);
                                                    FStar_TypeChecker_Env.attrtab
                                                      =
                                                      (env1.FStar_TypeChecker_Env.attrtab);
                                                    FStar_TypeChecker_Env.instantiate_imp
                                                      =
                                                      (env1.FStar_TypeChecker_Env.instantiate_imp);
                                                    FStar_TypeChecker_Env.effects
                                                      =
                                                      (env1.FStar_TypeChecker_Env.effects);
                                                    FStar_TypeChecker_Env.generalize
                                                      =
                                                      (env1.FStar_TypeChecker_Env.generalize);
                                                    FStar_TypeChecker_Env.letrecs
                                                      =
                                                      (env1.FStar_TypeChecker_Env.letrecs);
                                                    FStar_TypeChecker_Env.top_level
                                                      =
                                                      (env1.FStar_TypeChecker_Env.top_level);
                                                    FStar_TypeChecker_Env.check_uvars
                                                      =
                                                      (env1.FStar_TypeChecker_Env.check_uvars);
                                                    FStar_TypeChecker_Env.use_eq_strict
                                                      =
                                                      (env1.FStar_TypeChecker_Env.use_eq_strict);
                                                    FStar_TypeChecker_Env.is_iface
                                                      =
                                                      (env1.FStar_TypeChecker_Env.is_iface);
                                                    FStar_TypeChecker_Env.admit
                                                      =
                                                      (env1.FStar_TypeChecker_Env.admit);
                                                    FStar_TypeChecker_Env.lax
                                                      = true;
                                                    FStar_TypeChecker_Env.lax_universes
                                                      =
                                                      (env1.FStar_TypeChecker_Env.lax_universes);
                                                    FStar_TypeChecker_Env.phase1
                                                      =
                                                      (env1.FStar_TypeChecker_Env.phase1);
                                                    FStar_TypeChecker_Env.failhard
                                                      =
                                                      (env1.FStar_TypeChecker_Env.failhard);
                                                    FStar_TypeChecker_Env.nosynth
                                                      =
                                                      (env1.FStar_TypeChecker_Env.nosynth);
                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                      =
                                                      (env1.FStar_TypeChecker_Env.uvar_subtyping);
                                                    FStar_TypeChecker_Env.tc_term
                                                      =
                                                      (env1.FStar_TypeChecker_Env.tc_term);
                                                    FStar_TypeChecker_Env.typeof_tot_or_gtot_term
                                                      =
                                                      (env1.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                                                    FStar_TypeChecker_Env.universe_of
                                                      =
                                                      (env1.FStar_TypeChecker_Env.universe_of);
                                                    FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                                      =
                                                      (env1.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                                    FStar_TypeChecker_Env.teq_nosmt_force
                                                      =
                                                      (env1.FStar_TypeChecker_Env.teq_nosmt_force);
                                                    FStar_TypeChecker_Env.subtype_nosmt_force
                                                      =
                                                      (env1.FStar_TypeChecker_Env.subtype_nosmt_force);
                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                      = true;
                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                      =
                                                      (env1.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                      =
                                                      (env1.FStar_TypeChecker_Env.normalized_eff_names);
                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                      =
                                                      (env1.FStar_TypeChecker_Env.fv_delta_depths);
                                                    FStar_TypeChecker_Env.proof_ns
                                                      =
                                                      (env1.FStar_TypeChecker_Env.proof_ns);
                                                    FStar_TypeChecker_Env.synth_hook
                                                      =
                                                      (env1.FStar_TypeChecker_Env.synth_hook);
                                                    FStar_TypeChecker_Env.try_solve_implicits_hook
                                                      =
                                                      (env1.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                    FStar_TypeChecker_Env.splice
                                                      =
                                                      (env1.FStar_TypeChecker_Env.splice);
                                                    FStar_TypeChecker_Env.mpreprocess
                                                      =
                                                      (env1.FStar_TypeChecker_Env.mpreprocess);
                                                    FStar_TypeChecker_Env.postprocess
                                                      =
                                                      (env1.FStar_TypeChecker_Env.postprocess);
                                                    FStar_TypeChecker_Env.identifier_info
                                                      =
                                                      (env1.FStar_TypeChecker_Env.identifier_info);
                                                    FStar_TypeChecker_Env.tc_hooks
                                                      =
                                                      (env1.FStar_TypeChecker_Env.tc_hooks);
                                                    FStar_TypeChecker_Env.dsenv
                                                      =
                                                      (env1.FStar_TypeChecker_Env.dsenv);
                                                    FStar_TypeChecker_Env.nbe
                                                      =
                                                      (env1.FStar_TypeChecker_Env.nbe);
                                                    FStar_TypeChecker_Env.strict_args_tab
                                                      =
                                                      (env1.FStar_TypeChecker_Env.strict_args_tab);
                                                    FStar_TypeChecker_Env.erasable_types_tab
                                                      =
                                                      (env1.FStar_TypeChecker_Env.erasable_types_tab);
                                                    FStar_TypeChecker_Env.enable_defer_to_tac
                                                      =
                                                      (env1.FStar_TypeChecker_Env.enable_defer_to_tac);
                                                    FStar_TypeChecker_Env.unif_allow_ref_guards
                                                      =
                                                      (env1.FStar_TypeChecker_Env.unif_allow_ref_guards);
                                                    FStar_TypeChecker_Env.erase_erasable_args
                                                      =
                                                      (env1.FStar_TypeChecker_Env.erase_erasable_args);
                                                    FStar_TypeChecker_Env.core_check
                                                      =
                                                      (env1.FStar_TypeChecker_Env.core_check)
                                                  } head1 false in
                                              match uu___13 with
                                              | (t_head, uu___14) ->
                                                  let tx =
                                                    FStar_Syntax_Unionfind.new_transaction
                                                      () in
                                                  let solve_sub_probs_if_head_types_equal
                                                    head_uvars_to_restrict
                                                    wl2 =
                                                    let sol =
                                                      [TERM (ctx_uv, head1)] in
                                                    let wl3 =
                                                      restrict_all_uvars env1
                                                        ctx_uv []
                                                        head_uvars_to_restrict
                                                        wl2 in
                                                    let wl4 =
                                                      solve_prob orig1
                                                        FStar_Pervasives_Native.None
                                                        sol wl3 in
                                                    let uu___15 =
                                                      FStar_Compiler_List.fold_left2
                                                        (fun uu___16 ->
                                                           fun uu___17 ->
                                                             fun uu___18 ->
                                                               match 
                                                                 (uu___16,
                                                                   uu___17,
                                                                   uu___18)
                                                               with
                                                               | ((probs,
                                                                   wl5),
                                                                  (arg_lhs,
                                                                   uu___19),
                                                                  (arg_rhs,
                                                                   uu___20))
                                                                   ->
                                                                   let uu___21
                                                                    =
                                                                    mk_t_problem
                                                                    wl5 []
                                                                    orig1
                                                                    arg_lhs
                                                                    FStar_TypeChecker_Common.EQ
                                                                    arg_rhs
                                                                    FStar_Pervasives_Native.None
                                                                    "first-order arg" in
                                                                   (match uu___21
                                                                    with
                                                                    | 
                                                                    (p, wl6)
                                                                    ->
                                                                    ((p ::
                                                                    probs),
                                                                    wl6)))
                                                        ([], wl4) args_lhs
                                                        args_rhs1 in
                                                    match uu___15 with
                                                    | (sub_probs, wl5) ->
                                                        let wl' =
                                                          {
                                                            attempting =
                                                              sub_probs;
                                                            wl_deferred = [];
                                                            wl_deferred_to_tac
                                                              =
                                                              (wl5.wl_deferred_to_tac);
                                                            ctr = (wl5.ctr);
                                                            defer_ok =
                                                              NoDefer;
                                                            smt_ok = false;
                                                            umax_heuristic_ok
                                                              =
                                                              (wl5.umax_heuristic_ok);
                                                            tcenv =
                                                              (wl5.tcenv);
                                                            wl_implicits = [];
                                                            repr_subcomp_allowed
                                                              =
                                                              (wl5.repr_subcomp_allowed)
                                                          } in
                                                        let uu___16 =
                                                          solve env1 wl' in
                                                        (match uu___16 with
                                                         | Success
                                                             (uu___17,
                                                              defer_to_tac,
                                                              imps)
                                                             ->
                                                             let wl6 =
                                                               extend_wl wl5
                                                                 []
                                                                 defer_to_tac
                                                                 imps in
                                                             (FStar_Syntax_Unionfind.commit
                                                                tx;
                                                              FStar_Pervasives.Inr
                                                                wl6)
                                                         | Failed
                                                             (uu___17,
                                                              lstring1)
                                                             ->
                                                             (FStar_Syntax_Unionfind.rollback
                                                                tx;
                                                              inapplicable
                                                                "Subprobs failed: "
                                                                (FStar_Pervasives_Native.Some
                                                                   lstring1))) in
                                                  let uu___15 =
                                                    let uu___16 =
                                                      let uu___17 =
                                                        FStar_Syntax_Util.ctx_uvar_typ
                                                          ctx_uv in
                                                      FStar_Syntax_Util.eq_tm
                                                        t_head uu___17 in
                                                    uu___16 =
                                                      FStar_Syntax_Util.Equal in
                                                  if uu___15
                                                  then
                                                    solve_sub_probs_if_head_types_equal
                                                      uvars_head wl1
                                                  else
                                                    ((let uu___18 =
                                                        FStar_TypeChecker_Env.debug
                                                          env1
                                                          (FStar_Options.Other
                                                             "Rel") in
                                                      if uu___18
                                                      then
                                                        let uu___19 =
                                                          let uu___20 =
                                                            FStar_Syntax_Util.ctx_uvar_typ
                                                              ctx_uv in
                                                          FStar_Syntax_Print.term_to_string
                                                            uu___20 in
                                                        let uu___20 =
                                                          FStar_Syntax_Print.term_to_string
                                                            t_head in
                                                        FStar_Compiler_Util.print2
                                                          "first-order: head type mismatch:\n\tlhs=%s\n\trhs=%s\n"
                                                          uu___19 uu___20
                                                      else ());
                                                     (let typ_equality_prob
                                                        wl2 =
                                                        let uu___18 =
                                                          let uu___19 =
                                                            FStar_Syntax_Util.ctx_uvar_typ
                                                              ctx_uv in
                                                          mk_t_problem wl2 []
                                                            orig1 uu___19
                                                            FStar_TypeChecker_Common.EQ
                                                            t_head
                                                            FStar_Pervasives_Native.None
                                                            "first-order head type" in
                                                        match uu___18 with
                                                        | (p, wl3) ->
                                                            ([p], wl3) in
                                                      let uu___18 =
                                                        try_solve_probs_without_smt
                                                          env1 wl1
                                                          typ_equality_prob in
                                                      match uu___18 with
                                                      | FStar_Pervasives.Inl
                                                          wl2 ->
                                                          let uu___19 =
                                                            let uu___20 =
                                                              FStar_Compiler_Effect.op_Bar_Greater
                                                                head1
                                                                FStar_Syntax_Free.uvars in
                                                            FStar_Compiler_Effect.op_Bar_Greater
                                                              uu___20
                                                              FStar_Compiler_Util.set_elements in
                                                          solve_sub_probs_if_head_types_equal
                                                            uu___19 wl2
                                                      | FStar_Pervasives.Inr
                                                          msg ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           inapplicable
                                                             "first-order: head type mismatch"
                                                             (FStar_Pervasives_Native.Some
                                                                msg)))))))))) in
                match p_rel orig with
                | FStar_TypeChecker_Common.SUB ->
                    if wl.defer_ok = DeferAny
                    then
                      let uu___3 = FStar_Thunk.mkv "flex-rigid subtyping" in
                      giveup_or_defer env orig wl
                        FStar_TypeChecker_Common.Deferred_flex uu___3
                    else
                      solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs
                        rhs
                | FStar_TypeChecker_Common.SUBINV ->
                    if wl.defer_ok = DeferAny
                    then
                      let uu___3 = FStar_Thunk.mkv "flex-rigid subtyping" in
                      giveup_or_defer env orig wl
                        FStar_TypeChecker_Common.Deferred_flex uu___3
                    else
                      solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs
                        rhs
                | FStar_TypeChecker_Common.EQ ->
                    let uu___3 = lhs in
                    (match uu___3 with
                     | Flex (_t1, ctx_uv, args_lhs) ->
                         let uu___4 =
                           pat_vars env
                             ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                             args_lhs in
                         (match uu___4 with
                          | FStar_Pervasives_Native.Some lhs_binders ->
                              ((let uu___6 =
                                  FStar_Compiler_Effect.op_Less_Bar
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "Rel") in
                                if uu___6
                                then
                                  FStar_Compiler_Util.print_string
                                    "it's a pattern\n"
                                else ());
                               (let rhs1 = sn env rhs in
                                let names_to_string1 fvs =
                                  let uu___6 =
                                    let uu___7 =
                                      FStar_Compiler_Util.set_elements fvs in
                                    FStar_Compiler_List.map
                                      FStar_Syntax_Print.bv_to_string uu___7 in
                                  FStar_Compiler_Effect.op_Bar_Greater uu___6
                                    (FStar_String.concat ", ") in
                                let fvs1 =
                                  binders_as_bv_set
                                    (FStar_Compiler_List.op_At
                                       ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                       lhs_binders) in
                                let fvs2 = FStar_Syntax_Free.names rhs1 in
                                let uu___6 = occurs_check ctx_uv rhs1 in
                                match uu___6 with
                                | (uvars, occurs_ok, msg) ->
                                    if Prims.op_Negation occurs_ok
                                    then
                                      let uu___7 =
                                        let uu___8 =
                                          let uu___9 =
                                            FStar_Compiler_Option.get msg in
                                          Prims.op_Hat
                                            "occurs-check failed: " uu___9 in
                                        FStar_Compiler_Effect.op_Less_Bar
                                          FStar_Thunk.mkv uu___8 in
                                      giveup_or_defer env orig wl
                                        FStar_TypeChecker_Common.Deferred_occur_check_failed
                                        uu___7
                                    else
                                      (let uu___8 =
                                         FStar_Compiler_Util.set_is_subset_of
                                           fvs2 fvs1 in
                                       if uu___8
                                       then
                                         let sol =
                                           mk_solution env lhs lhs_binders
                                             rhs1 in
                                         let wl1 =
                                           restrict_all_uvars env ctx_uv
                                             lhs_binders uvars wl in
                                         let uu___9 =
                                           solve_prob orig
                                             FStar_Pervasives_Native.None sol
                                             wl1 in
                                         solve env uu___9
                                       else
                                         if wl.defer_ok = DeferAny
                                         then
                                           (let msg1 =
                                              mklstr
                                                (fun uu___10 ->
                                                   let uu___11 =
                                                     names_to_string1 fvs2 in
                                                   let uu___12 =
                                                     names_to_string1 fvs1 in
                                                   let uu___13 =
                                                     FStar_Syntax_Print.binders_to_string
                                                       ", "
                                                       (FStar_Compiler_List.op_At
                                                          ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                          lhs_binders) in
                                                   FStar_Compiler_Util.format3
                                                     "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                                     uu___11 uu___12 uu___13) in
                                            giveup_or_defer env orig wl
                                              FStar_TypeChecker_Common.Deferred_free_names_check_failed
                                              msg1)
                                         else imitate orig env wl lhs rhs1)))
                          | uu___5 ->
                              if wl.defer_ok = DeferAny
                              then
                                let uu___6 = FStar_Thunk.mkv "Not a pattern" in
                                giveup_or_defer env orig wl
                                  FStar_TypeChecker_Common.Deferred_not_a_pattern
                                  uu___6
                              else
                                (let uu___7 =
                                   try_first_order orig env wl lhs rhs in
                                 match uu___7 with
                                 | FStar_Pervasives.Inr wl1 -> solve env wl1
                                 | uu___8 ->
                                     let uu___9 =
                                       try_quasi_pattern orig env wl lhs rhs in
                                     (match uu___9 with
                                      | (FStar_Pervasives.Inr sol, wl1) ->
                                          let uu___10 =
                                            solve_prob orig
                                              FStar_Pervasives_Native.None
                                              sol wl1 in
                                          solve env uu___10
                                      | (FStar_Pervasives.Inl msg, uu___10)
                                          -> imitate orig env wl lhs rhs))))))
and (solve_t_flex_flex :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> worklist -> flex_t -> flex_t -> solution)
  =
  fun env ->
    fun orig ->
      fun wl ->
        fun lhs ->
          fun rhs ->
            let should_run_meta_arg_tac flex =
              let uv = flex_uvar flex in
              (flex_uvar_has_meta_tac uv) &&
                (let uu___ =
                   let uu___1 = FStar_Syntax_Util.ctx_uvar_typ uv in
                   FStar_Syntax_Free.uvars uu___1 in
                 FStar_Compiler_Util.set_is_empty uu___) in
            let run_meta_arg_tac_and_try_again flex =
              let uv = flex_uvar flex in
              let t = run_meta_arg_tac uv in
              (let uu___1 =
                 FStar_Compiler_Effect.op_Less_Bar
                   (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel") in
               if uu___1
               then
                 let uu___2 = FStar_Syntax_Print.ctx_uvar_to_string uv in
                 let uu___3 = FStar_Syntax_Print.term_to_string t in
                 FStar_Compiler_Util.print2
                   "solve_t_flex_flex: solving meta arg uvar %s with %s\n"
                   uu___2 uu___3
               else ());
              set_uvar env uv t;
              (let uu___2 = attempt [orig] wl in solve env uu___2) in
            match p_rel orig with
            | FStar_TypeChecker_Common.SUB ->
                if wl.defer_ok = DeferAny
                then
                  let uu___ = FStar_Thunk.mkv "flex-flex subtyping" in
                  giveup_or_defer_flex_flex env orig wl
                    FStar_TypeChecker_Common.Deferred_flex uu___
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV ->
                if wl.defer_ok = DeferAny
                then
                  let uu___ = FStar_Thunk.mkv "flex-flex subtyping" in
                  giveup_or_defer_flex_flex env orig wl
                    FStar_TypeChecker_Common.Deferred_flex uu___
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ ->
                let uu___ =
                  (should_defer_flex_to_user_tac env wl lhs) ||
                    (should_defer_flex_to_user_tac env wl rhs) in
                if uu___
                then
                  defer_to_user_tac env orig
                    (Prims.op_Hat (flex_reason lhs)
                       (Prims.op_Hat ", " (flex_reason rhs))) wl
                else
                  if
                    ((wl.defer_ok = DeferAny) ||
                       (wl.defer_ok = DeferFlexFlexOnly))
                      &&
                      ((Prims.op_Negation (is_flex_pat lhs)) ||
                         (Prims.op_Negation (is_flex_pat rhs)))
                  then
                    (let uu___2 = FStar_Thunk.mkv "flex-flex non-pattern" in
                     giveup_or_defer_flex_flex env orig wl
                       FStar_TypeChecker_Common.Deferred_flex_flex_nonpattern
                       uu___2)
                  else
                    (let uu___3 = should_run_meta_arg_tac lhs in
                     if uu___3
                     then run_meta_arg_tac_and_try_again lhs
                     else
                       (let uu___5 = should_run_meta_arg_tac rhs in
                        if uu___5
                        then run_meta_arg_tac_and_try_again rhs
                        else
                          (let uu___7 =
                             let uu___8 = quasi_pattern env lhs in
                             let uu___9 = quasi_pattern env rhs in
                             (uu___8, uu___9) in
                           match uu___7 with
                           | (FStar_Pervasives_Native.Some
                              (binders_lhs, t_res_lhs),
                              FStar_Pervasives_Native.Some
                              (binders_rhs, t_res_rhs)) ->
                               let uu___8 = lhs in
                               (match uu___8 with
                                | Flex
                                    ({ FStar_Syntax_Syntax.n = uu___9;
                                       FStar_Syntax_Syntax.pos = range;
                                       FStar_Syntax_Syntax.vars = uu___10;
                                       FStar_Syntax_Syntax.hash_code =
                                         uu___11;_},
                                     u_lhs, uu___12)
                                    ->
                                    let uu___13 = rhs in
                                    (match uu___13 with
                                     | Flex (uu___14, u_rhs, uu___15) ->
                                         let uu___16 =
                                           (FStar_Syntax_Unionfind.equiv
                                              u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                              u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                             &&
                                             (binders_eq binders_lhs
                                                binders_rhs) in
                                         if uu___16
                                         then
                                           let uu___17 =
                                             solve_prob orig
                                               FStar_Pervasives_Native.None
                                               [] wl in
                                           solve env uu___17
                                         else
                                           (let uu___18 =
                                              maximal_prefix
                                                u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                                u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders in
                                            match uu___18 with
                                            | (ctx_w, (ctx_l, ctx_r)) ->
                                                let gamma_w =
                                                  gamma_until
                                                    u_lhs.FStar_Syntax_Syntax.ctx_uvar_gamma
                                                    ctx_w in
                                                let zs =
                                                  intersect_binders gamma_w
                                                    (FStar_Compiler_List.op_At
                                                       ctx_l binders_lhs)
                                                    (FStar_Compiler_List.op_At
                                                       ctx_r binders_rhs) in
                                                let new_uvar_typ =
                                                  let uu___19 =
                                                    FStar_Syntax_Syntax.mk_Total
                                                      t_res_lhs in
                                                  FStar_Syntax_Util.arrow zs
                                                    uu___19 in
                                                let uu___19 =
                                                  (let uu___20 =
                                                     occurs u_lhs
                                                       new_uvar_typ in
                                                   FStar_Pervasives_Native.snd
                                                     uu___20)
                                                    ||
                                                    ((let uu___20 =
                                                        FStar_Syntax_Unionfind.equiv
                                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_head in
                                                      Prims.op_Negation
                                                        uu___20)
                                                       &&
                                                       (let uu___20 =
                                                          occurs u_rhs
                                                            new_uvar_typ in
                                                        FStar_Pervasives_Native.snd
                                                          uu___20)) in
                                                if uu___19
                                                then
                                                  let uu___20 =
                                                    let uu___21 =
                                                      FStar_Compiler_Util.format1
                                                        "flex-flex: occurs\n defer_ok=%s\n"
                                                        (string_of_defer_ok
                                                           wl.defer_ok) in
                                                    FStar_Thunk.mkv uu___21 in
                                                  giveup_or_defer_flex_flex
                                                    env orig wl
                                                    FStar_TypeChecker_Common.Deferred_flex_flex_nonpattern
                                                    uu___20
                                                else
                                                  ((let uu___22 =
                                                      FStar_Compiler_Effect.op_Less_Bar
                                                        (FStar_TypeChecker_Env.debug
                                                           env)
                                                        (FStar_Options.Other
                                                           "Rel") in
                                                    if uu___22
                                                    then
                                                      let uu___23 =
                                                        FStar_Compiler_Util.stack_dump
                                                          () in
                                                      FStar_Compiler_Util.print1
                                                        "flex-flex quasi: %s\n"
                                                        uu___23
                                                    else ());
                                                   (let uu___22 =
                                                      let uu___23 =
                                                        let uu___24 =
                                                          (let uu___25 =
                                                             FStar_Syntax_Util.ctx_uvar_should_check
                                                               u_lhs in
                                                           FStar_Syntax_Syntax.uu___is_Allow_untyped
                                                             uu___25)
                                                            &&
                                                            (let uu___25 =
                                                               FStar_Syntax_Util.ctx_uvar_should_check
                                                                 u_rhs in
                                                             FStar_Syntax_Syntax.uu___is_Allow_untyped
                                                               uu___25) in
                                                        if uu___24
                                                        then
                                                          FStar_Syntax_Util.ctx_uvar_should_check
                                                            u_lhs
                                                        else
                                                          FStar_Syntax_Syntax.Strict in
                                                      new_uvar
                                                        (Prims.op_Hat
                                                           "flex-flex quasi:"
                                                           (Prims.op_Hat
                                                              "\tlhs="
                                                              (Prims.op_Hat
                                                                 u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                                 (Prims.op_Hat
                                                                    "\trhs="
                                                                    u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                                        wl range gamma_w
                                                        ctx_w new_uvar_typ
                                                        uu___23
                                                        (FStar_Pervasives.Inl
                                                           FStar_Pervasives_Native.None)
                                                        FStar_Pervasives_Native.None in
                                                    match uu___22 with
                                                    | (uu___23, w, wl1) ->
                                                        let w_app =
                                                          let uu___24 =
                                                            FStar_Compiler_List.map
                                                              (fun uu___25 ->
                                                                 match uu___25
                                                                 with
                                                                 | {
                                                                    FStar_Syntax_Syntax.binder_bv
                                                                    = z;
                                                                    FStar_Syntax_Syntax.binder_qual
                                                                    = uu___26;
                                                                    FStar_Syntax_Syntax.binder_attrs
                                                                    = uu___27;_}
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    z in
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    uu___28)
                                                              zs in
                                                          FStar_Syntax_Syntax.mk_Tm_app
                                                            w uu___24
                                                            w.FStar_Syntax_Syntax.pos in
                                                        ((let uu___25 =
                                                            FStar_Compiler_Effect.op_Less_Bar
                                                              (FStar_TypeChecker_Env.debug
                                                                 env)
                                                              (FStar_Options.Other
                                                                 "Rel") in
                                                          if uu___25
                                                          then
                                                            let uu___26 =
                                                              let uu___27 =
                                                                flex_t_to_string
                                                                  lhs in
                                                              let uu___28 =
                                                                let uu___29 =
                                                                  flex_t_to_string
                                                                    rhs in
                                                                let uu___30 =
                                                                  let uu___31
                                                                    =
                                                                    term_to_string
                                                                    w in
                                                                  let uu___32
                                                                    =
                                                                    let uu___33
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    (FStar_Compiler_List.op_At
                                                                    ctx_l
                                                                    binders_lhs) in
                                                                    let uu___34
                                                                    =
                                                                    let uu___35
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    (FStar_Compiler_List.op_At
                                                                    ctx_r
                                                                    binders_rhs) in
                                                                    let uu___36
                                                                    =
                                                                    let uu___37
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ", " zs in
                                                                    [uu___37] in
                                                                    uu___35
                                                                    ::
                                                                    uu___36 in
                                                                    uu___33
                                                                    ::
                                                                    uu___34 in
                                                                  uu___31 ::
                                                                    uu___32 in
                                                                uu___29 ::
                                                                  uu___30 in
                                                              uu___27 ::
                                                                uu___28 in
                                                            FStar_Compiler_Util.print
                                                              "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                              uu___26
                                                          else ());
                                                         (let s1_sol =
                                                            FStar_Syntax_Util.abs
                                                              binders_lhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs)) in
                                                          let s1 =
                                                            TERM
                                                              (u_lhs, s1_sol) in
                                                          let uu___25 =
                                                            FStar_Syntax_Unionfind.equiv
                                                              u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                              u_rhs.FStar_Syntax_Syntax.ctx_uvar_head in
                                                          if uu___25
                                                          then
                                                            let uu___26 =
                                                              solve_prob orig
                                                                FStar_Pervasives_Native.None
                                                                [s1] wl1 in
                                                            solve env uu___26
                                                          else
                                                            (let s2_sol =
                                                               FStar_Syntax_Util.abs
                                                                 binders_rhs
                                                                 w_app
                                                                 (FStar_Pervasives_Native.Some
                                                                    (
                                                                    FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs)) in
                                                             let s2 =
                                                               TERM
                                                                 (u_rhs,
                                                                   s2_sol) in
                                                             let uu___27 =
                                                               solve_prob
                                                                 orig
                                                                 FStar_Pervasives_Native.None
                                                                 [s1; s2] wl1 in
                                                             solve env
                                                               uu___27))))))))
                           | uu___8 ->
                               let uu___9 =
                                 FStar_Thunk.mkv "flex-flex: non-patterns" in
                               giveup_or_defer env orig wl
                                 FStar_TypeChecker_Common.Deferred_flex_flex_nonpattern
                                 uu___9)))
and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env ->
    fun problem ->
      fun wl ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig in
           (let uu___2 =
              FStar_Compiler_Effect.op_Less_Bar
                (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel") in
            if uu___2
            then
              let uu___3 = FStar_Syntax_Print.term_to_string t1 in
              let uu___4 = FStar_Syntax_Print.tag_of_term t1 in
              let uu___5 = FStar_Syntax_Print.term_to_string t2 in
              let uu___6 = FStar_Syntax_Print.tag_of_term t2 in
              FStar_Compiler_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match") uu___3
                uu___4 uu___5 uu___6
            else ());
           (let uu___2 = FStar_Syntax_Util.head_and_args t1 in
            match uu___2 with
            | (head1, args1) ->
                let uu___3 = FStar_Syntax_Util.head_and_args t2 in
                (match uu___3 with
                 | (head2, args2) ->
                     let need_unif1 =
                       match (((head1.FStar_Syntax_Syntax.n), args1),
                               ((head2.FStar_Syntax_Syntax.n), args2))
                       with
                       | ((FStar_Syntax_Syntax.Tm_uinst (uu___4, us1),
                           uu___5::uu___6),
                          (FStar_Syntax_Syntax.Tm_uinst (uu___7, us2),
                           uu___8::uu___9)) ->
                           let uu___10 =
                             (FStar_Compiler_List.for_all
                                (fun u ->
                                   let uu___11 = universe_has_max env1 u in
                                   Prims.op_Negation uu___11) us1)
                               &&
                               (FStar_Compiler_List.for_all
                                  (fun u ->
                                     let uu___11 = universe_has_max env1 u in
                                     Prims.op_Negation uu___11) us2) in
                           if uu___10 then need_unif else true
                       | uu___4 -> need_unif in
                     let solve_head_then wl2 k =
                       if need_unif1
                       then k true wl2
                       else
                         (let uu___5 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2 in
                          match uu___5 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              let uu___6 =
                                defer_lit
                                  FStar_TypeChecker_Common.Deferred_univ_constraint
                                  "universe constraints" orig wl3 in
                              k false uu___6) in
                     let nargs = FStar_Compiler_List.length args1 in
                     if nargs <> (FStar_Compiler_List.length args2)
                     then
                       let uu___4 =
                         mklstr
                           (fun uu___5 ->
                              let uu___6 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu___7 = args_to_string args1 in
                              let uu___8 =
                                FStar_Syntax_Print.term_to_string head2 in
                              let uu___9 = args_to_string args2 in
                              FStar_Compiler_Util.format4
                                "unequal number of arguments: %s[%s] and %s[%s]"
                                uu___6 uu___7 uu___8 uu___9) in
                       giveup env1 uu___4 orig
                     else
                       (let uu___5 =
                          (nargs = Prims.int_zero) ||
                            (let uu___6 =
                               FStar_Syntax_Util.eq_args args1 args2 in
                             uu___6 = FStar_Syntax_Util.Equal) in
                        if uu___5
                        then
                          (if need_unif1
                           then
                             solve_t env1
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (problem.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = head1;
                                 FStar_TypeChecker_Common.relation =
                                   (problem.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = head2;
                                 FStar_TypeChecker_Common.element =
                                   (problem.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (problem.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (problem.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (problem.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (problem.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (problem.FStar_TypeChecker_Common.rank)
                               } wl1
                           else
                             solve_head_then wl1
                               (fun ok ->
                                  fun wl2 ->
                                    if ok
                                    then
                                      let uu___7 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2 in
                                      solve env1 uu___7
                                    else solve env1 wl2))
                        else
                          (let uu___7 = base_and_refinement env1 t1 in
                           match uu___7 with
                           | (base1, refinement1) ->
                               let uu___8 = base_and_refinement env1 t2 in
                               (match uu___8 with
                                | (base2, refinement2) ->
                                    (match (refinement1, refinement2) with
                                     | (FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None) ->
                                         let mk_sub_probs wl2 =
                                           let argp =
                                             if need_unif1
                                             then
                                               FStar_Compiler_List.zip
                                                 ((head1,
                                                    FStar_Pervasives_Native.None)
                                                 :: args1)
                                                 ((head2,
                                                    FStar_Pervasives_Native.None)
                                                 :: args2)
                                             else
                                               FStar_Compiler_List.zip args1
                                                 args2 in
                                           let uu___9 =
                                             FStar_Compiler_List.fold_right
                                               (fun uu___10 ->
                                                  fun uu___11 ->
                                                    match (uu___10, uu___11)
                                                    with
                                                    | (((a1, uu___12),
                                                        (a2, uu___13)),
                                                       (probs, wl3)) ->
                                                        let uu___14 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index" in
                                                        (match uu___14 with
                                                         | (prob', wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2) in
                                           match uu___9 with
                                           | (subprobs, wl3) ->
                                               ((let uu___11 =
                                                   FStar_Compiler_Effect.op_Less_Bar
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel") in
                                                 if uu___11
                                                 then
                                                   let uu___12 =
                                                     FStar_Compiler_Util.string_of_bool
                                                       wl3.smt_ok in
                                                   let uu___13 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs in
                                                   FStar_Compiler_Util.print2
                                                     "Adding subproblems for arguments (smtok=%s): %s"
                                                     uu___12 uu___13
                                                 else ());
                                                (let uu___12 =
                                                   FStar_Options.defensive () in
                                                 if uu___12
                                                 then
                                                   FStar_Compiler_List.iter
                                                     (def_check_prob
                                                        "solve_t' subprobs")
                                                     subprobs
                                                 else ());
                                                (subprobs, wl3)) in
                                         let solve_sub_probs env2 wl2 =
                                           solve_head_then wl2
                                             (fun ok ->
                                                fun wl3 ->
                                                  if Prims.op_Negation ok
                                                  then solve env2 wl3
                                                  else
                                                    (let uu___10 =
                                                       mk_sub_probs wl3 in
                                                     match uu___10 with
                                                     | (subprobs, wl4) ->
                                                         let formula =
                                                           let uu___11 =
                                                             FStar_Compiler_List.map
                                                               (fun p ->
                                                                  p_guard p)
                                                               subprobs in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu___11 in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4 in
                                                         let uu___11 =
                                                           attempt subprobs
                                                             wl5 in
                                                         solve env2 uu___11)) in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok ->
                                                fun wl3 ->
                                                  let uu___10 =
                                                    mk_sub_probs wl3 in
                                                  match uu___10 with
                                                  | (subprobs, wl4) ->
                                                      let formula =
                                                        let uu___11 =
                                                          FStar_Compiler_List.map
                                                            (fun p ->
                                                               p_guard p)
                                                            subprobs in
                                                        FStar_Syntax_Util.mk_conj_l
                                                          uu___11 in
                                                      let wl5 =
                                                        solve_prob orig
                                                          (FStar_Pervasives_Native.Some
                                                             formula) [] wl4 in
                                                      let uu___11 =
                                                        attempt subprobs wl5 in
                                                      solve env2 uu___11) in
                                         let unfold_and_retry d env2 wl2
                                           uu___9 =
                                           match uu___9 with
                                           | (prob, reason) ->
                                               ((let uu___11 =
                                                   FStar_Compiler_Effect.op_Less_Bar
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel") in
                                                 if uu___11
                                                 then
                                                   let uu___12 =
                                                     prob_to_string env2 orig in
                                                   let uu___13 =
                                                     FStar_Thunk.force reason in
                                                   FStar_Compiler_Util.print2
                                                     "Failed to solve %s because a sub-problem is not solvable without SMT because %s"
                                                     uu___12 uu___13
                                                 else ());
                                                (let uu___11 =
                                                   let uu___12 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1 in
                                                   let uu___13 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2 in
                                                   (uu___12, uu___13) in
                                                 match uu___11 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',
                                                    FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu___12 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1' in
                                                     (match uu___12 with
                                                      | (head1', uu___13) ->
                                                          let uu___14 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2' in
                                                          (match uu___14 with
                                                           | (head2',
                                                              uu___15) ->
                                                               let uu___16 =
                                                                 let uu___17
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1 in
                                                                 let uu___18
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2 in
                                                                 (uu___17,
                                                                   uu___18) in
                                                               (match uu___16
                                                                with
                                                                | (FStar_Syntax_Util.Equal,
                                                                   FStar_Syntax_Util.Equal)
                                                                    ->
                                                                    (
                                                                    (
                                                                    let uu___18
                                                                    =
                                                                    FStar_Compiler_Effect.op_Less_Bar
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel") in
                                                                    if
                                                                    uu___18
                                                                    then
                                                                    let uu___19
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1 in
                                                                    let uu___20
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1' in
                                                                    let uu___21
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2 in
                                                                    let uu___22
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2' in
                                                                    FStar_Compiler_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu___19
                                                                    uu___20
                                                                    uu___21
                                                                    uu___22
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu___17 ->
                                                                    let torig'
                                                                    =
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (torig.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (torig.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (torig.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (torig.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (torig.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (torig.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (torig.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (torig.FStar_TypeChecker_Common.rank)
                                                                    } in
                                                                    ((
                                                                    let uu___19
                                                                    =
                                                                    FStar_Compiler_Effect.op_Less_Bar
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel") in
                                                                    if
                                                                    uu___19
                                                                    then
                                                                    let uu___20
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig') in
                                                                    FStar_Compiler_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu___20
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu___12 ->
                                                     solve_sub_probs env2 wl2)) in
                                         let d =
                                           let uu___9 =
                                             delta_depth_of_term env1 head1 in
                                           match uu___9 with
                                           | FStar_Pervasives_Native.None ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d1
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d1 in
                                         let treat_as_injective =
                                           let uu___9 =
                                             let uu___10 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1 in
                                             uu___10.FStar_Syntax_Syntax.n in
                                           match uu___9 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu___10 -> false in
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
                                          | uu___9 ->
                                              solve_sub_probs env1 wl1)
                                     | uu___9 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1) in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2) in
                                         solve_t' env1
                                           {
                                             FStar_TypeChecker_Common.pid =
                                               (problem.FStar_TypeChecker_Common.pid);
                                             FStar_TypeChecker_Common.lhs =
                                               lhs;
                                             FStar_TypeChecker_Common.relation
                                               =
                                               (problem.FStar_TypeChecker_Common.relation);
                                             FStar_TypeChecker_Common.rhs =
                                               rhs;
                                             FStar_TypeChecker_Common.element
                                               =
                                               (problem.FStar_TypeChecker_Common.element);
                                             FStar_TypeChecker_Common.logical_guard
                                               =
                                               (problem.FStar_TypeChecker_Common.logical_guard);
                                             FStar_TypeChecker_Common.logical_guard_uvar
                                               =
                                               (problem.FStar_TypeChecker_Common.logical_guard_uvar);
                                             FStar_TypeChecker_Common.reason
                                               =
                                               (problem.FStar_TypeChecker_Common.reason);
                                             FStar_TypeChecker_Common.loc =
                                               (problem.FStar_TypeChecker_Common.loc);
                                             FStar_TypeChecker_Common.rank =
                                               (problem.FStar_TypeChecker_Common.rank)
                                           } wl1)))))) in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu___1 = destruct_flex_t env1 scrutinee wl1 in
             match uu___1 with
             | (Flex (_t, uv, _args), wl2) ->
                 let uu___2 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true true env1 p in
                 (match uu___2 with
                  | (xs, pat_term, g_pat_as_exp, uu___3) ->
                      let uu___4 =
                        FStar_Compiler_List.fold_left
                          (fun uu___5 ->
                             fun x ->
                               match uu___5 with
                               | (subst, wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst
                                       x.FStar_Syntax_Syntax.sort in
                                   let uu___6 = copy_uvar uv [] t_x wl3 in
                                   (match uu___6 with
                                    | (uu___7, u, wl4) ->
                                        let subst1 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst in
                                        (subst1, wl4))) ([], wl2) xs in
                      (match uu___4 with
                       | (subst, wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst pat_term in
                           let uu___5 =
                             let must_tot = false in
                             let scrutinee_t =
                               let uu___6 =
                                 let uu___7 =
                                   let uu___8 =
                                     env1.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                       env1 scrutinee must_tot in
                                   FStar_Compiler_Effect.op_Bar_Greater
                                     uu___8 FStar_Pervasives_Native.fst in
                                 FStar_Compiler_Effect.op_Bar_Greater uu___7
                                   (FStar_TypeChecker_Normalize.normalize_refinement
                                      FStar_TypeChecker_Normalize.whnf_steps
                                      env1) in
                               FStar_Compiler_Effect.op_Bar_Greater uu___6
                                 FStar_Syntax_Util.unrefine in
                             (let uu___7 =
                                FStar_Compiler_Effect.op_Less_Bar
                                  (FStar_TypeChecker_Env.debug env1)
                                  (FStar_Options.Other "Rel") in
                              if uu___7
                              then
                                let uu___8 =
                                  FStar_Syntax_Print.term_to_string pat_term1 in
                                FStar_Compiler_Util.print1
                                  "Match heuristic, typechecking the pattern term: %s {\n\n"
                                  uu___8
                              else ());
                             (let uu___7 =
                                let uu___8 =
                                  FStar_TypeChecker_Env.set_expected_typ env1
                                    scrutinee_t in
                                env1.FStar_TypeChecker_Env.typeof_tot_or_gtot_term
                                  uu___8 pat_term1 must_tot in
                              match uu___7 with
                              | (pat_term2, pat_term_t, g_pat_term) ->
                                  ((let uu___9 =
                                      FStar_Compiler_Effect.op_Less_Bar
                                        (FStar_TypeChecker_Env.debug env1)
                                        (FStar_Options.Other "Rel") in
                                    if uu___9
                                    then
                                      let uu___10 =
                                        FStar_Syntax_Print.term_to_string
                                          pat_term2 in
                                      let uu___11 =
                                        FStar_Syntax_Print.term_to_string
                                          pat_term_t in
                                      FStar_Compiler_Util.print2
                                        "} Match heuristic, typechecked pattern term to %s and type %s\n"
                                        uu___10 uu___11
                                    else ());
                                   (pat_term2, g_pat_term))) in
                           (match uu___5 with
                            | (pat_term2, g_pat_term) ->
                                let uu___6 =
                                  let uu___7 =
                                    FStar_Compiler_Effect.op_Bar_Greater
                                      g_pat_term (simplify_guard env1) in
                                  FStar_Compiler_Effect.op_Bar_Greater uu___7
                                    FStar_TypeChecker_Env.is_trivial_guard_formula in
                                if uu___6
                                then
                                  let uu___7 =
                                    new_problem wl3 env1 scrutinee
                                      FStar_TypeChecker_Common.EQ pat_term2
                                      FStar_Pervasives_Native.None
                                      scrutinee.FStar_Syntax_Syntax.pos
                                      "match heuristic" in
                                  (match uu___7 with
                                   | (prob, wl4) ->
                                       let wl' =
                                         extend_wl
                                           {
                                             attempting =
                                               [FStar_TypeChecker_Common.TProb
                                                  prob];
                                             wl_deferred = [];
                                             wl_deferred_to_tac =
                                               (wl4.wl_deferred_to_tac);
                                             ctr = (wl4.ctr);
                                             defer_ok = NoDefer;
                                             smt_ok = false;
                                             umax_heuristic_ok =
                                               (wl4.umax_heuristic_ok);
                                             tcenv = (wl4.tcenv);
                                             wl_implicits = [];
                                             repr_subcomp_allowed =
                                               (wl4.repr_subcomp_allowed)
                                           }
                                           g_pat_term.FStar_TypeChecker_Common.deferred
                                           g_pat_term.FStar_TypeChecker_Common.deferred_to_tac
                                           [] in
                                       let tx =
                                         FStar_Syntax_Unionfind.new_transaction
                                           () in
                                       let uu___8 = solve env1 wl' in
                                       (match uu___8 with
                                        | Success
                                            (uu___9, defer_to_tac, imps) ->
                                            let wl'1 =
                                              {
                                                attempting = [orig];
                                                wl_deferred =
                                                  (wl'.wl_deferred);
                                                wl_deferred_to_tac =
                                                  (wl'.wl_deferred_to_tac);
                                                ctr = (wl'.ctr);
                                                defer_ok = (wl'.defer_ok);
                                                smt_ok = (wl'.smt_ok);
                                                umax_heuristic_ok =
                                                  (wl'.umax_heuristic_ok);
                                                tcenv = (wl'.tcenv);
                                                wl_implicits =
                                                  (wl'.wl_implicits);
                                                repr_subcomp_allowed =
                                                  (wl'.repr_subcomp_allowed)
                                              } in
                                            let uu___10 = solve env1 wl'1 in
                                            (match uu___10 with
                                             | Success
                                                 (uu___11, defer_to_tac',
                                                  imps')
                                                 ->
                                                 (FStar_Syntax_Unionfind.commit
                                                    tx;
                                                  (let uu___13 =
                                                     extend_wl wl4 []
                                                       (FStar_Compiler_List.op_At
                                                          defer_to_tac
                                                          defer_to_tac')
                                                       (FStar_Compiler_List.op_At
                                                          imps
                                                          (FStar_Compiler_List.op_At
                                                             imps'
                                                             (FStar_Compiler_List.op_At
                                                                g_pat_as_exp.FStar_TypeChecker_Common.implicits
                                                                g_pat_term.FStar_TypeChecker_Common.implicits))) in
                                                   FStar_Pervasives_Native.Some
                                                     uu___13))
                                             | Failed uu___11 ->
                                                 (FStar_Syntax_Unionfind.rollback
                                                    tx;
                                                  FStar_Pervasives_Native.None))
                                        | uu___9 ->
                                            (FStar_Syntax_Unionfind.rollback
                                               tx;
                                             FStar_Pervasives_Native.None)))
                                else FStar_Pervasives_Native.None))) in
           match t1t2_opt with
           | FStar_Pervasives_Native.None ->
               FStar_Pervasives.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1, t2) ->
               ((let uu___2 =
                   FStar_Compiler_Effect.op_Less_Bar
                     (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel") in
                 if uu___2
                 then
                   let uu___3 = FStar_Syntax_Print.term_to_string t1 in
                   let uu___4 = FStar_Syntax_Print.term_to_string t2 in
                   FStar_Compiler_Util.print2
                     "Trying match heuristic for %s vs. %s\n" uu___3 uu___4
                 else ());
                (let uu___2 =
                   let uu___3 =
                     let uu___4 = FStar_Syntax_Util.unmeta t1 in (s1, uu___4) in
                   let uu___4 =
                     let uu___5 = FStar_Syntax_Util.unmeta t2 in (s2, uu___5) in
                   (uu___3, uu___4) in
                 match uu___2 with
                 | ((uu___3,
                     {
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_match
                         (scrutinee, uu___4, branches, uu___5);
                       FStar_Syntax_Syntax.pos = uu___6;
                       FStar_Syntax_Syntax.vars = uu___7;
                       FStar_Syntax_Syntax.hash_code = uu___8;_}),
                    (s, t)) ->
                     let uu___9 =
                       let uu___10 = is_flex scrutinee in
                       Prims.op_Negation uu___10 in
                     if uu___9
                     then
                       ((let uu___11 =
                           FStar_Compiler_Effect.op_Less_Bar
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel") in
                         if uu___11
                         then
                           let uu___12 =
                             FStar_Syntax_Print.term_to_string scrutinee in
                           FStar_Compiler_Util.print1
                             "match head %s is not a flex term\n" uu___12
                         else ());
                        FStar_Pervasives.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok = DeferAny
                       then
                         ((let uu___12 =
                             FStar_Compiler_Effect.op_Less_Bar
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel") in
                           if uu___12
                           then
                             FStar_Compiler_Util.print_string
                               "Deferring ... \n"
                           else ());
                          FStar_Pervasives.Inl "defer")
                       else
                         ((let uu___13 =
                             FStar_Compiler_Effect.op_Less_Bar
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel") in
                           if uu___13
                           then
                             let uu___14 =
                               FStar_Syntax_Print.term_to_string scrutinee in
                             let uu___15 =
                               FStar_Syntax_Print.term_to_string t in
                             FStar_Compiler_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu___14 uu___15
                           else ());
                          (let pat_discriminates uu___13 =
                             match uu___13 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant uu___14;
                                  FStar_Syntax_Syntax.p = uu___15;_},
                                FStar_Pervasives_Native.None, uu___16) ->
                                 true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu___14;
                                  FStar_Syntax_Syntax.p = uu___15;_},
                                FStar_Pervasives_Native.None, uu___16) ->
                                 true
                             | uu___14 -> false in
                           let head_matching_branch =
                             FStar_Compiler_Effect.op_Bar_Greater branches
                               (FStar_Compiler_Util.try_find
                                  (fun b ->
                                     if pat_discriminates b
                                     then
                                       let uu___13 =
                                         FStar_Syntax_Subst.open_branch b in
                                       match uu___13 with
                                       | (uu___14, uu___15, t') ->
                                           let uu___16 =
                                             head_matches_delta env1
                                               wl1.smt_ok s t' in
                                           (match uu___16 with
                                            | (FullMatch, uu___17) -> true
                                            | (HeadMatch uu___17, uu___18) ->
                                                true
                                            | uu___17 -> false)
                                     else false)) in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None ->
                               ((let uu___14 =
                                   FStar_Compiler_Effect.op_Less_Bar
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu___14
                                 then
                                   FStar_Compiler_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu___14 =
                                     FStar_Compiler_Util.prefix_until
                                       (fun b ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches in
                                   match uu___14 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1, uu___15, uu___16) ->
                                       branches1
                                   | uu___15 -> branches in
                                 let uu___14 =
                                   FStar_Compiler_Util.find_map try_branches
                                     (fun b ->
                                        let uu___15 =
                                          FStar_Syntax_Subst.open_branch b in
                                        match uu___15 with
                                        | (p, uu___16, uu___17) ->
                                            try_solve_branch scrutinee p) in
                                 FStar_Compiler_Effect.op_Less_Bar
                                   (fun uu___15 ->
                                      FStar_Pervasives.Inr uu___15) uu___14))
                           | FStar_Pervasives_Native.Some b ->
                               let uu___13 = FStar_Syntax_Subst.open_branch b in
                               (match uu___13 with
                                | (p, uu___14, e) ->
                                    ((let uu___16 =
                                        FStar_Compiler_Effect.op_Less_Bar
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel") in
                                      if uu___16
                                      then
                                        let uu___17 =
                                          FStar_Syntax_Print.pat_to_string p in
                                        let uu___18 =
                                          FStar_Syntax_Print.term_to_string e in
                                        FStar_Compiler_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu___17 uu___18
                                      else ());
                                     (let uu___16 =
                                        try_solve_branch scrutinee p in
                                      FStar_Compiler_Effect.op_Less_Bar
                                        (fun uu___17 ->
                                           FStar_Pervasives.Inr uu___17)
                                        uu___16)))))
                 | ((s, t),
                    (uu___3,
                     {
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_match
                         (scrutinee, uu___4, branches, uu___5);
                       FStar_Syntax_Syntax.pos = uu___6;
                       FStar_Syntax_Syntax.vars = uu___7;
                       FStar_Syntax_Syntax.hash_code = uu___8;_}))
                     ->
                     let uu___9 =
                       let uu___10 = is_flex scrutinee in
                       Prims.op_Negation uu___10 in
                     if uu___9
                     then
                       ((let uu___11 =
                           FStar_Compiler_Effect.op_Less_Bar
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel") in
                         if uu___11
                         then
                           let uu___12 =
                             FStar_Syntax_Print.term_to_string scrutinee in
                           FStar_Compiler_Util.print1
                             "match head %s is not a flex term\n" uu___12
                         else ());
                        FStar_Pervasives.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok = DeferAny
                       then
                         ((let uu___12 =
                             FStar_Compiler_Effect.op_Less_Bar
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel") in
                           if uu___12
                           then
                             FStar_Compiler_Util.print_string
                               "Deferring ... \n"
                           else ());
                          FStar_Pervasives.Inl "defer")
                       else
                         ((let uu___13 =
                             FStar_Compiler_Effect.op_Less_Bar
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel") in
                           if uu___13
                           then
                             let uu___14 =
                               FStar_Syntax_Print.term_to_string scrutinee in
                             let uu___15 =
                               FStar_Syntax_Print.term_to_string t in
                             FStar_Compiler_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu___14 uu___15
                           else ());
                          (let pat_discriminates uu___13 =
                             match uu___13 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant uu___14;
                                  FStar_Syntax_Syntax.p = uu___15;_},
                                FStar_Pervasives_Native.None, uu___16) ->
                                 true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu___14;
                                  FStar_Syntax_Syntax.p = uu___15;_},
                                FStar_Pervasives_Native.None, uu___16) ->
                                 true
                             | uu___14 -> false in
                           let head_matching_branch =
                             FStar_Compiler_Effect.op_Bar_Greater branches
                               (FStar_Compiler_Util.try_find
                                  (fun b ->
                                     if pat_discriminates b
                                     then
                                       let uu___13 =
                                         FStar_Syntax_Subst.open_branch b in
                                       match uu___13 with
                                       | (uu___14, uu___15, t') ->
                                           let uu___16 =
                                             head_matches_delta env1
                                               wl1.smt_ok s t' in
                                           (match uu___16 with
                                            | (FullMatch, uu___17) -> true
                                            | (HeadMatch uu___17, uu___18) ->
                                                true
                                            | uu___17 -> false)
                                     else false)) in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None ->
                               ((let uu___14 =
                                   FStar_Compiler_Effect.op_Less_Bar
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu___14
                                 then
                                   FStar_Compiler_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu___14 =
                                     FStar_Compiler_Util.prefix_until
                                       (fun b ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches in
                                   match uu___14 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1, uu___15, uu___16) ->
                                       branches1
                                   | uu___15 -> branches in
                                 let uu___14 =
                                   FStar_Compiler_Util.find_map try_branches
                                     (fun b ->
                                        let uu___15 =
                                          FStar_Syntax_Subst.open_branch b in
                                        match uu___15 with
                                        | (p, uu___16, uu___17) ->
                                            try_solve_branch scrutinee p) in
                                 FStar_Compiler_Effect.op_Less_Bar
                                   (fun uu___15 ->
                                      FStar_Pervasives.Inr uu___15) uu___14))
                           | FStar_Pervasives_Native.Some b ->
                               let uu___13 = FStar_Syntax_Subst.open_branch b in
                               (match uu___13 with
                                | (p, uu___14, e) ->
                                    ((let uu___16 =
                                        FStar_Compiler_Effect.op_Less_Bar
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel") in
                                      if uu___16
                                      then
                                        let uu___17 =
                                          FStar_Syntax_Print.pat_to_string p in
                                        let uu___18 =
                                          FStar_Syntax_Print.term_to_string e in
                                        FStar_Compiler_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu___17 uu___18
                                      else ());
                                     (let uu___16 =
                                        try_solve_branch scrutinee p in
                                      FStar_Compiler_Effect.op_Less_Bar
                                        (fun uu___17 ->
                                           FStar_Pervasives.Inr uu___17)
                                        uu___16)))))
                 | uu___3 ->
                     ((let uu___5 =
                         FStar_Compiler_Effect.op_Less_Bar
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel") in
                       if uu___5
                       then
                         let uu___6 = FStar_Syntax_Print.tag_of_term t1 in
                         let uu___7 = FStar_Syntax_Print.tag_of_term t2 in
                         FStar_Compiler_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu___6 uu___7
                       else ());
                      FStar_Pervasives.Inr FStar_Pervasives_Native.None))) in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig in
           (let uu___2 =
              FStar_Compiler_Effect.op_Less_Bar
                (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta") in
            if uu___2
            then
              let uu___3 = FStar_Syntax_Print.tag_of_term t1 in
              let uu___4 = FStar_Syntax_Print.tag_of_term t2 in
              let uu___5 = FStar_Syntax_Print.term_to_string t1 in
              let uu___6 = FStar_Syntax_Print.term_to_string t2 in
              FStar_Compiler_Util.print4
                "rigid_rigid_delta of %s-%s (%s, %s)\n" uu___3 uu___4 uu___5
                uu___6
            else ());
           (let uu___2 = head_matches_delta env1 wl1.smt_ok t1 t2 in
            match uu___2 with
            | (m, o) ->
                (match (m, o) with
                 | (MisMatch uu___3, uu___4) ->
                     let try_reveal_hide env2 t11 t21 =
                       let payload_of_hide_reveal h args =
                         match ((h.FStar_Syntax_Syntax.n), args) with
                         | (FStar_Syntax_Syntax.Tm_uinst (uu___5, u::[]),
                            (ty, FStar_Pervasives_Native.Some
                             { FStar_Syntax_Syntax.aqual_implicit = true;
                               FStar_Syntax_Syntax.aqual_attributes = uu___6;_})::
                            (t, uu___7)::[]) when is_flex t ->
                             FStar_Pervasives_Native.Some (u, ty, t)
                         | uu___5 -> FStar_Pervasives_Native.None in
                       let is_reveal_or_hide t =
                         let uu___5 = FStar_Syntax_Util.head_and_args t in
                         match uu___5 with
                         | (h, args) ->
                             let uu___6 =
                               FStar_Syntax_Util.is_fvar
                                 FStar_Parser_Const.reveal h in
                             if uu___6
                             then
                               (match payload_of_hide_reveal h args with
                                | FStar_Pervasives_Native.None ->
                                    FStar_Pervasives_Native.None
                                | FStar_Pervasives_Native.Some t3 ->
                                    FStar_Pervasives_Native.Some
                                      (FStar_Pervasives.Inl t3))
                             else
                               (let uu___8 =
                                  FStar_Syntax_Util.is_fvar
                                    FStar_Parser_Const.hide h in
                                if uu___8
                                then
                                  match payload_of_hide_reveal h args with
                                  | FStar_Pervasives_Native.None ->
                                      FStar_Pervasives_Native.None
                                  | FStar_Pervasives_Native.Some t3 ->
                                      FStar_Pervasives_Native.Some
                                        (FStar_Pervasives.Inr t3)
                                else FStar_Pervasives_Native.None) in
                       let mk_fv_app lid u args r =
                         let fv =
                           FStar_TypeChecker_Env.fvar_of_nonqual_lid env2 lid in
                         let head = FStar_Syntax_Syntax.mk_Tm_uinst fv [u] in
                         FStar_Syntax_Syntax.mk_Tm_app head args r in
                       let uu___5 =
                         let uu___6 = is_reveal_or_hide t11 in
                         let uu___7 = is_reveal_or_hide t21 in
                         (uu___6, uu___7) in
                       match uu___5 with
                       | (FStar_Pervasives_Native.None,
                          FStar_Pervasives_Native.None) ->
                           FStar_Pervasives_Native.None
                       | (FStar_Pervasives_Native.Some (FStar_Pervasives.Inl
                          uu___6), FStar_Pervasives_Native.Some
                          (FStar_Pervasives.Inl uu___7)) ->
                           FStar_Pervasives_Native.None
                       | (FStar_Pervasives_Native.Some (FStar_Pervasives.Inr
                          uu___6), FStar_Pervasives_Native.Some
                          (FStar_Pervasives.Inr uu___7)) ->
                           FStar_Pervasives_Native.None
                       | (FStar_Pervasives_Native.Some (FStar_Pervasives.Inl
                          uu___6), FStar_Pervasives_Native.Some
                          (FStar_Pervasives.Inr uu___7)) ->
                           FStar_Pervasives_Native.None
                       | (FStar_Pervasives_Native.Some (FStar_Pervasives.Inr
                          uu___6), FStar_Pervasives_Native.Some
                          (FStar_Pervasives.Inl uu___7)) ->
                           FStar_Pervasives_Native.None
                       | (FStar_Pervasives_Native.Some (FStar_Pervasives.Inl
                          (u, ty, lhs)), FStar_Pervasives_Native.None) ->
                           let rhs =
                             let uu___6 =
                               let uu___7 =
                                 let uu___8 =
                                   FStar_Syntax_Syntax.as_aqual_implicit true in
                                 (ty, uu___8) in
                               [uu___7; (t21, FStar_Pervasives_Native.None)] in
                             mk_fv_app FStar_Parser_Const.hide u uu___6
                               t21.FStar_Syntax_Syntax.pos in
                           FStar_Pervasives_Native.Some (lhs, rhs)
                       | (FStar_Pervasives_Native.None,
                          FStar_Pervasives_Native.Some (FStar_Pervasives.Inl
                          (u, ty, rhs))) ->
                           let lhs =
                             let uu___6 =
                               let uu___7 =
                                 let uu___8 =
                                   FStar_Syntax_Syntax.as_aqual_implicit true in
                                 (ty, uu___8) in
                               [uu___7; (t11, FStar_Pervasives_Native.None)] in
                             mk_fv_app FStar_Parser_Const.hide u uu___6
                               t11.FStar_Syntax_Syntax.pos in
                           FStar_Pervasives_Native.Some (lhs, rhs)
                       | (FStar_Pervasives_Native.Some (FStar_Pervasives.Inr
                          (u, ty, lhs)), FStar_Pervasives_Native.None) ->
                           let rhs =
                             let uu___6 =
                               let uu___7 =
                                 let uu___8 =
                                   FStar_Syntax_Syntax.as_aqual_implicit true in
                                 (ty, uu___8) in
                               [uu___7; (t21, FStar_Pervasives_Native.None)] in
                             mk_fv_app FStar_Parser_Const.reveal u uu___6
                               t21.FStar_Syntax_Syntax.pos in
                           FStar_Pervasives_Native.Some (lhs, rhs)
                       | (FStar_Pervasives_Native.None,
                          FStar_Pervasives_Native.Some (FStar_Pervasives.Inr
                          (u, ty, rhs))) ->
                           let lhs =
                             let uu___6 =
                               let uu___7 =
                                 let uu___8 =
                                   FStar_Syntax_Syntax.as_aqual_implicit true in
                                 (ty, uu___8) in
                               [uu___7; (t11, FStar_Pervasives_Native.None)] in
                             mk_fv_app FStar_Parser_Const.reveal u uu___6
                               t11.FStar_Syntax_Syntax.pos in
                           FStar_Pervasives_Native.Some (lhs, rhs) in
                     let uu___5 = try_match_heuristic env1 orig wl1 t1 t2 o in
                     (match uu___5 with
                      | FStar_Pervasives.Inl _defer_ok ->
                          let uu___6 =
                            FStar_Thunk.mkv "delaying match heuristic" in
                          giveup_or_defer1 orig
                            FStar_TypeChecker_Common.Deferred_delay_match_heuristic
                            uu___6
                      | FStar_Pervasives.Inr (FStar_Pervasives_Native.Some
                          wl2) -> solve env1 wl2
                      | FStar_Pervasives.Inr (FStar_Pervasives_Native.None)
                          ->
                          let uu___6 = try_reveal_hide env1 t1 t2 in
                          (match uu___6 with
                           | FStar_Pervasives_Native.Some (t1', t2') ->
                               solve_t env1
                                 {
                                   FStar_TypeChecker_Common.pid =
                                     (problem.FStar_TypeChecker_Common.pid);
                                   FStar_TypeChecker_Common.lhs = t1';
                                   FStar_TypeChecker_Common.relation =
                                     (problem.FStar_TypeChecker_Common.relation);
                                   FStar_TypeChecker_Common.rhs = t2';
                                   FStar_TypeChecker_Common.element =
                                     (problem.FStar_TypeChecker_Common.element);
                                   FStar_TypeChecker_Common.logical_guard =
                                     (problem.FStar_TypeChecker_Common.logical_guard);
                                   FStar_TypeChecker_Common.logical_guard_uvar
                                     =
                                     (problem.FStar_TypeChecker_Common.logical_guard_uvar);
                                   FStar_TypeChecker_Common.reason =
                                     (problem.FStar_TypeChecker_Common.reason);
                                   FStar_TypeChecker_Common.loc =
                                     (problem.FStar_TypeChecker_Common.loc);
                                   FStar_TypeChecker_Common.rank =
                                     (problem.FStar_TypeChecker_Common.rank)
                                 } wl1
                           | FStar_Pervasives_Native.None ->
                               let uu___7 =
                                 ((may_relate env1
                                     problem.FStar_TypeChecker_Common.relation
                                     head1)
                                    ||
                                    (may_relate env1
                                       problem.FStar_TypeChecker_Common.relation
                                       head2))
                                   && wl1.smt_ok in
                               if uu___7
                               then
                                 let uu___8 =
                                   guard_of_prob env1 wl1 problem t1 t2 in
                                 (match uu___8 with
                                  | (guard, wl2) ->
                                      let uu___9 =
                                        solve_prob orig
                                          (FStar_Pervasives_Native.Some guard)
                                          [] wl2 in
                                      solve env1 uu___9)
                               else
                                 (let uu___9 =
                                    mklstr
                                      (fun uu___10 ->
                                         let uu___11 =
                                           FStar_Syntax_Print.term_to_string
                                             head1 in
                                         let uu___12 =
                                           let uu___13 =
                                             let uu___14 =
                                               delta_depth_of_term env1 head1 in
                                             FStar_Compiler_Util.bind_opt
                                               uu___14
                                               (fun x ->
                                                  let uu___15 =
                                                    FStar_Syntax_Print.delta_depth_to_string
                                                      x in
                                                  FStar_Pervasives_Native.Some
                                                    uu___15) in
                                           FStar_Compiler_Util.dflt ""
                                             uu___13 in
                                         let uu___13 =
                                           FStar_Syntax_Print.term_to_string
                                             head2 in
                                         let uu___14 =
                                           let uu___15 =
                                             let uu___16 =
                                               delta_depth_of_term env1 head2 in
                                             FStar_Compiler_Util.bind_opt
                                               uu___16
                                               (fun x ->
                                                  let uu___17 =
                                                    FStar_Syntax_Print.delta_depth_to_string
                                                      x in
                                                  FStar_Pervasives_Native.Some
                                                    uu___17) in
                                           FStar_Compiler_Util.dflt ""
                                             uu___15 in
                                         FStar_Compiler_Util.format4
                                           "head mismatch (%s (%s) vs %s (%s))"
                                           uu___11 uu___12 uu___13 uu___14) in
                                  giveup env1 uu___9 orig)))
                 | (HeadMatch (true), uu___3) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu___4 = guard_of_prob env1 wl1 problem t1 t2 in
                       (match uu___4 with
                        | (guard, wl2) ->
                            let uu___5 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2 in
                            solve env1 uu___5)
                     else
                       (let uu___5 =
                          mklstr
                            (fun uu___6 ->
                               let uu___7 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu___8 =
                                 FStar_Syntax_Print.term_to_string t2 in
                               FStar_Compiler_Util.format2
                                 "head mismatch for subtyping (%s vs %s)"
                                 uu___7 uu___8) in
                        giveup env1 uu___5 orig)
                 | (uu___3, FStar_Pervasives_Native.Some (t11, t21)) ->
                     solve_t env1
                       {
                         FStar_TypeChecker_Common.pid =
                           (problem.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = t11;
                         FStar_TypeChecker_Common.relation =
                           (problem.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = t21;
                         FStar_TypeChecker_Common.element =
                           (problem.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (problem.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (problem.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (problem.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (problem.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (problem.FStar_TypeChecker_Common.rank)
                       } wl1
                 | (HeadMatch need_unif, FStar_Pervasives_Native.None) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch, FStar_Pervasives_Native.None) ->
                     rigid_heads_match env1 false torig wl1 t1 t2)) in
         let orig = FStar_TypeChecker_Common.TProb problem in
         def_check_prob "solve_t'.2" orig;
         (let uu___2 =
            FStar_Compiler_Util.physical_equality
              problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs in
          if uu___2
          then
            let uu___3 = solve_prob orig FStar_Pervasives_Native.None [] wl in
            solve env uu___3
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs in
             let t2 = problem.FStar_TypeChecker_Common.rhs in
             (let uu___5 =
                let uu___6 = p_scope orig in
                FStar_Compiler_List.map
                  (fun b -> b.FStar_Syntax_Syntax.binder_bv) uu___6 in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu___5 t1);
             (let uu___6 =
                let uu___7 = p_scope orig in
                FStar_Compiler_List.map
                  (fun b -> b.FStar_Syntax_Syntax.binder_bv) uu___7 in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu___6 t2);
             (let uu___7 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel") in
              if uu___7
              then
                let uu___8 =
                  FStar_Compiler_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid in
                let uu___9 =
                  let uu___10 = FStar_Syntax_Print.tag_of_term t1 in
                  let uu___11 =
                    let uu___12 = FStar_Syntax_Print.term_to_string t1 in
                    Prims.op_Hat "::" uu___12 in
                  Prims.op_Hat uu___10 uu___11 in
                let uu___10 =
                  let uu___11 = FStar_Syntax_Print.tag_of_term t2 in
                  let uu___12 =
                    let uu___13 = FStar_Syntax_Print.term_to_string t2 in
                    Prims.op_Hat "::" uu___13 in
                  Prims.op_Hat uu___11 uu___12 in
                FStar_Compiler_Util.print4
                  "Attempting %s (%s vs %s); rel = (%s)\n" uu___8 uu___9
                  uu___10
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu___7, uu___8) ->
                  failwith "Impossible: terms were not compressed"
              | (uu___7, FStar_Syntax_Syntax.Tm_delayed uu___8) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu___7, uu___8) ->
                  let uu___9 =
                    let uu___10 = FStar_Syntax_Util.unascribe t1 in
                    {
                      FStar_TypeChecker_Common.pid =
                        (problem.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu___10;
                      FStar_TypeChecker_Common.relation =
                        (problem.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (problem.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (problem.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (problem.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (problem.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (problem.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (problem.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (problem.FStar_TypeChecker_Common.rank)
                    } in
                  solve_t' env uu___9 wl
              | (FStar_Syntax_Syntax.Tm_meta uu___7, uu___8) ->
                  let uu___9 =
                    let uu___10 = FStar_Syntax_Util.unmeta t1 in
                    {
                      FStar_TypeChecker_Common.pid =
                        (problem.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu___10;
                      FStar_TypeChecker_Common.relation =
                        (problem.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (problem.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (problem.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (problem.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (problem.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (problem.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (problem.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (problem.FStar_TypeChecker_Common.rank)
                    } in
                  solve_t' env uu___9 wl
              | (uu___7, FStar_Syntax_Syntax.Tm_ascribed uu___8) ->
                  let uu___9 =
                    let uu___10 = FStar_Syntax_Util.unascribe t2 in
                    {
                      FStar_TypeChecker_Common.pid =
                        (problem.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (problem.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (problem.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu___10;
                      FStar_TypeChecker_Common.element =
                        (problem.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (problem.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (problem.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (problem.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (problem.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (problem.FStar_TypeChecker_Common.rank)
                    } in
                  solve_t' env uu___9 wl
              | (uu___7, FStar_Syntax_Syntax.Tm_meta uu___8) ->
                  let uu___9 =
                    let uu___10 = FStar_Syntax_Util.unmeta t2 in
                    {
                      FStar_TypeChecker_Common.pid =
                        (problem.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (problem.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (problem.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu___10;
                      FStar_TypeChecker_Common.element =
                        (problem.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (problem.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (problem.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (problem.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (problem.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (problem.FStar_TypeChecker_Common.rank)
                    } in
                  solve_t' env uu___9 wl
              | (FStar_Syntax_Syntax.Tm_quoted (t11, uu___7),
                 FStar_Syntax_Syntax.Tm_quoted (t21, uu___8)) ->
                  let uu___9 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl in
                  solve env uu___9
              | (FStar_Syntax_Syntax.Tm_bvar uu___7, uu___8) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu___7, FStar_Syntax_Syntax.Tm_bvar uu___8) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1, FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow (bs1, c1),
                 FStar_Syntax_Syntax.Tm_arrow (bs2, c2)) ->
                  let mk_c c uu___7 =
                    match uu___7 with
                    | [] -> c
                    | bs ->
                        let uu___8 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            c.FStar_Syntax_Syntax.pos in
                        FStar_Syntax_Syntax.mk_Total uu___8 in
                  let uu___7 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                  (match uu___7 with
                   | ((bs11, c11), (bs21, c21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1 ->
                            fun scope ->
                              fun env1 ->
                                fun subst ->
                                  let c12 =
                                    FStar_Syntax_Subst.subst_comp subst c11 in
                                  let c22 =
                                    FStar_Syntax_Subst.subst_comp subst c21 in
                                  let rel =
                                    let uu___8 =
                                      FStar_Options.use_eq_at_higher_order () in
                                    if uu___8
                                    then FStar_TypeChecker_Common.EQ
                                    else
                                      problem.FStar_TypeChecker_Common.relation in
                                  mk_c_problem wl1 scope orig c12 rel c22
                                    FStar_Pervasives_Native.None
                                    "function co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, lopt1),
                 FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, lopt2)) ->
                  let mk_t t l uu___7 =
                    match uu___7 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          t.FStar_Syntax_Syntax.pos in
                  let uu___7 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2)) in
                  (match uu___7 with
                   | ((bs11, tbody11), (bs21, tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1 ->
                            fun scope ->
                              fun env1 ->
                                fun subst ->
                                  let uu___8 =
                                    FStar_Syntax_Subst.subst subst tbody11 in
                                  let uu___9 =
                                    FStar_Syntax_Subst.subst subst tbody21 in
                                  mk_t_problem wl1 scope orig uu___8
                                    problem.FStar_TypeChecker_Common.relation
                                    uu___9 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_refine (x1, phi1),
                 FStar_Syntax_Syntax.Tm_refine (x2, phi2)) ->
                  let uu___7 =
                    let uu___8 =
                      head_matches_delta env wl.smt_ok
                        x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort in
                    match uu___8 with
                    | (FullMatch, FStar_Pervasives_Native.Some (t11, t21)) ->
                        ({
                           FStar_Syntax_Syntax.ppname =
                             (x1.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (x1.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = t11
                         },
                          {
                            FStar_Syntax_Syntax.ppname =
                              (x2.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (x2.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t21
                          })
                    | (HeadMatch uu___9, FStar_Pervasives_Native.Some
                       (t11, t21)) ->
                        ({
                           FStar_Syntax_Syntax.ppname =
                             (x1.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (x1.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = t11
                         },
                          {
                            FStar_Syntax_Syntax.ppname =
                              (x2.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (x2.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t21
                          })
                    | uu___9 -> (x1, x2) in
                  (match uu___7 with
                   | (x11, x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1 in
                       let t21 = FStar_Syntax_Util.refine x21 phi2 in
                       let uu___8 = as_refinement false env t11 in
                       (match uu___8 with
                        | (x12, phi11) ->
                            let uu___9 = as_refinement false env t21 in
                            (match uu___9 with
                             | (x22, phi21) ->
                                 ((let uu___11 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel") in
                                   if uu___11
                                   then
                                     ((let uu___13 =
                                         FStar_Syntax_Print.bv_to_string x12 in
                                       let uu___14 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort in
                                       let uu___15 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11 in
                                       FStar_Compiler_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu___13
                                         uu___14 uu___15);
                                      (let uu___13 =
                                         FStar_Syntax_Print.bv_to_string x22 in
                                       let uu___14 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort in
                                       let uu___15 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21 in
                                       FStar_Compiler_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu___13
                                         uu___14 uu___15))
                                   else ());
                                  (let uu___11 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type" in
                                   match uu___11 with
                                   | (base_prob, wl1) ->
                                       let x13 =
                                         FStar_Syntax_Syntax.freshen_bv x12 in
                                       let subst =
                                         [FStar_Syntax_Syntax.DB
                                            (Prims.int_zero, x13)] in
                                       let phi12 =
                                         FStar_Syntax_Subst.subst subst phi11 in
                                       let phi22 =
                                         FStar_Syntax_Subst.subst subst phi21 in
                                       let env1 =
                                         FStar_TypeChecker_Env.push_bv env
                                           x13 in
                                       let mk_imp imp phi13 phi23 =
                                         let uu___12 = imp phi13 phi23 in
                                         FStar_Compiler_Effect.op_Bar_Greater
                                           uu___12
                                           (guard_on_element wl1 problem x13) in
                                       let fallback uu___12 =
                                         let impl =
                                           if
                                             problem.FStar_TypeChecker_Common.relation
                                               = FStar_TypeChecker_Common.EQ
                                           then
                                             mk_imp FStar_Syntax_Util.mk_iff
                                               phi12 phi22
                                           else
                                             mk_imp FStar_Syntax_Util.mk_imp
                                               phi12 phi22 in
                                         let guard =
                                           FStar_Syntax_Util.mk_conj
                                             (p_guard base_prob) impl in
                                         (let uu___14 =
                                            let uu___15 = p_scope orig in
                                            FStar_Compiler_List.map
                                              (fun b ->
                                                 b.FStar_Syntax_Syntax.binder_bv)
                                              uu___15 in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu___14
                                            (p_guard base_prob));
                                         (let uu___15 =
                                            let uu___16 = p_scope orig in
                                            FStar_Compiler_List.map
                                              (fun b ->
                                                 b.FStar_Syntax_Syntax.binder_bv)
                                              uu___16 in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu___15 impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1 in
                                          let uu___15 =
                                            attempt [base_prob] wl2 in
                                          solve env1 uu___15) in
                                       let has_uvars =
                                         (let uu___12 =
                                            let uu___13 =
                                              FStar_Syntax_Free.uvars phi12 in
                                            FStar_Compiler_Util.set_is_empty
                                              uu___13 in
                                          Prims.op_Negation uu___12) ||
                                           (let uu___12 =
                                              let uu___13 =
                                                FStar_Syntax_Free.uvars phi22 in
                                              FStar_Compiler_Util.set_is_empty
                                                uu___13 in
                                            Prims.op_Negation uu___12) in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu___12 =
                                           let uu___13 =
                                             let uu___14 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13 in
                                             [uu___14] in
                                           mk_t_problem wl1 uu___13 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula" in
                                         (match uu___12 with
                                          | (ref_prob, wl2) ->
                                              let tx =
                                                FStar_Syntax_Unionfind.new_transaction
                                                  () in
                                              let uu___13 =
                                                solve env1
                                                  {
                                                    attempting = [ref_prob];
                                                    wl_deferred = [];
                                                    wl_deferred_to_tac =
                                                      (wl2.wl_deferred_to_tac);
                                                    ctr = (wl2.ctr);
                                                    defer_ok = NoDefer;
                                                    smt_ok = (wl2.smt_ok);
                                                    umax_heuristic_ok =
                                                      (wl2.umax_heuristic_ok);
                                                    tcenv = (wl2.tcenv);
                                                    wl_implicits = [];
                                                    repr_subcomp_allowed =
                                                      (wl2.repr_subcomp_allowed)
                                                  } in
                                              (match uu___13 with
                                               | Failed (prob, msg) ->
                                                   (FStar_Syntax_Unionfind.rollback
                                                      tx;
                                                    if
                                                      (((Prims.op_Negation
                                                           env1.FStar_TypeChecker_Env.uvar_subtyping)
                                                          && has_uvars)
                                                         ||
                                                         (Prims.op_Negation
                                                            wl2.smt_ok))
                                                        &&
                                                        (Prims.op_Negation
                                                           env1.FStar_TypeChecker_Env.unif_allow_ref_guards)
                                                    then giveup env1 msg prob
                                                    else fallback ())
                                               | Success
                                                   (uu___14, defer_to_tac,
                                                    imps)
                                                   ->
                                                   (FStar_Syntax_Unionfind.commit
                                                      tx;
                                                    (let guard =
                                                       let uu___16 =
                                                         FStar_Compiler_Effect.op_Bar_Greater
                                                           (p_guard ref_prob)
                                                           (guard_on_element
                                                              wl2 problem x13) in
                                                       FStar_Syntax_Util.mk_conj
                                                         (p_guard base_prob)
                                                         uu___16 in
                                                     let wl3 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            guard) [] wl2 in
                                                     let wl4 =
                                                       {
                                                         attempting =
                                                           (wl3.attempting);
                                                         wl_deferred =
                                                           (wl3.wl_deferred);
                                                         wl_deferred_to_tac =
                                                           (wl3.wl_deferred_to_tac);
                                                         ctr =
                                                           (wl3.ctr +
                                                              Prims.int_one);
                                                         defer_ok =
                                                           (wl3.defer_ok);
                                                         smt_ok =
                                                           (wl3.smt_ok);
                                                         umax_heuristic_ok =
                                                           (wl3.umax_heuristic_ok);
                                                         tcenv = (wl3.tcenv);
                                                         wl_implicits =
                                                           (wl3.wl_implicits);
                                                         repr_subcomp_allowed
                                                           =
                                                           (wl3.repr_subcomp_allowed)
                                                       } in
                                                     let wl5 =
                                                       extend_wl wl4 []
                                                         defer_to_tac imps in
                                                     let uu___16 =
                                                       attempt [base_prob]
                                                         wl5 in
                                                     solve env1 uu___16))))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar uu___7,
                 FStar_Syntax_Syntax.Tm_uvar uu___8) ->
                  let uu___9 = ensure_no_uvar_subst env t1 wl in
                  (match uu___9 with
                   | (t11, wl1) ->
                       let t21 = FStar_Syntax_Util.canon_app t2 in
                       let uu___10 = ensure_no_uvar_subst env t21 wl1 in
                       (match uu___10 with
                        | (t22, wl2) ->
                            let f1 = destruct_flex_t' t11 in
                            let f2 = destruct_flex_t' t22 in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu___7;
                    FStar_Syntax_Syntax.pos = uu___8;
                    FStar_Syntax_Syntax.vars = uu___9;
                    FStar_Syntax_Syntax.hash_code = uu___10;_},
                  uu___11),
                 FStar_Syntax_Syntax.Tm_uvar uu___12) ->
                  let uu___13 = ensure_no_uvar_subst env t1 wl in
                  (match uu___13 with
                   | (t11, wl1) ->
                       let t21 = FStar_Syntax_Util.canon_app t2 in
                       let uu___14 = ensure_no_uvar_subst env t21 wl1 in
                       (match uu___14 with
                        | (t22, wl2) ->
                            let f1 = destruct_flex_t' t11 in
                            let f2 = destruct_flex_t' t22 in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu___7,
                 FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu___8;
                    FStar_Syntax_Syntax.pos = uu___9;
                    FStar_Syntax_Syntax.vars = uu___10;
                    FStar_Syntax_Syntax.hash_code = uu___11;_},
                  uu___12)) ->
                  let uu___13 = ensure_no_uvar_subst env t1 wl in
                  (match uu___13 with
                   | (t11, wl1) ->
                       let t21 = FStar_Syntax_Util.canon_app t2 in
                       let uu___14 = ensure_no_uvar_subst env t21 wl1 in
                       (match uu___14 with
                        | (t22, wl2) ->
                            let f1 = destruct_flex_t' t11 in
                            let f2 = destruct_flex_t' t22 in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu___7;
                    FStar_Syntax_Syntax.pos = uu___8;
                    FStar_Syntax_Syntax.vars = uu___9;
                    FStar_Syntax_Syntax.hash_code = uu___10;_},
                  uu___11),
                 FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu___12;
                    FStar_Syntax_Syntax.pos = uu___13;
                    FStar_Syntax_Syntax.vars = uu___14;
                    FStar_Syntax_Syntax.hash_code = uu___15;_},
                  uu___16)) ->
                  let uu___17 = ensure_no_uvar_subst env t1 wl in
                  (match uu___17 with
                   | (t11, wl1) ->
                       let t21 = FStar_Syntax_Util.canon_app t2 in
                       let uu___18 = ensure_no_uvar_subst env t21 wl1 in
                       (match uu___18 with
                        | (t22, wl2) ->
                            let f1 = destruct_flex_t' t11 in
                            let f2 = destruct_flex_t' t22 in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu___7, uu___8) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu___9 = destruct_flex_t env t1 wl in
                  (match uu___9 with
                   | (f1, wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu___7;
                    FStar_Syntax_Syntax.pos = uu___8;
                    FStar_Syntax_Syntax.vars = uu___9;
                    FStar_Syntax_Syntax.hash_code = uu___10;_},
                  uu___11),
                 uu___12) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu___13 = destruct_flex_t env t1 wl in
                  (match uu___13 with
                   | (f1, wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu___7, FStar_Syntax_Syntax.Tm_uvar uu___8) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t' env (invert problem) wl
              | (uu___7, FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu___8;
                    FStar_Syntax_Syntax.pos = uu___9;
                    FStar_Syntax_Syntax.vars = uu___10;
                    FStar_Syntax_Syntax.hash_code = uu___11;_},
                  uu___12)) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t' env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar uu___7,
                 FStar_Syntax_Syntax.Tm_arrow uu___8) ->
                  solve_t' env
                    {
                      FStar_TypeChecker_Common.pid =
                        (problem.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (problem.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        FStar_TypeChecker_Common.EQ;
                      FStar_TypeChecker_Common.rhs =
                        (problem.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (problem.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (problem.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (problem.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (problem.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (problem.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (problem.FStar_TypeChecker_Common.rank)
                    } wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu___7;
                    FStar_Syntax_Syntax.pos = uu___8;
                    FStar_Syntax_Syntax.vars = uu___9;
                    FStar_Syntax_Syntax.hash_code = uu___10;_},
                  uu___11),
                 FStar_Syntax_Syntax.Tm_arrow uu___12) ->
                  solve_t' env
                    {
                      FStar_TypeChecker_Common.pid =
                        (problem.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (problem.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        FStar_TypeChecker_Common.EQ;
                      FStar_TypeChecker_Common.rhs =
                        (problem.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (problem.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (problem.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (problem.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (problem.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (problem.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (problem.FStar_TypeChecker_Common.rank)
                    } wl
              | (uu___7, FStar_Syntax_Syntax.Tm_uvar uu___8) ->
                  let uu___9 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl in
                  solve env uu___9
              | (uu___7, FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu___8;
                    FStar_Syntax_Syntax.pos = uu___9;
                    FStar_Syntax_Syntax.vars = uu___10;
                    FStar_Syntax_Syntax.hash_code = uu___11;_},
                  uu___12)) ->
                  let uu___13 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl in
                  solve env uu___13
              | (FStar_Syntax_Syntax.Tm_uvar uu___7, uu___8) ->
                  let uu___9 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl in
                  solve env uu___9
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu___7;
                    FStar_Syntax_Syntax.pos = uu___8;
                    FStar_Syntax_Syntax.vars = uu___9;
                    FStar_Syntax_Syntax.hash_code = uu___10;_},
                  uu___11),
                 uu___12) ->
                  let uu___13 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl in
                  solve env uu___13
              | (FStar_Syntax_Syntax.Tm_abs uu___7, uu___8) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu___9 ->
                        FStar_Pervasives.Inl t
                    | uu___9 -> FStar_Pervasives.Inr t in
                  (match ((is_abs t1), (is_abs t2)) with
                   | (FStar_Pervasives.Inl t_abs, FStar_Pervasives.Inr
                      not_abs) ->
                       let uu___9 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                       if uu___9
                       then
                         let uu___10 = destruct_flex_t env not_abs wl in
                         (match uu___10 with
                          | (flex, wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let uu___11 =
                            head_matches_delta env wl.smt_ok not_abs t_abs in
                          match uu___11 with
                          | (HeadMatch uu___12, FStar_Pervasives_Native.Some
                             (not_abs', uu___13)) ->
                              solve_t env
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (problem.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = not_abs';
                                  FStar_TypeChecker_Common.relation =
                                    (problem.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t_abs;
                                  FStar_TypeChecker_Common.element =
                                    (problem.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (problem.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (problem.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (problem.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (problem.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (problem.FStar_TypeChecker_Common.rank)
                                } wl
                          | uu___12 ->
                              let uu___13 =
                                FStar_Syntax_Util.head_and_args not_abs in
                              (match uu___13 with
                               | (head, uu___14) ->
                                   let uu___15 =
                                     wl.smt_ok &&
                                       (may_relate env (p_rel orig) head) in
                                   if uu___15
                                   then
                                     let uu___16 =
                                       mk_eq2 wl env orig t_abs not_abs in
                                     (match uu___16 with
                                      | (g, wl1) ->
                                          let uu___17 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some g)
                                              [] wl1 in
                                          solve env uu___17)
                                   else
                                     (let uu___17 =
                                        FStar_Thunk.mkv
                                          "head tag mismatch: RHS is an abstraction" in
                                      giveup env uu___17 orig)))
                   | (FStar_Pervasives.Inr not_abs, FStar_Pervasives.Inl
                      t_abs) ->
                       let uu___9 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                       if uu___9
                       then
                         let uu___10 = destruct_flex_t env not_abs wl in
                         (match uu___10 with
                          | (flex, wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let uu___11 =
                            head_matches_delta env wl.smt_ok not_abs t_abs in
                          match uu___11 with
                          | (HeadMatch uu___12, FStar_Pervasives_Native.Some
                             (not_abs', uu___13)) ->
                              solve_t env
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (problem.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = not_abs';
                                  FStar_TypeChecker_Common.relation =
                                    (problem.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t_abs;
                                  FStar_TypeChecker_Common.element =
                                    (problem.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (problem.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (problem.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (problem.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (problem.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (problem.FStar_TypeChecker_Common.rank)
                                } wl
                          | uu___12 ->
                              let uu___13 =
                                FStar_Syntax_Util.head_and_args not_abs in
                              (match uu___13 with
                               | (head, uu___14) ->
                                   let uu___15 =
                                     wl.smt_ok &&
                                       (may_relate env (p_rel orig) head) in
                                   if uu___15
                                   then
                                     let uu___16 =
                                       mk_eq2 wl env orig t_abs not_abs in
                                     (match uu___16 with
                                      | (g, wl1) ->
                                          let uu___17 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some g)
                                              [] wl1 in
                                          solve env uu___17)
                                   else
                                     (let uu___17 =
                                        FStar_Thunk.mkv
                                          "head tag mismatch: RHS is an abstraction" in
                                      giveup env uu___17 orig)))
                   | uu___9 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu___7, FStar_Syntax_Syntax.Tm_abs uu___8) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu___9 ->
                        FStar_Pervasives.Inl t
                    | uu___9 -> FStar_Pervasives.Inr t in
                  (match ((is_abs t1), (is_abs t2)) with
                   | (FStar_Pervasives.Inl t_abs, FStar_Pervasives.Inr
                      not_abs) ->
                       let uu___9 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                       if uu___9
                       then
                         let uu___10 = destruct_flex_t env not_abs wl in
                         (match uu___10 with
                          | (flex, wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let uu___11 =
                            head_matches_delta env wl.smt_ok not_abs t_abs in
                          match uu___11 with
                          | (HeadMatch uu___12, FStar_Pervasives_Native.Some
                             (not_abs', uu___13)) ->
                              solve_t env
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (problem.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = not_abs';
                                  FStar_TypeChecker_Common.relation =
                                    (problem.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t_abs;
                                  FStar_TypeChecker_Common.element =
                                    (problem.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (problem.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (problem.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (problem.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (problem.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (problem.FStar_TypeChecker_Common.rank)
                                } wl
                          | uu___12 ->
                              let uu___13 =
                                FStar_Syntax_Util.head_and_args not_abs in
                              (match uu___13 with
                               | (head, uu___14) ->
                                   let uu___15 =
                                     wl.smt_ok &&
                                       (may_relate env (p_rel orig) head) in
                                   if uu___15
                                   then
                                     let uu___16 =
                                       mk_eq2 wl env orig t_abs not_abs in
                                     (match uu___16 with
                                      | (g, wl1) ->
                                          let uu___17 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some g)
                                              [] wl1 in
                                          solve env uu___17)
                                   else
                                     (let uu___17 =
                                        FStar_Thunk.mkv
                                          "head tag mismatch: RHS is an abstraction" in
                                      giveup env uu___17 orig)))
                   | (FStar_Pervasives.Inr not_abs, FStar_Pervasives.Inl
                      t_abs) ->
                       let uu___9 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                       if uu___9
                       then
                         let uu___10 = destruct_flex_t env not_abs wl in
                         (match uu___10 with
                          | (flex, wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let uu___11 =
                            head_matches_delta env wl.smt_ok not_abs t_abs in
                          match uu___11 with
                          | (HeadMatch uu___12, FStar_Pervasives_Native.Some
                             (not_abs', uu___13)) ->
                              solve_t env
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (problem.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = not_abs';
                                  FStar_TypeChecker_Common.relation =
                                    (problem.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = t_abs;
                                  FStar_TypeChecker_Common.element =
                                    (problem.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (problem.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (problem.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (problem.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (problem.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (problem.FStar_TypeChecker_Common.rank)
                                } wl
                          | uu___12 ->
                              let uu___13 =
                                FStar_Syntax_Util.head_and_args not_abs in
                              (match uu___13 with
                               | (head, uu___14) ->
                                   let uu___15 =
                                     wl.smt_ok &&
                                       (may_relate env (p_rel orig) head) in
                                   if uu___15
                                   then
                                     let uu___16 =
                                       mk_eq2 wl env orig t_abs not_abs in
                                     (match uu___16 with
                                      | (g, wl1) ->
                                          let uu___17 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some g)
                                              [] wl1 in
                                          solve env uu___17)
                                   else
                                     (let uu___17 =
                                        FStar_Thunk.mkv
                                          "head tag mismatch: RHS is an abstraction" in
                                      giveup env uu___17 orig)))
                   | uu___9 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine uu___7, uu___8) ->
                  let t21 =
                    let uu___9 = base_and_refinement env t2 in
                    FStar_Compiler_Effect.op_Less_Bar force_refinement uu___9 in
                  solve_t' env
                    {
                      FStar_TypeChecker_Common.pid =
                        (problem.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (problem.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (problem.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = t21;
                      FStar_TypeChecker_Common.element =
                        (problem.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (problem.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (problem.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (problem.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (problem.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (problem.FStar_TypeChecker_Common.rank)
                    } wl
              | (uu___7, FStar_Syntax_Syntax.Tm_refine uu___8) ->
                  let t11 =
                    let uu___9 = base_and_refinement env t1 in
                    FStar_Compiler_Effect.op_Less_Bar force_refinement uu___9 in
                  solve_t' env
                    {
                      FStar_TypeChecker_Common.pid =
                        (problem.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = t11;
                      FStar_TypeChecker_Common.relation =
                        (problem.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (problem.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (problem.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (problem.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (problem.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (problem.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (problem.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (problem.FStar_TypeChecker_Common.rank)
                    } wl
              | (FStar_Syntax_Syntax.Tm_match (s1, uu___7, brs1, uu___8),
                 FStar_Syntax_Syntax.Tm_match (s2, uu___9, brs2, uu___10)) ->
                  let by_smt uu___11 =
                    let uu___12 = guard_of_prob env wl problem t1 t2 in
                    match uu___12 with
                    | (guard, wl1) ->
                        let uu___13 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1 in
                        solve env uu___13 in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1, br2::rs2) ->
                        let uu___11 = br1 in
                        (match uu___11 with
                         | (p1, w1, uu___12) ->
                             let uu___13 = br2 in
                             (match uu___13 with
                              | (p2, w2, uu___14) ->
                                  let uu___15 =
                                    let uu___16 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2 in
                                    Prims.op_Negation uu___16 in
                                  if uu___15
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu___17 =
                                       FStar_Syntax_Subst.open_branch' br1 in
                                     match uu___17 with
                                     | ((p11, w11, e1), s) ->
                                         let uu___18 = br2 in
                                         (match uu___18 with
                                          | (p21, w21, e2) ->
                                              let w22 =
                                                FStar_Compiler_Util.map_opt
                                                  w21
                                                  (FStar_Syntax_Subst.subst s) in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2 in
                                              let scope =
                                                let uu___19 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11 in
                                                FStar_Compiler_Effect.op_Less_Bar
                                                  (FStar_Compiler_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu___19 in
                                              let uu___19 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu___20,
                                                   FStar_Pervasives_Native.None)
                                                    ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None,
                                                   FStar_Pervasives_Native.Some
                                                   uu___20) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None,
                                                   FStar_Pervasives_Native.None)
                                                    ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,
                                                   FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu___20 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause" in
                                                    (match uu___20 with
                                                     | (p, wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2)) in
                                              FStar_Compiler_Util.bind_opt
                                                uu___19
                                                (fun uu___20 ->
                                                   match uu___20 with
                                                   | (wprobs, wl2) ->
                                                       let uu___21 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body" in
                                                       (match uu___21 with
                                                        | (prob, wl3) ->
                                                            ((let uu___23 =
                                                                FStar_Compiler_Effect.op_Less_Bar
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel") in
                                                              if uu___23
                                                              then
                                                                let uu___24 =
                                                                  prob_to_string
                                                                    env prob in
                                                                let uu___25 =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope in
                                                                FStar_Compiler_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu___24
                                                                  uu___25
                                                              else ());
                                                             (let uu___23 =
                                                                solve_branches
                                                                  wl3 rs1 rs2 in
                                                              FStar_Compiler_Util.bind_opt
                                                                uu___23
                                                                (fun uu___24
                                                                   ->
                                                                   match uu___24
                                                                   with
                                                                   | 
                                                                   (r1, wl4)
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (((scope,
                                                                    prob) ::
                                                                    (FStar_Compiler_List.op_At
                                                                    wprobs r1)),
                                                                    wl4))))))))))
                    | ([], []) -> FStar_Pervasives_Native.Some ([], wl1)
                    | uu___11 -> FStar_Pervasives_Native.None in
                  let uu___11 = solve_branches wl brs1 brs2 in
                  (match uu___11 with
                   | FStar_Pervasives_Native.None ->
                       if wl.smt_ok
                       then by_smt ()
                       else
                         (let uu___13 =
                            FStar_Thunk.mkv "Tm_match branches don't match" in
                          giveup env uu___13 orig)
                   | FStar_Pervasives_Native.Some (sub_probs, wl1) ->
                       let uu___12 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee" in
                       (match uu___12 with
                        | (sc_prob, wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs in
                            let formula =
                              let uu___13 =
                                FStar_Compiler_List.map
                                  (fun uu___14 ->
                                     match uu___14 with
                                     | (scope, p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1 in
                              FStar_Syntax_Util.mk_conj_l uu___13 in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction () in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2 in
                            let uu___13 =
                              let uu___14 =
                                let uu___15 =
                                  FStar_Compiler_List.map
                                    FStar_Pervasives_Native.snd sub_probs1 in
                                attempt uu___15
                                  {
                                    attempting = (wl3.attempting);
                                    wl_deferred = (wl3.wl_deferred);
                                    wl_deferred_to_tac =
                                      (wl3.wl_deferred_to_tac);
                                    ctr = (wl3.ctr);
                                    defer_ok = (wl3.defer_ok);
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (wl3.umax_heuristic_ok);
                                    tcenv = (wl3.tcenv);
                                    wl_implicits = (wl3.wl_implicits);
                                    repr_subcomp_allowed =
                                      (wl3.repr_subcomp_allowed)
                                  } in
                              solve env uu___14 in
                            (match uu___13 with
                             | Success (ds, ds', imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, ds', imp))
                             | Failed uu___14 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  if wl3.smt_ok
                                  then by_smt ()
                                  else
                                    (let uu___17 =
                                       FStar_Thunk.mkv
                                         "Could not unify matches without SMT" in
                                     giveup env uu___17 orig)))))
              | (FStar_Syntax_Syntax.Tm_match uu___7, uu___8) ->
                  let head1 =
                    let uu___9 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_Compiler_Effect.op_Bar_Greater uu___9
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu___9 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_Compiler_Effect.op_Bar_Greater uu___9
                      FStar_Pervasives_Native.fst in
                  ((let uu___10 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu___10
                    then
                      let uu___11 =
                        let uu___12 =
                          FStar_Compiler_Util.string_of_int
                            problem.FStar_TypeChecker_Common.pid in
                        let uu___13 =
                          let uu___14 =
                            FStar_Compiler_Util.string_of_bool wl.smt_ok in
                          let uu___15 =
                            let uu___16 =
                              FStar_Syntax_Print.term_to_string head1 in
                            let uu___17 =
                              let uu___18 =
                                let uu___19 =
                                  FStar_TypeChecker_Env.is_interpreted env
                                    head1 in
                                FStar_Compiler_Util.string_of_bool uu___19 in
                              let uu___19 =
                                let uu___20 =
                                  let uu___21 = no_free_uvars t1 in
                                  FStar_Compiler_Util.string_of_bool uu___21 in
                                let uu___21 =
                                  let uu___22 =
                                    FStar_Syntax_Print.term_to_string head2 in
                                  let uu___23 =
                                    let uu___24 =
                                      let uu___25 =
                                        FStar_TypeChecker_Env.is_interpreted
                                          env head2 in
                                      FStar_Compiler_Util.string_of_bool
                                        uu___25 in
                                    let uu___25 =
                                      let uu___26 =
                                        let uu___27 = no_free_uvars t2 in
                                        FStar_Compiler_Util.string_of_bool
                                          uu___27 in
                                      [uu___26] in
                                    uu___24 :: uu___25 in
                                  uu___22 :: uu___23 in
                                uu___20 :: uu___21 in
                              uu___18 :: uu___19 in
                            uu___16 :: uu___17 in
                          uu___14 :: uu___15 in
                        uu___12 :: uu___13 in
                      FStar_Compiler_Util.print
                        ">> (%s) (smtok=%s)\n>>> head1 = %s [interpreted=%s; no_free_uvars=%s]\n>>> head2 = %s [interpreted=%s;no_free_uvars=%s]\n"
                        uu___11
                    else ());
                   (let equal t11 t21 =
                      (let uu___10 = FStar_Syntax_Util.eq_tm t11 t21 in
                       uu___10 = FStar_Syntax_Util.Equal) ||
                        (let steps =
                           [FStar_TypeChecker_Env.UnfoldUntil
                              FStar_Syntax_Syntax.delta_constant;
                           FStar_TypeChecker_Env.Primops;
                           FStar_TypeChecker_Env.Beta;
                           FStar_TypeChecker_Env.Eager_unfolding;
                           FStar_TypeChecker_Env.Iota] in
                         let t12 =
                           norm_with_steps
                             "FStar.TypeChecker.Rel.norm_with_steps.2" steps
                             env t11 in
                         let t22 =
                           norm_with_steps
                             "FStar.TypeChecker.Rel.norm_with_steps.3" steps
                             env t21 in
                         let uu___10 = FStar_Syntax_Util.eq_tm t12 t22 in
                         uu___10 = FStar_Syntax_Util.Equal) in
                    let uu___10 =
                      ((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ) in
                    if uu___10
                    then
                      let solve_with_smt uu___11 =
                        let uu___12 =
                          let uu___13 = equal t1 t2 in
                          if uu___13
                          then (FStar_Pervasives_Native.None, wl)
                          else
                            (let uu___15 = mk_eq2 wl env orig t1 t2 in
                             match uu___15 with
                             | (g, wl1) ->
                                 ((FStar_Pervasives_Native.Some g), wl1)) in
                        match uu___12 with
                        | (guard, wl1) ->
                            let uu___13 = solve_prob orig guard [] wl1 in
                            solve env uu___13 in
                      let uu___11 = (no_free_uvars t1) && (no_free_uvars t2) in
                      (if uu___11
                       then
                         let uu___12 =
                           (Prims.op_Negation wl.smt_ok) ||
                             (FStar_Options.ml_ish ()) in
                         (if uu___12
                          then
                            let uu___13 = equal t1 t2 in
                            (if uu___13
                             then
                               let uu___14 =
                                 solve_prob orig FStar_Pervasives_Native.None
                                   [] wl in
                               solve env uu___14
                             else
                               rigid_rigid_delta env problem wl head1 head2
                                 t1 t2)
                          else solve_with_smt ())
                       else
                         (let uu___13 =
                            (Prims.op_Negation wl.smt_ok) ||
                              (FStar_Options.ml_ish ()) in
                          if uu___13
                          then
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2
                          else
                            try_solve_then_or_else env wl
                              (fun env1 ->
                                 fun wl_empty ->
                                   rigid_rigid_delta env1 problem wl_empty
                                     head1 head2 t1 t2)
                              (fun env1 -> fun wl1 -> solve env1 wl1)
                              (fun uu___15 ->
                                 fun uu___16 -> solve_with_smt ())))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu___7, uu___8) ->
                  let head1 =
                    let uu___9 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_Compiler_Effect.op_Bar_Greater uu___9
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu___9 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_Compiler_Effect.op_Bar_Greater uu___9
                      FStar_Pervasives_Native.fst in
                  ((let uu___10 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu___10
                    then
                      let uu___11 =
                        let uu___12 =
                          FStar_Compiler_Util.string_of_int
                            problem.FStar_TypeChecker_Common.pid in
                        let uu___13 =
                          let uu___14 =
                            FStar_Compiler_Util.string_of_bool wl.smt_ok in
                          let uu___15 =
                            let uu___16 =
                              FStar_Syntax_Print.term_to_string head1 in
                            let uu___17 =
                              let uu___18 =
                                let uu___19 =
                                  FStar_TypeChecker_Env.is_interpreted env
                                    head1 in
                                FStar_Compiler_Util.string_of_bool uu___19 in
                              let uu___19 =
                                let uu___20 =
                                  let uu___21 = no_free_uvars t1 in
                                  FStar_Compiler_Util.string_of_bool uu___21 in
                                let uu___21 =
                                  let uu___22 =
                                    FStar_Syntax_Print.term_to_string head2 in
                                  let uu___23 =
                                    let uu___24 =
                                      let uu___25 =
                                        FStar_TypeChecker_Env.is_interpreted
                                          env head2 in
                                      FStar_Compiler_Util.string_of_bool
                                        uu___25 in
                                    let uu___25 =
                                      let uu___26 =
                                        let uu___27 = no_free_uvars t2 in
                                        FStar_Compiler_Util.string_of_bool
                                          uu___27 in
                                      [uu___26] in
                                    uu___24 :: uu___25 in
                                  uu___22 :: uu___23 in
                                uu___20 :: uu___21 in
                              uu___18 :: uu___19 in
                            uu___16 :: uu___17 in
                          uu___14 :: uu___15 in
                        uu___12 :: uu___13 in
                      FStar_Compiler_Util.print
                        ">> (%s) (smtok=%s)\n>>> head1 = %s [interpreted=%s; no_free_uvars=%s]\n>>> head2 = %s [interpreted=%s;no_free_uvars=%s]\n"
                        uu___11
                    else ());
                   (let equal t11 t21 =
                      (let uu___10 = FStar_Syntax_Util.eq_tm t11 t21 in
                       uu___10 = FStar_Syntax_Util.Equal) ||
                        (let steps =
                           [FStar_TypeChecker_Env.UnfoldUntil
                              FStar_Syntax_Syntax.delta_constant;
                           FStar_TypeChecker_Env.Primops;
                           FStar_TypeChecker_Env.Beta;
                           FStar_TypeChecker_Env.Eager_unfolding;
                           FStar_TypeChecker_Env.Iota] in
                         let t12 =
                           norm_with_steps
                             "FStar.TypeChecker.Rel.norm_with_steps.2" steps
                             env t11 in
                         let t22 =
                           norm_with_steps
                             "FStar.TypeChecker.Rel.norm_with_steps.3" steps
                             env t21 in
                         let uu___10 = FStar_Syntax_Util.eq_tm t12 t22 in
                         uu___10 = FStar_Syntax_Util.Equal) in
                    let uu___10 =
                      ((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ) in
                    if uu___10
                    then
                      let solve_with_smt uu___11 =
                        let uu___12 =
                          let uu___13 = equal t1 t2 in
                          if uu___13
                          then (FStar_Pervasives_Native.None, wl)
                          else
                            (let uu___15 = mk_eq2 wl env orig t1 t2 in
                             match uu___15 with
                             | (g, wl1) ->
                                 ((FStar_Pervasives_Native.Some g), wl1)) in
                        match uu___12 with
                        | (guard, wl1) ->
                            let uu___13 = solve_prob orig guard [] wl1 in
                            solve env uu___13 in
                      let uu___11 = (no_free_uvars t1) && (no_free_uvars t2) in
                      (if uu___11
                       then
                         let uu___12 =
                           (Prims.op_Negation wl.smt_ok) ||
                             (FStar_Options.ml_ish ()) in
                         (if uu___12
                          then
                            let uu___13 = equal t1 t2 in
                            (if uu___13
                             then
                               let uu___14 =
                                 solve_prob orig FStar_Pervasives_Native.None
                                   [] wl in
                               solve env uu___14
                             else
                               rigid_rigid_delta env problem wl head1 head2
                                 t1 t2)
                          else solve_with_smt ())
                       else
                         (let uu___13 =
                            (Prims.op_Negation wl.smt_ok) ||
                              (FStar_Options.ml_ish ()) in
                          if uu___13
                          then
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2
                          else
                            try_solve_then_or_else env wl
                              (fun env1 ->
                                 fun wl_empty ->
                                   rigid_rigid_delta env1 problem wl_empty
                                     head1 head2 t1 t2)
                              (fun env1 -> fun wl1 -> solve env1 wl1)
                              (fun uu___15 ->
                                 fun uu___16 -> solve_with_smt ())))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu___7, uu___8) ->
                  let head1 =
                    let uu___9 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_Compiler_Effect.op_Bar_Greater uu___9
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu___9 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_Compiler_Effect.op_Bar_Greater uu___9
                      FStar_Pervasives_Native.fst in
                  ((let uu___10 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu___10
                    then
                      let uu___11 =
                        let uu___12 =
                          FStar_Compiler_Util.string_of_int
                            problem.FStar_TypeChecker_Common.pid in
                        let uu___13 =
                          let uu___14 =
                            FStar_Compiler_Util.string_of_bool wl.smt_ok in
                          let uu___15 =
                            let uu___16 =
                              FStar_Syntax_Print.term_to_string head1 in
                            let uu___17 =
                              let uu___18 =
                                let uu___19 =
                                  FStar_TypeChecker_Env.is_interpreted env
                                    head1 in
                                FStar_Compiler_Util.string_of_bool uu___19 in
                              let uu___19 =
                                let uu___20 =
                                  let uu___21 = no_free_uvars t1 in
                                  FStar_Compiler_Util.string_of_bool uu___21 in
                                let uu___21 =
                                  let uu___22 =
                                    FStar_Syntax_Print.term_to_string head2 in
                                  let uu___23 =
                                    let uu___24 =
                                      let uu___25 =
                                        FStar_TypeChecker_Env.is_interpreted
                                          env head2 in
                                      FStar_Compiler_Util.string_of_bool
                                        uu___25 in
                                    let uu___25 =
                                      let uu___26 =
                                        let uu___27 = no_free_uvars t2 in
                                        FStar_Compiler_Util.string_of_bool
                                          uu___27 in
                                      [uu___26] in
                                    uu___24 :: uu___25 in
                                  uu___22 :: uu___23 in
                                uu___20 :: uu___21 in
                              uu___18 :: uu___19 in
                            uu___16 :: uu___17 in
                          uu___14 :: uu___15 in
                        uu___12 :: uu___13 in
                      FStar_Compiler_Util.print
                        ">> (%s) (smtok=%s)\n>>> head1 = %s [interpreted=%s; no_free_uvars=%s]\n>>> head2 = %s [interpreted=%s;no_free_uvars=%s]\n"
                        uu___11
                    else ());
                   (let equal t11 t21 =
                      (let uu___10 = FStar_Syntax_Util.eq_tm t11 t21 in
                       uu___10 = FStar_Syntax_Util.Equal) ||
                        (let steps =
                           [FStar_TypeChecker_Env.UnfoldUntil
                              FStar_Syntax_Syntax.delta_constant;
                           FStar_TypeChecker_Env.Primops;
                           FStar_TypeChecker_Env.Beta;
                           FStar_TypeChecker_Env.Eager_unfolding;
                           FStar_TypeChecker_Env.Iota] in
                         let t12 =
                           norm_with_steps
                             "FStar.TypeChecker.Rel.norm_with_steps.2" steps
                             env t11 in
                         let t22 =
                           norm_with_steps
                             "FStar.TypeChecker.Rel.norm_with_steps.3" steps
                             env t21 in
                         let uu___10 = FStar_Syntax_Util.eq_tm t12 t22 in
                         uu___10 = FStar_Syntax_Util.Equal) in
                    let uu___10 =
                      ((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ) in
                    if uu___10
                    then
                      let solve_with_smt uu___11 =
                        let uu___12 =
                          let uu___13 = equal t1 t2 in
                          if uu___13
                          then (FStar_Pervasives_Native.None, wl)
                          else
                            (let uu___15 = mk_eq2 wl env orig t1 t2 in
                             match uu___15 with
                             | (g, wl1) ->
                                 ((FStar_Pervasives_Native.Some g), wl1)) in
                        match uu___12 with
                        | (guard, wl1) ->
                            let uu___13 = solve_prob orig guard [] wl1 in
                            solve env uu___13 in
                      let uu___11 = (no_free_uvars t1) && (no_free_uvars t2) in
                      (if uu___11
                       then
                         let uu___12 =
                           (Prims.op_Negation wl.smt_ok) ||
                             (FStar_Options.ml_ish ()) in
                         (if uu___12
                          then
                            let uu___13 = equal t1 t2 in
                            (if uu___13
                             then
                               let uu___14 =
                                 solve_prob orig FStar_Pervasives_Native.None
                                   [] wl in
                               solve env uu___14
                             else
                               rigid_rigid_delta env problem wl head1 head2
                                 t1 t2)
                          else solve_with_smt ())
                       else
                         (let uu___13 =
                            (Prims.op_Negation wl.smt_ok) ||
                              (FStar_Options.ml_ish ()) in
                          if uu___13
                          then
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2
                          else
                            try_solve_then_or_else env wl
                              (fun env1 ->
                                 fun wl_empty ->
                                   rigid_rigid_delta env1 problem wl_empty
                                     head1 head2 t1 t2)
                              (fun env1 -> fun wl1 -> solve env1 wl1)
                              (fun uu___15 ->
                                 fun uu___16 -> solve_with_smt ())))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu___7, uu___8) ->
                  let head1 =
                    let uu___9 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_Compiler_Effect.op_Bar_Greater uu___9
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu___9 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_Compiler_Effect.op_Bar_Greater uu___9
                      FStar_Pervasives_Native.fst in
                  ((let uu___10 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu___10
                    then
                      let uu___11 =
                        let uu___12 =
                          FStar_Compiler_Util.string_of_int
                            problem.FStar_TypeChecker_Common.pid in
                        let uu___13 =
                          let uu___14 =
                            FStar_Compiler_Util.string_of_bool wl.smt_ok in
                          let uu___15 =
                            let uu___16 =
                              FStar_Syntax_Print.term_to_string head1 in
                            let uu___17 =
                              let uu___18 =
                                let uu___19 =
                                  FStar_TypeChecker_Env.is_interpreted env
                                    head1 in
                                FStar_Compiler_Util.string_of_bool uu___19 in
                              let uu___19 =
                                let uu___20 =
                                  let uu___21 = no_free_uvars t1 in
                                  FStar_Compiler_Util.string_of_bool uu___21 in
                                let uu___21 =
                                  let uu___22 =
                                    FStar_Syntax_Print.term_to_string head2 in
                                  let uu___23 =
                                    let uu___24 =
                                      let uu___25 =
                                        FStar_TypeChecker_Env.is_interpreted
                                          env head2 in
                                      FStar_Compiler_Util.string_of_bool
                                        uu___25 in
                                    let uu___25 =
                                      let uu___26 =
                                        let uu___27 = no_free_uvars t2 in
                                        FStar_Compiler_Util.string_of_bool
                                          uu___27 in
                                      [uu___26] in
                                    uu___24 :: uu___25 in
                                  uu___22 :: uu___23 in
                                uu___20 :: uu___21 in
                              uu___18 :: uu___19 in
                            uu___16 :: uu___17 in
                          uu___14 :: uu___15 in
                        uu___12 :: uu___13 in
                      FStar_Compiler_Util.print
                        ">> (%s) (smtok=%s)\n>>> head1 = %s [interpreted=%s; no_free_uvars=%s]\n>>> head2 = %s [interpreted=%s;no_free_uvars=%s]\n"
                        uu___11
                    else ());
                   (let equal t11 t21 =
                      (let uu___10 = FStar_Syntax_Util.eq_tm t11 t21 in
                       uu___10 = FStar_Syntax_Util.Equal) ||
                        (let steps =
                           [FStar_TypeChecker_Env.UnfoldUntil
                              FStar_Syntax_Syntax.delta_constant;
                           FStar_TypeChecker_Env.Primops;
                           FStar_TypeChecker_Env.Beta;
                           FStar_TypeChecker_Env.Eager_unfolding;
                           FStar_TypeChecker_Env.Iota] in
                         let t12 =
                           norm_with_steps
                             "FStar.TypeChecker.Rel.norm_with_steps.2" steps
                             env t11 in
                         let t22 =
                           norm_with_steps
                             "FStar.TypeChecker.Rel.norm_with_steps.3" steps
                             env t21 in
                         let uu___10 = FStar_Syntax_Util.eq_tm t12 t22 in
                         uu___10 = FStar_Syntax_Util.Equal) in
                    let uu___10 =
                      ((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ) in
                    if uu___10
                    then
                      let solve_with_smt uu___11 =
                        let uu___12 =
                          let uu___13 = equal t1 t2 in
                          if uu___13
                          then (FStar_Pervasives_Native.None, wl)
                          else
                            (let uu___15 = mk_eq2 wl env orig t1 t2 in
                             match uu___15 with
                             | (g, wl1) ->
                                 ((FStar_Pervasives_Native.Some g), wl1)) in
                        match uu___12 with
                        | (guard, wl1) ->
                            let uu___13 = solve_prob orig guard [] wl1 in
                            solve env uu___13 in
                      let uu___11 = (no_free_uvars t1) && (no_free_uvars t2) in
                      (if uu___11
                       then
                         let uu___12 =
                           (Prims.op_Negation wl.smt_ok) ||
                             (FStar_Options.ml_ish ()) in
                         (if uu___12
                          then
                            let uu___13 = equal t1 t2 in
                            (if uu___13
                             then
                               let uu___14 =
                                 solve_prob orig FStar_Pervasives_Native.None
                                   [] wl in
                               solve env uu___14
                             else
                               rigid_rigid_delta env problem wl head1 head2
                                 t1 t2)
                          else solve_with_smt ())
                       else
                         (let uu___13 =
                            (Prims.op_Negation wl.smt_ok) ||
                              (FStar_Options.ml_ish ()) in
                          if uu___13
                          then
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2
                          else
                            try_solve_then_or_else env wl
                              (fun env1 ->
                                 fun wl_empty ->
                                   rigid_rigid_delta env1 problem wl_empty
                                     head1 head2 t1 t2)
                              (fun env1 -> fun wl1 -> solve env1 wl1)
                              (fun uu___15 ->
                                 fun uu___16 -> solve_with_smt ())))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu___7, uu___8) ->
                  let head1 =
                    let uu___9 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_Compiler_Effect.op_Bar_Greater uu___9
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu___9 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_Compiler_Effect.op_Bar_Greater uu___9
                      FStar_Pervasives_Native.fst in
                  ((let uu___10 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu___10
                    then
                      let uu___11 =
                        let uu___12 =
                          FStar_Compiler_Util.string_of_int
                            problem.FStar_TypeChecker_Common.pid in
                        let uu___13 =
                          let uu___14 =
                            FStar_Compiler_Util.string_of_bool wl.smt_ok in
                          let uu___15 =
                            let uu___16 =
                              FStar_Syntax_Print.term_to_string head1 in
                            let uu___17 =
                              let uu___18 =
                                let uu___19 =
                                  FStar_TypeChecker_Env.is_interpreted env
                                    head1 in
                                FStar_Compiler_Util.string_of_bool uu___19 in
                              let uu___19 =
                                let uu___20 =
                                  let uu___21 = no_free_uvars t1 in
                                  FStar_Compiler_Util.string_of_bool uu___21 in
                                let uu___21 =
                                  let uu___22 =
                                    FStar_Syntax_Print.term_to_string head2 in
                                  let uu___23 =
                                    let uu___24 =
                                      let uu___25 =
                                        FStar_TypeChecker_Env.is_interpreted
                                          env head2 in
                                      FStar_Compiler_Util.string_of_bool
                                        uu___25 in
                                    let uu___25 =
                                      let uu___26 =
                                        let uu___27 = no_free_uvars t2 in
                                        FStar_Compiler_Util.string_of_bool
                                          uu___27 in
                                      [uu___26] in
                                    uu___24 :: uu___25 in
                                  uu___22 :: uu___23 in
                                uu___20 :: uu___21 in
                              uu___18 :: uu___19 in
                            uu___16 :: uu___17 in
                          uu___14 :: uu___15 in
                        uu___12 :: uu___13 in
                      FStar_Compiler_Util.print
                        ">> (%s) (smtok=%s)\n>>> head1 = %s [interpreted=%s; no_free_uvars=%s]\n>>> head2 = %s [interpreted=%s;no_free_uvars=%s]\n"
                        uu___11
                    else ());
                   (let equal t11 t21 =
                      (let uu___10 = FStar_Syntax_Util.eq_tm t11 t21 in
                       uu___10 = FStar_Syntax_Util.Equal) ||
                        (let steps =
                           [FStar_TypeChecker_Env.UnfoldUntil
                              FStar_Syntax_Syntax.delta_constant;
                           FStar_TypeChecker_Env.Primops;
                           FStar_TypeChecker_Env.Beta;
                           FStar_TypeChecker_Env.Eager_unfolding;
                           FStar_TypeChecker_Env.Iota] in
                         let t12 =
                           norm_with_steps
                             "FStar.TypeChecker.Rel.norm_with_steps.2" steps
                             env t11 in
                         let t22 =
                           norm_with_steps
                             "FStar.TypeChecker.Rel.norm_with_steps.3" steps
                             env t21 in
                         let uu___10 = FStar_Syntax_Util.eq_tm t12 t22 in
                         uu___10 = FStar_Syntax_Util.Equal) in
                    let uu___10 =
                      ((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ) in
                    if uu___10
                    then
                      let solve_with_smt uu___11 =
                        let uu___12 =
                          let uu___13 = equal t1 t2 in
                          if uu___13
                          then (FStar_Pervasives_Native.None, wl)
                          else
                            (let uu___15 = mk_eq2 wl env orig t1 t2 in
                             match uu___15 with
                             | (g, wl1) ->
                                 ((FStar_Pervasives_Native.Some g), wl1)) in
                        match uu___12 with
                        | (guard, wl1) ->
                            let uu___13 = solve_prob orig guard [] wl1 in
                            solve env uu___13 in
                      let uu___11 = (no_free_uvars t1) && (no_free_uvars t2) in
                      (if uu___11
                       then
                         let uu___12 =
                           (Prims.op_Negation wl.smt_ok) ||
                             (FStar_Options.ml_ish ()) in
                         (if uu___12
                          then
                            let uu___13 = equal t1 t2 in
                            (if uu___13
                             then
                               let uu___14 =
                                 solve_prob orig FStar_Pervasives_Native.None
                                   [] wl in
                               solve env uu___14
                             else
                               rigid_rigid_delta env problem wl head1 head2
                                 t1 t2)
                          else solve_with_smt ())
                       else
                         (let uu___13 =
                            (Prims.op_Negation wl.smt_ok) ||
                              (FStar_Options.ml_ish ()) in
                          if uu___13
                          then
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2
                          else
                            try_solve_then_or_else env wl
                              (fun env1 ->
                                 fun wl_empty ->
                                   rigid_rigid_delta env1 problem wl_empty
                                     head1 head2 t1 t2)
                              (fun env1 -> fun wl1 -> solve env1 wl1)
                              (fun uu___15 ->
                                 fun uu___16 -> solve_with_smt ())))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu___7, uu___8) ->
                  let head1 =
                    let uu___9 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_Compiler_Effect.op_Bar_Greater uu___9
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu___9 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_Compiler_Effect.op_Bar_Greater uu___9
                      FStar_Pervasives_Native.fst in
                  ((let uu___10 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu___10
                    then
                      let uu___11 =
                        let uu___12 =
                          FStar_Compiler_Util.string_of_int
                            problem.FStar_TypeChecker_Common.pid in
                        let uu___13 =
                          let uu___14 =
                            FStar_Compiler_Util.string_of_bool wl.smt_ok in
                          let uu___15 =
                            let uu___16 =
                              FStar_Syntax_Print.term_to_string head1 in
                            let uu___17 =
                              let uu___18 =
                                let uu___19 =
                                  FStar_TypeChecker_Env.is_interpreted env
                                    head1 in
                                FStar_Compiler_Util.string_of_bool uu___19 in
                              let uu___19 =
                                let uu___20 =
                                  let uu___21 = no_free_uvars t1 in
                                  FStar_Compiler_Util.string_of_bool uu___21 in
                                let uu___21 =
                                  let uu___22 =
                                    FStar_Syntax_Print.term_to_string head2 in
                                  let uu___23 =
                                    let uu___24 =
                                      let uu___25 =
                                        FStar_TypeChecker_Env.is_interpreted
                                          env head2 in
                                      FStar_Compiler_Util.string_of_bool
                                        uu___25 in
                                    let uu___25 =
                                      let uu___26 =
                                        let uu___27 = no_free_uvars t2 in
                                        FStar_Compiler_Util.string_of_bool
                                          uu___27 in
                                      [uu___26] in
                                    uu___24 :: uu___25 in
                                  uu___22 :: uu___23 in
                                uu___20 :: uu___21 in
                              uu___18 :: uu___19 in
                            uu___16 :: uu___17 in
                          uu___14 :: uu___15 in
                        uu___12 :: uu___13 in
                      FStar_Compiler_Util.print
                        ">> (%s) (smtok=%s)\n>>> head1 = %s [interpreted=%s; no_free_uvars=%s]\n>>> head2 = %s [interpreted=%s;no_free_uvars=%s]\n"
                        uu___11
                    else ());
                   (let equal t11 t21 =
                      (let uu___10 = FStar_Syntax_Util.eq_tm t11 t21 in
                       uu___10 = FStar_Syntax_Util.Equal) ||
                        (let steps =
                           [FStar_TypeChecker_Env.UnfoldUntil
                              FStar_Syntax_Syntax.delta_constant;
                           FStar_TypeChecker_Env.Primops;
                           FStar_TypeChecker_Env.Beta;
                           FStar_TypeChecker_Env.Eager_unfolding;
                           FStar_TypeChecker_Env.Iota] in
                         let t12 =
                           norm_with_steps
                             "FStar.TypeChecker.Rel.norm_with_steps.2" steps
                             env t11 in
                         let t22 =
                           norm_with_steps
                             "FStar.TypeChecker.Rel.norm_with_steps.3" steps
                             env t21 in
                         let uu___10 = FStar_Syntax_Util.eq_tm t12 t22 in
                         uu___10 = FStar_Syntax_Util.Equal) in
                    let uu___10 =
                      ((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ) in
                    if uu___10
                    then
                      let solve_with_smt uu___11 =
                        let uu___12 =
                          let uu___13 = equal t1 t2 in
                          if uu___13
                          then (FStar_Pervasives_Native.None, wl)
                          else
                            (let uu___15 = mk_eq2 wl env orig t1 t2 in
                             match uu___15 with
                             | (g, wl1) ->
                                 ((FStar_Pervasives_Native.Some g), wl1)) in
                        match uu___12 with
                        | (guard, wl1) ->
                            let uu___13 = solve_prob orig guard [] wl1 in
                            solve env uu___13 in
                      let uu___11 = (no_free_uvars t1) && (no_free_uvars t2) in
                      (if uu___11
                       then
                         let uu___12 =
                           (Prims.op_Negation wl.smt_ok) ||
                             (FStar_Options.ml_ish ()) in
                         (if uu___12
                          then
                            let uu___13 = equal t1 t2 in
                            (if uu___13
                             then
                               let uu___14 =
                                 solve_prob orig FStar_Pervasives_Native.None
                                   [] wl in
                               solve env uu___14
                             else
                               rigid_rigid_delta env problem wl head1 head2
                                 t1 t2)
                          else solve_with_smt ())
                       else
                         (let uu___13 =
                            (Prims.op_Negation wl.smt_ok) ||
                              (FStar_Options.ml_ish ()) in
                          if uu___13
                          then
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2
                          else
                            try_solve_then_or_else env wl
                              (fun env1 ->
                                 fun wl_empty ->
                                   rigid_rigid_delta env1 problem wl_empty
                                     head1 head2 t1 t2)
                              (fun env1 -> fun wl1 -> solve env1 wl1)
                              (fun uu___15 ->
                                 fun uu___16 -> solve_with_smt ())))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu___7, FStar_Syntax_Syntax.Tm_match uu___8) ->
                  let head1 =
                    let uu___9 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_Compiler_Effect.op_Bar_Greater uu___9
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu___9 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_Compiler_Effect.op_Bar_Greater uu___9
                      FStar_Pervasives_Native.fst in
                  ((let uu___10 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu___10
                    then
                      let uu___11 =
                        let uu___12 =
                          FStar_Compiler_Util.string_of_int
                            problem.FStar_TypeChecker_Common.pid in
                        let uu___13 =
                          let uu___14 =
                            FStar_Compiler_Util.string_of_bool wl.smt_ok in
                          let uu___15 =
                            let uu___16 =
                              FStar_Syntax_Print.term_to_string head1 in
                            let uu___17 =
                              let uu___18 =
                                let uu___19 =
                                  FStar_TypeChecker_Env.is_interpreted env
                                    head1 in
                                FStar_Compiler_Util.string_of_bool uu___19 in
                              let uu___19 =
                                let uu___20 =
                                  let uu___21 = no_free_uvars t1 in
                                  FStar_Compiler_Util.string_of_bool uu___21 in
                                let uu___21 =
                                  let uu___22 =
                                    FStar_Syntax_Print.term_to_string head2 in
                                  let uu___23 =
                                    let uu___24 =
                                      let uu___25 =
                                        FStar_TypeChecker_Env.is_interpreted
                                          env head2 in
                                      FStar_Compiler_Util.string_of_bool
                                        uu___25 in
                                    let uu___25 =
                                      let uu___26 =
                                        let uu___27 = no_free_uvars t2 in
                                        FStar_Compiler_Util.string_of_bool
                                          uu___27 in
                                      [uu___26] in
                                    uu___24 :: uu___25 in
                                  uu___22 :: uu___23 in
                                uu___20 :: uu___21 in
                              uu___18 :: uu___19 in
                            uu___16 :: uu___17 in
                          uu___14 :: uu___15 in
                        uu___12 :: uu___13 in
                      FStar_Compiler_Util.print
                        ">> (%s) (smtok=%s)\n>>> head1 = %s [interpreted=%s; no_free_uvars=%s]\n>>> head2 = %s [interpreted=%s;no_free_uvars=%s]\n"
                        uu___11
                    else ());
                   (let equal t11 t21 =
                      (let uu___10 = FStar_Syntax_Util.eq_tm t11 t21 in
                       uu___10 = FStar_Syntax_Util.Equal) ||
                        (let steps =
                           [FStar_TypeChecker_Env.UnfoldUntil
                              FStar_Syntax_Syntax.delta_constant;
                           FStar_TypeChecker_Env.Primops;
                           FStar_TypeChecker_Env.Beta;
                           FStar_TypeChecker_Env.Eager_unfolding;
                           FStar_TypeChecker_Env.Iota] in
                         let t12 =
                           norm_with_steps
                             "FStar.TypeChecker.Rel.norm_with_steps.2" steps
                             env t11 in
                         let t22 =
                           norm_with_steps
                             "FStar.TypeChecker.Rel.norm_with_steps.3" steps
                             env t21 in
                         let uu___10 = FStar_Syntax_Util.eq_tm t12 t22 in
                         uu___10 = FStar_Syntax_Util.Equal) in
                    let uu___10 =
                      ((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ) in
                    if uu___10
                    then
                      let solve_with_smt uu___11 =
                        let uu___12 =
                          let uu___13 = equal t1 t2 in
                          if uu___13
                          then (FStar_Pervasives_Native.None, wl)
                          else
                            (let uu___15 = mk_eq2 wl env orig t1 t2 in
                             match uu___15 with
                             | (g, wl1) ->
                                 ((FStar_Pervasives_Native.Some g), wl1)) in
                        match uu___12 with
                        | (guard, wl1) ->
                            let uu___13 = solve_prob orig guard [] wl1 in
                            solve env uu___13 in
                      let uu___11 = (no_free_uvars t1) && (no_free_uvars t2) in
                      (if uu___11
                       then
                         let uu___12 =
                           (Prims.op_Negation wl.smt_ok) ||
                             (FStar_Options.ml_ish ()) in
                         (if uu___12
                          then
                            let uu___13 = equal t1 t2 in
                            (if uu___13
                             then
                               let uu___14 =
                                 solve_prob orig FStar_Pervasives_Native.None
                                   [] wl in
                               solve env uu___14
                             else
                               rigid_rigid_delta env problem wl head1 head2
                                 t1 t2)
                          else solve_with_smt ())
                       else
                         (let uu___13 =
                            (Prims.op_Negation wl.smt_ok) ||
                              (FStar_Options.ml_ish ()) in
                          if uu___13
                          then
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2
                          else
                            try_solve_then_or_else env wl
                              (fun env1 ->
                                 fun wl_empty ->
                                   rigid_rigid_delta env1 problem wl_empty
                                     head1 head2 t1 t2)
                              (fun env1 -> fun wl1 -> solve env1 wl1)
                              (fun uu___15 ->
                                 fun uu___16 -> solve_with_smt ())))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu___7, FStar_Syntax_Syntax.Tm_uinst uu___8) ->
                  let head1 =
                    let uu___9 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_Compiler_Effect.op_Bar_Greater uu___9
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu___9 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_Compiler_Effect.op_Bar_Greater uu___9
                      FStar_Pervasives_Native.fst in
                  ((let uu___10 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu___10
                    then
                      let uu___11 =
                        let uu___12 =
                          FStar_Compiler_Util.string_of_int
                            problem.FStar_TypeChecker_Common.pid in
                        let uu___13 =
                          let uu___14 =
                            FStar_Compiler_Util.string_of_bool wl.smt_ok in
                          let uu___15 =
                            let uu___16 =
                              FStar_Syntax_Print.term_to_string head1 in
                            let uu___17 =
                              let uu___18 =
                                let uu___19 =
                                  FStar_TypeChecker_Env.is_interpreted env
                                    head1 in
                                FStar_Compiler_Util.string_of_bool uu___19 in
                              let uu___19 =
                                let uu___20 =
                                  let uu___21 = no_free_uvars t1 in
                                  FStar_Compiler_Util.string_of_bool uu___21 in
                                let uu___21 =
                                  let uu___22 =
                                    FStar_Syntax_Print.term_to_string head2 in
                                  let uu___23 =
                                    let uu___24 =
                                      let uu___25 =
                                        FStar_TypeChecker_Env.is_interpreted
                                          env head2 in
                                      FStar_Compiler_Util.string_of_bool
                                        uu___25 in
                                    let uu___25 =
                                      let uu___26 =
                                        let uu___27 = no_free_uvars t2 in
                                        FStar_Compiler_Util.string_of_bool
                                          uu___27 in
                                      [uu___26] in
                                    uu___24 :: uu___25 in
                                  uu___22 :: uu___23 in
                                uu___20 :: uu___21 in
                              uu___18 :: uu___19 in
                            uu___16 :: uu___17 in
                          uu___14 :: uu___15 in
                        uu___12 :: uu___13 in
                      FStar_Compiler_Util.print
                        ">> (%s) (smtok=%s)\n>>> head1 = %s [interpreted=%s; no_free_uvars=%s]\n>>> head2 = %s [interpreted=%s;no_free_uvars=%s]\n"
                        uu___11
                    else ());
                   (let equal t11 t21 =
                      (let uu___10 = FStar_Syntax_Util.eq_tm t11 t21 in
                       uu___10 = FStar_Syntax_Util.Equal) ||
                        (let steps =
                           [FStar_TypeChecker_Env.UnfoldUntil
                              FStar_Syntax_Syntax.delta_constant;
                           FStar_TypeChecker_Env.Primops;
                           FStar_TypeChecker_Env.Beta;
                           FStar_TypeChecker_Env.Eager_unfolding;
                           FStar_TypeChecker_Env.Iota] in
                         let t12 =
                           norm_with_steps
                             "FStar.TypeChecker.Rel.norm_with_steps.2" steps
                             env t11 in
                         let t22 =
                           norm_with_steps
                             "FStar.TypeChecker.Rel.norm_with_steps.3" steps
                             env t21 in
                         let uu___10 = FStar_Syntax_Util.eq_tm t12 t22 in
                         uu___10 = FStar_Syntax_Util.Equal) in
                    let uu___10 =
                      ((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ) in
                    if uu___10
                    then
                      let solve_with_smt uu___11 =
                        let uu___12 =
                          let uu___13 = equal t1 t2 in
                          if uu___13
                          then (FStar_Pervasives_Native.None, wl)
                          else
                            (let uu___15 = mk_eq2 wl env orig t1 t2 in
                             match uu___15 with
                             | (g, wl1) ->
                                 ((FStar_Pervasives_Native.Some g), wl1)) in
                        match uu___12 with
                        | (guard, wl1) ->
                            let uu___13 = solve_prob orig guard [] wl1 in
                            solve env uu___13 in
                      let uu___11 = (no_free_uvars t1) && (no_free_uvars t2) in
                      (if uu___11
                       then
                         let uu___12 =
                           (Prims.op_Negation wl.smt_ok) ||
                             (FStar_Options.ml_ish ()) in
                         (if uu___12
                          then
                            let uu___13 = equal t1 t2 in
                            (if uu___13
                             then
                               let uu___14 =
                                 solve_prob orig FStar_Pervasives_Native.None
                                   [] wl in
                               solve env uu___14
                             else
                               rigid_rigid_delta env problem wl head1 head2
                                 t1 t2)
                          else solve_with_smt ())
                       else
                         (let uu___13 =
                            (Prims.op_Negation wl.smt_ok) ||
                              (FStar_Options.ml_ish ()) in
                          if uu___13
                          then
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2
                          else
                            try_solve_then_or_else env wl
                              (fun env1 ->
                                 fun wl_empty ->
                                   rigid_rigid_delta env1 problem wl_empty
                                     head1 head2 t1 t2)
                              (fun env1 -> fun wl1 -> solve env1 wl1)
                              (fun uu___15 ->
                                 fun uu___16 -> solve_with_smt ())))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu___7, FStar_Syntax_Syntax.Tm_name uu___8) ->
                  let head1 =
                    let uu___9 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_Compiler_Effect.op_Bar_Greater uu___9
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu___9 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_Compiler_Effect.op_Bar_Greater uu___9
                      FStar_Pervasives_Native.fst in
                  ((let uu___10 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu___10
                    then
                      let uu___11 =
                        let uu___12 =
                          FStar_Compiler_Util.string_of_int
                            problem.FStar_TypeChecker_Common.pid in
                        let uu___13 =
                          let uu___14 =
                            FStar_Compiler_Util.string_of_bool wl.smt_ok in
                          let uu___15 =
                            let uu___16 =
                              FStar_Syntax_Print.term_to_string head1 in
                            let uu___17 =
                              let uu___18 =
                                let uu___19 =
                                  FStar_TypeChecker_Env.is_interpreted env
                                    head1 in
                                FStar_Compiler_Util.string_of_bool uu___19 in
                              let uu___19 =
                                let uu___20 =
                                  let uu___21 = no_free_uvars t1 in
                                  FStar_Compiler_Util.string_of_bool uu___21 in
                                let uu___21 =
                                  let uu___22 =
                                    FStar_Syntax_Print.term_to_string head2 in
                                  let uu___23 =
                                    let uu___24 =
                                      let uu___25 =
                                        FStar_TypeChecker_Env.is_interpreted
                                          env head2 in
                                      FStar_Compiler_Util.string_of_bool
                                        uu___25 in
                                    let uu___25 =
                                      let uu___26 =
                                        let uu___27 = no_free_uvars t2 in
                                        FStar_Compiler_Util.string_of_bool
                                          uu___27 in
                                      [uu___26] in
                                    uu___24 :: uu___25 in
                                  uu___22 :: uu___23 in
                                uu___20 :: uu___21 in
                              uu___18 :: uu___19 in
                            uu___16 :: uu___17 in
                          uu___14 :: uu___15 in
                        uu___12 :: uu___13 in
                      FStar_Compiler_Util.print
                        ">> (%s) (smtok=%s)\n>>> head1 = %s [interpreted=%s; no_free_uvars=%s]\n>>> head2 = %s [interpreted=%s;no_free_uvars=%s]\n"
                        uu___11
                    else ());
                   (let equal t11 t21 =
                      (let uu___10 = FStar_Syntax_Util.eq_tm t11 t21 in
                       uu___10 = FStar_Syntax_Util.Equal) ||
                        (let steps =
                           [FStar_TypeChecker_Env.UnfoldUntil
                              FStar_Syntax_Syntax.delta_constant;
                           FStar_TypeChecker_Env.Primops;
                           FStar_TypeChecker_Env.Beta;
                           FStar_TypeChecker_Env.Eager_unfolding;
                           FStar_TypeChecker_Env.Iota] in
                         let t12 =
                           norm_with_steps
                             "FStar.TypeChecker.Rel.norm_with_steps.2" steps
                             env t11 in
                         let t22 =
                           norm_with_steps
                             "FStar.TypeChecker.Rel.norm_with_steps.3" steps
                             env t21 in
                         let uu___10 = FStar_Syntax_Util.eq_tm t12 t22 in
                         uu___10 = FStar_Syntax_Util.Equal) in
                    let uu___10 =
                      ((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ) in
                    if uu___10
                    then
                      let solve_with_smt uu___11 =
                        let uu___12 =
                          let uu___13 = equal t1 t2 in
                          if uu___13
                          then (FStar_Pervasives_Native.None, wl)
                          else
                            (let uu___15 = mk_eq2 wl env orig t1 t2 in
                             match uu___15 with
                             | (g, wl1) ->
                                 ((FStar_Pervasives_Native.Some g), wl1)) in
                        match uu___12 with
                        | (guard, wl1) ->
                            let uu___13 = solve_prob orig guard [] wl1 in
                            solve env uu___13 in
                      let uu___11 = (no_free_uvars t1) && (no_free_uvars t2) in
                      (if uu___11
                       then
                         let uu___12 =
                           (Prims.op_Negation wl.smt_ok) ||
                             (FStar_Options.ml_ish ()) in
                         (if uu___12
                          then
                            let uu___13 = equal t1 t2 in
                            (if uu___13
                             then
                               let uu___14 =
                                 solve_prob orig FStar_Pervasives_Native.None
                                   [] wl in
                               solve env uu___14
                             else
                               rigid_rigid_delta env problem wl head1 head2
                                 t1 t2)
                          else solve_with_smt ())
                       else
                         (let uu___13 =
                            (Prims.op_Negation wl.smt_ok) ||
                              (FStar_Options.ml_ish ()) in
                          if uu___13
                          then
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2
                          else
                            try_solve_then_or_else env wl
                              (fun env1 ->
                                 fun wl_empty ->
                                   rigid_rigid_delta env1 problem wl_empty
                                     head1 head2 t1 t2)
                              (fun env1 -> fun wl1 -> solve env1 wl1)
                              (fun uu___15 ->
                                 fun uu___16 -> solve_with_smt ())))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu___7, FStar_Syntax_Syntax.Tm_constant uu___8) ->
                  let head1 =
                    let uu___9 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_Compiler_Effect.op_Bar_Greater uu___9
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu___9 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_Compiler_Effect.op_Bar_Greater uu___9
                      FStar_Pervasives_Native.fst in
                  ((let uu___10 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu___10
                    then
                      let uu___11 =
                        let uu___12 =
                          FStar_Compiler_Util.string_of_int
                            problem.FStar_TypeChecker_Common.pid in
                        let uu___13 =
                          let uu___14 =
                            FStar_Compiler_Util.string_of_bool wl.smt_ok in
                          let uu___15 =
                            let uu___16 =
                              FStar_Syntax_Print.term_to_string head1 in
                            let uu___17 =
                              let uu___18 =
                                let uu___19 =
                                  FStar_TypeChecker_Env.is_interpreted env
                                    head1 in
                                FStar_Compiler_Util.string_of_bool uu___19 in
                              let uu___19 =
                                let uu___20 =
                                  let uu___21 = no_free_uvars t1 in
                                  FStar_Compiler_Util.string_of_bool uu___21 in
                                let uu___21 =
                                  let uu___22 =
                                    FStar_Syntax_Print.term_to_string head2 in
                                  let uu___23 =
                                    let uu___24 =
                                      let uu___25 =
                                        FStar_TypeChecker_Env.is_interpreted
                                          env head2 in
                                      FStar_Compiler_Util.string_of_bool
                                        uu___25 in
                                    let uu___25 =
                                      let uu___26 =
                                        let uu___27 = no_free_uvars t2 in
                                        FStar_Compiler_Util.string_of_bool
                                          uu___27 in
                                      [uu___26] in
                                    uu___24 :: uu___25 in
                                  uu___22 :: uu___23 in
                                uu___20 :: uu___21 in
                              uu___18 :: uu___19 in
                            uu___16 :: uu___17 in
                          uu___14 :: uu___15 in
                        uu___12 :: uu___13 in
                      FStar_Compiler_Util.print
                        ">> (%s) (smtok=%s)\n>>> head1 = %s [interpreted=%s; no_free_uvars=%s]\n>>> head2 = %s [interpreted=%s;no_free_uvars=%s]\n"
                        uu___11
                    else ());
                   (let equal t11 t21 =
                      (let uu___10 = FStar_Syntax_Util.eq_tm t11 t21 in
                       uu___10 = FStar_Syntax_Util.Equal) ||
                        (let steps =
                           [FStar_TypeChecker_Env.UnfoldUntil
                              FStar_Syntax_Syntax.delta_constant;
                           FStar_TypeChecker_Env.Primops;
                           FStar_TypeChecker_Env.Beta;
                           FStar_TypeChecker_Env.Eager_unfolding;
                           FStar_TypeChecker_Env.Iota] in
                         let t12 =
                           norm_with_steps
                             "FStar.TypeChecker.Rel.norm_with_steps.2" steps
                             env t11 in
                         let t22 =
                           norm_with_steps
                             "FStar.TypeChecker.Rel.norm_with_steps.3" steps
                             env t21 in
                         let uu___10 = FStar_Syntax_Util.eq_tm t12 t22 in
                         uu___10 = FStar_Syntax_Util.Equal) in
                    let uu___10 =
                      ((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ) in
                    if uu___10
                    then
                      let solve_with_smt uu___11 =
                        let uu___12 =
                          let uu___13 = equal t1 t2 in
                          if uu___13
                          then (FStar_Pervasives_Native.None, wl)
                          else
                            (let uu___15 = mk_eq2 wl env orig t1 t2 in
                             match uu___15 with
                             | (g, wl1) ->
                                 ((FStar_Pervasives_Native.Some g), wl1)) in
                        match uu___12 with
                        | (guard, wl1) ->
                            let uu___13 = solve_prob orig guard [] wl1 in
                            solve env uu___13 in
                      let uu___11 = (no_free_uvars t1) && (no_free_uvars t2) in
                      (if uu___11
                       then
                         let uu___12 =
                           (Prims.op_Negation wl.smt_ok) ||
                             (FStar_Options.ml_ish ()) in
                         (if uu___12
                          then
                            let uu___13 = equal t1 t2 in
                            (if uu___13
                             then
                               let uu___14 =
                                 solve_prob orig FStar_Pervasives_Native.None
                                   [] wl in
                               solve env uu___14
                             else
                               rigid_rigid_delta env problem wl head1 head2
                                 t1 t2)
                          else solve_with_smt ())
                       else
                         (let uu___13 =
                            (Prims.op_Negation wl.smt_ok) ||
                              (FStar_Options.ml_ish ()) in
                          if uu___13
                          then
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2
                          else
                            try_solve_then_or_else env wl
                              (fun env1 ->
                                 fun wl_empty ->
                                   rigid_rigid_delta env1 problem wl_empty
                                     head1 head2 t1 t2)
                              (fun env1 -> fun wl1 -> solve env1 wl1)
                              (fun uu___15 ->
                                 fun uu___16 -> solve_with_smt ())))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu___7, FStar_Syntax_Syntax.Tm_fvar uu___8) ->
                  let head1 =
                    let uu___9 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_Compiler_Effect.op_Bar_Greater uu___9
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu___9 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_Compiler_Effect.op_Bar_Greater uu___9
                      FStar_Pervasives_Native.fst in
                  ((let uu___10 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu___10
                    then
                      let uu___11 =
                        let uu___12 =
                          FStar_Compiler_Util.string_of_int
                            problem.FStar_TypeChecker_Common.pid in
                        let uu___13 =
                          let uu___14 =
                            FStar_Compiler_Util.string_of_bool wl.smt_ok in
                          let uu___15 =
                            let uu___16 =
                              FStar_Syntax_Print.term_to_string head1 in
                            let uu___17 =
                              let uu___18 =
                                let uu___19 =
                                  FStar_TypeChecker_Env.is_interpreted env
                                    head1 in
                                FStar_Compiler_Util.string_of_bool uu___19 in
                              let uu___19 =
                                let uu___20 =
                                  let uu___21 = no_free_uvars t1 in
                                  FStar_Compiler_Util.string_of_bool uu___21 in
                                let uu___21 =
                                  let uu___22 =
                                    FStar_Syntax_Print.term_to_string head2 in
                                  let uu___23 =
                                    let uu___24 =
                                      let uu___25 =
                                        FStar_TypeChecker_Env.is_interpreted
                                          env head2 in
                                      FStar_Compiler_Util.string_of_bool
                                        uu___25 in
                                    let uu___25 =
                                      let uu___26 =
                                        let uu___27 = no_free_uvars t2 in
                                        FStar_Compiler_Util.string_of_bool
                                          uu___27 in
                                      [uu___26] in
                                    uu___24 :: uu___25 in
                                  uu___22 :: uu___23 in
                                uu___20 :: uu___21 in
                              uu___18 :: uu___19 in
                            uu___16 :: uu___17 in
                          uu___14 :: uu___15 in
                        uu___12 :: uu___13 in
                      FStar_Compiler_Util.print
                        ">> (%s) (smtok=%s)\n>>> head1 = %s [interpreted=%s; no_free_uvars=%s]\n>>> head2 = %s [interpreted=%s;no_free_uvars=%s]\n"
                        uu___11
                    else ());
                   (let equal t11 t21 =
                      (let uu___10 = FStar_Syntax_Util.eq_tm t11 t21 in
                       uu___10 = FStar_Syntax_Util.Equal) ||
                        (let steps =
                           [FStar_TypeChecker_Env.UnfoldUntil
                              FStar_Syntax_Syntax.delta_constant;
                           FStar_TypeChecker_Env.Primops;
                           FStar_TypeChecker_Env.Beta;
                           FStar_TypeChecker_Env.Eager_unfolding;
                           FStar_TypeChecker_Env.Iota] in
                         let t12 =
                           norm_with_steps
                             "FStar.TypeChecker.Rel.norm_with_steps.2" steps
                             env t11 in
                         let t22 =
                           norm_with_steps
                             "FStar.TypeChecker.Rel.norm_with_steps.3" steps
                             env t21 in
                         let uu___10 = FStar_Syntax_Util.eq_tm t12 t22 in
                         uu___10 = FStar_Syntax_Util.Equal) in
                    let uu___10 =
                      ((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ) in
                    if uu___10
                    then
                      let solve_with_smt uu___11 =
                        let uu___12 =
                          let uu___13 = equal t1 t2 in
                          if uu___13
                          then (FStar_Pervasives_Native.None, wl)
                          else
                            (let uu___15 = mk_eq2 wl env orig t1 t2 in
                             match uu___15 with
                             | (g, wl1) ->
                                 ((FStar_Pervasives_Native.Some g), wl1)) in
                        match uu___12 with
                        | (guard, wl1) ->
                            let uu___13 = solve_prob orig guard [] wl1 in
                            solve env uu___13 in
                      let uu___11 = (no_free_uvars t1) && (no_free_uvars t2) in
                      (if uu___11
                       then
                         let uu___12 =
                           (Prims.op_Negation wl.smt_ok) ||
                             (FStar_Options.ml_ish ()) in
                         (if uu___12
                          then
                            let uu___13 = equal t1 t2 in
                            (if uu___13
                             then
                               let uu___14 =
                                 solve_prob orig FStar_Pervasives_Native.None
                                   [] wl in
                               solve env uu___14
                             else
                               rigid_rigid_delta env problem wl head1 head2
                                 t1 t2)
                          else solve_with_smt ())
                       else
                         (let uu___13 =
                            (Prims.op_Negation wl.smt_ok) ||
                              (FStar_Options.ml_ish ()) in
                          if uu___13
                          then
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2
                          else
                            try_solve_then_or_else env wl
                              (fun env1 ->
                                 fun wl_empty ->
                                   rigid_rigid_delta env1 problem wl_empty
                                     head1 head2 t1 t2)
                              (fun env1 -> fun wl1 -> solve env1 wl1)
                              (fun uu___15 ->
                                 fun uu___16 -> solve_with_smt ())))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu___7, FStar_Syntax_Syntax.Tm_app uu___8) ->
                  let head1 =
                    let uu___9 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_Compiler_Effect.op_Bar_Greater uu___9
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu___9 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_Compiler_Effect.op_Bar_Greater uu___9
                      FStar_Pervasives_Native.fst in
                  ((let uu___10 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu___10
                    then
                      let uu___11 =
                        let uu___12 =
                          FStar_Compiler_Util.string_of_int
                            problem.FStar_TypeChecker_Common.pid in
                        let uu___13 =
                          let uu___14 =
                            FStar_Compiler_Util.string_of_bool wl.smt_ok in
                          let uu___15 =
                            let uu___16 =
                              FStar_Syntax_Print.term_to_string head1 in
                            let uu___17 =
                              let uu___18 =
                                let uu___19 =
                                  FStar_TypeChecker_Env.is_interpreted env
                                    head1 in
                                FStar_Compiler_Util.string_of_bool uu___19 in
                              let uu___19 =
                                let uu___20 =
                                  let uu___21 = no_free_uvars t1 in
                                  FStar_Compiler_Util.string_of_bool uu___21 in
                                let uu___21 =
                                  let uu___22 =
                                    FStar_Syntax_Print.term_to_string head2 in
                                  let uu___23 =
                                    let uu___24 =
                                      let uu___25 =
                                        FStar_TypeChecker_Env.is_interpreted
                                          env head2 in
                                      FStar_Compiler_Util.string_of_bool
                                        uu___25 in
                                    let uu___25 =
                                      let uu___26 =
                                        let uu___27 = no_free_uvars t2 in
                                        FStar_Compiler_Util.string_of_bool
                                          uu___27 in
                                      [uu___26] in
                                    uu___24 :: uu___25 in
                                  uu___22 :: uu___23 in
                                uu___20 :: uu___21 in
                              uu___18 :: uu___19 in
                            uu___16 :: uu___17 in
                          uu___14 :: uu___15 in
                        uu___12 :: uu___13 in
                      FStar_Compiler_Util.print
                        ">> (%s) (smtok=%s)\n>>> head1 = %s [interpreted=%s; no_free_uvars=%s]\n>>> head2 = %s [interpreted=%s;no_free_uvars=%s]\n"
                        uu___11
                    else ());
                   (let equal t11 t21 =
                      (let uu___10 = FStar_Syntax_Util.eq_tm t11 t21 in
                       uu___10 = FStar_Syntax_Util.Equal) ||
                        (let steps =
                           [FStar_TypeChecker_Env.UnfoldUntil
                              FStar_Syntax_Syntax.delta_constant;
                           FStar_TypeChecker_Env.Primops;
                           FStar_TypeChecker_Env.Beta;
                           FStar_TypeChecker_Env.Eager_unfolding;
                           FStar_TypeChecker_Env.Iota] in
                         let t12 =
                           norm_with_steps
                             "FStar.TypeChecker.Rel.norm_with_steps.2" steps
                             env t11 in
                         let t22 =
                           norm_with_steps
                             "FStar.TypeChecker.Rel.norm_with_steps.3" steps
                             env t21 in
                         let uu___10 = FStar_Syntax_Util.eq_tm t12 t22 in
                         uu___10 = FStar_Syntax_Util.Equal) in
                    let uu___10 =
                      ((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ) in
                    if uu___10
                    then
                      let solve_with_smt uu___11 =
                        let uu___12 =
                          let uu___13 = equal t1 t2 in
                          if uu___13
                          then (FStar_Pervasives_Native.None, wl)
                          else
                            (let uu___15 = mk_eq2 wl env orig t1 t2 in
                             match uu___15 with
                             | (g, wl1) ->
                                 ((FStar_Pervasives_Native.Some g), wl1)) in
                        match uu___12 with
                        | (guard, wl1) ->
                            let uu___13 = solve_prob orig guard [] wl1 in
                            solve env uu___13 in
                      let uu___11 = (no_free_uvars t1) && (no_free_uvars t2) in
                      (if uu___11
                       then
                         let uu___12 =
                           (Prims.op_Negation wl.smt_ok) ||
                             (FStar_Options.ml_ish ()) in
                         (if uu___12
                          then
                            let uu___13 = equal t1 t2 in
                            (if uu___13
                             then
                               let uu___14 =
                                 solve_prob orig FStar_Pervasives_Native.None
                                   [] wl in
                               solve env uu___14
                             else
                               rigid_rigid_delta env problem wl head1 head2
                                 t1 t2)
                          else solve_with_smt ())
                       else
                         (let uu___13 =
                            (Prims.op_Negation wl.smt_ok) ||
                              (FStar_Options.ml_ish ()) in
                          if uu___13
                          then
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2
                          else
                            try_solve_then_or_else env wl
                              (fun env1 ->
                                 fun wl_empty ->
                                   rigid_rigid_delta env1 problem wl_empty
                                     head1 head2 t1 t2)
                              (fun env1 -> fun wl1 -> solve env1 wl1)
                              (fun uu___15 ->
                                 fun uu___16 -> solve_with_smt ())))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let uu___7,
                 FStar_Syntax_Syntax.Tm_let uu___8) ->
                  let uu___9 = FStar_Syntax_Util.term_eq t1 t2 in
                  if uu___9
                  then
                    let uu___10 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl in
                    solve env uu___10
                  else
                    (let uu___11 = FStar_Thunk.mkv "Tm_let mismatch" in
                     giveup env uu___11 orig)
              | (FStar_Syntax_Syntax.Tm_let uu___7, uu___8) ->
                  let uu___9 =
                    let uu___10 =
                      let uu___11 = FStar_Syntax_Print.tag_of_term t1 in
                      let uu___12 = FStar_Syntax_Print.tag_of_term t2 in
                      let uu___13 = FStar_Syntax_Print.term_to_string t1 in
                      let uu___14 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Compiler_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu___11 uu___12 uu___13 uu___14 in
                    (FStar_Errors.Fatal_UnificationNotWellFormed, uu___10) in
                  FStar_Errors.raise_error uu___9 t1.FStar_Syntax_Syntax.pos
              | (uu___7, FStar_Syntax_Syntax.Tm_let uu___8) ->
                  let uu___9 =
                    let uu___10 =
                      let uu___11 = FStar_Syntax_Print.tag_of_term t1 in
                      let uu___12 = FStar_Syntax_Print.tag_of_term t2 in
                      let uu___13 = FStar_Syntax_Print.term_to_string t1 in
                      let uu___14 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Compiler_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu___11 uu___12 uu___13 uu___14 in
                    (FStar_Errors.Fatal_UnificationNotWellFormed, uu___10) in
                  FStar_Errors.raise_error uu___9 t1.FStar_Syntax_Syntax.pos
              | uu___7 ->
                  let uu___8 = FStar_Thunk.mkv "head tag mismatch" in
                  giveup env uu___8 orig))))
and (solve_c :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem ->
      worklist -> solution)
  =
  fun env ->
    fun problem ->
      fun wl ->
        let c1 = problem.FStar_TypeChecker_Common.lhs in
        let c2 = problem.FStar_TypeChecker_Common.rhs in
        let orig = FStar_TypeChecker_Common.CProb problem in
        let sub_prob wl1 t1 rel t2 reason =
          mk_t_problem wl1 [] orig t1 rel t2 FStar_Pervasives_Native.None
            reason in
        let solve_eq c1_comp c2_comp g_lift =
          (let uu___1 =
             FStar_Compiler_Effect.op_Less_Bar
               (FStar_TypeChecker_Env.debug env) (FStar_Options.Other "EQ") in
           if uu___1
           then
             let uu___2 =
               let uu___3 = FStar_Syntax_Syntax.mk_Comp c1_comp in
               FStar_Syntax_Print.comp_to_string uu___3 in
             let uu___3 =
               let uu___4 = FStar_Syntax_Syntax.mk_Comp c2_comp in
               FStar_Syntax_Print.comp_to_string uu___4 in
             FStar_Compiler_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n" uu___2
               uu___3
           else ());
          (let uu___1 =
             let uu___2 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name in
             Prims.op_Negation uu___2 in
           if uu___1
           then
             let uu___2 =
               mklstr
                 (fun uu___3 ->
                    let uu___4 =
                      FStar_Syntax_Print.lid_to_string
                        c1_comp.FStar_Syntax_Syntax.effect_name in
                    let uu___5 =
                      FStar_Syntax_Print.lid_to_string
                        c2_comp.FStar_Syntax_Syntax.effect_name in
                    FStar_Compiler_Util.format2
                      "incompatible effects: %s <> %s" uu___4 uu___5) in
             giveup env uu___2 orig
           else
             if
               (FStar_Compiler_List.length
                  c1_comp.FStar_Syntax_Syntax.effect_args)
                 <>
                 (FStar_Compiler_List.length
                    c2_comp.FStar_Syntax_Syntax.effect_args)
             then
               (let uu___3 =
                  mklstr
                    (fun uu___4 ->
                       let uu___5 =
                         FStar_Syntax_Print.args_to_string
                           c1_comp.FStar_Syntax_Syntax.effect_args in
                       let uu___6 =
                         FStar_Syntax_Print.args_to_string
                           c2_comp.FStar_Syntax_Syntax.effect_args in
                       FStar_Compiler_Util.format2
                         "incompatible effect arguments: %s <> %s" uu___5
                         uu___6) in
                giveup env uu___3 orig)
             else
               (let uu___4 =
                  FStar_Compiler_List.fold_left2
                    (fun uu___5 ->
                       fun u1 ->
                         fun u2 ->
                           match uu___5 with
                           | (univ_sub_probs, wl1) ->
                               let uu___6 =
                                 let uu___7 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u1)
                                     FStar_Compiler_Range.dummyRange in
                                 let uu___8 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u2)
                                     FStar_Compiler_Range.dummyRange in
                                 sub_prob wl1 uu___7
                                   FStar_TypeChecker_Common.EQ uu___8
                                   "effect universes" in
                               (match uu___6 with
                                | (p, wl2) ->
                                    ((FStar_Compiler_List.op_At
                                        univ_sub_probs [p]), wl2))) ([], wl)
                    c1_comp.FStar_Syntax_Syntax.comp_univs
                    c2_comp.FStar_Syntax_Syntax.comp_univs in
                match uu___4 with
                | (univ_sub_probs, wl1) ->
                    let uu___5 =
                      sub_prob wl1 c1_comp.FStar_Syntax_Syntax.result_typ
                        FStar_TypeChecker_Common.EQ
                        c2_comp.FStar_Syntax_Syntax.result_typ
                        "effect ret type" in
                    (match uu___5 with
                     | (ret_sub_prob, wl2) ->
                         let uu___6 =
                           FStar_Compiler_List.fold_right2
                             (fun uu___7 ->
                                fun uu___8 ->
                                  fun uu___9 ->
                                    match (uu___7, uu___8, uu___9) with
                                    | ((a1, uu___10), (a2, uu___11),
                                       (arg_sub_probs, wl3)) ->
                                        let uu___12 =
                                          sub_prob wl3 a1
                                            FStar_TypeChecker_Common.EQ a2
                                            "effect arg" in
                                        (match uu___12 with
                                         | (p, wl4) ->
                                             ((p :: arg_sub_probs), wl4)))
                             c1_comp.FStar_Syntax_Syntax.effect_args
                             c2_comp.FStar_Syntax_Syntax.effect_args
                             ([], wl2) in
                         (match uu___6 with
                          | (arg_sub_probs, wl3) ->
                              let sub_probs =
                                let uu___7 =
                                  let uu___8 =
                                    let uu___9 =
                                      FStar_Compiler_Effect.op_Bar_Greater
                                        g_lift.FStar_TypeChecker_Common.deferred
                                        (FStar_Compiler_List.map
                                           (fun uu___10 ->
                                              match uu___10 with
                                              | (uu___11, uu___12, p) -> p)) in
                                    FStar_Compiler_List.op_At arg_sub_probs
                                      uu___9 in
                                  FStar_Compiler_List.op_At [ret_sub_prob]
                                    uu___8 in
                                FStar_Compiler_List.op_At univ_sub_probs
                                  uu___7 in
                              let guard =
                                let guard1 =
                                  let uu___7 =
                                    FStar_Compiler_List.map p_guard sub_probs in
                                  FStar_Syntax_Util.mk_conj_l uu___7 in
                                match g_lift.FStar_TypeChecker_Common.guard_f
                                with
                                | FStar_TypeChecker_Common.Trivial -> guard1
                                | FStar_TypeChecker_Common.NonTrivial f ->
                                    FStar_Syntax_Util.mk_conj guard1 f in
                              let wl4 =
                                {
                                  attempting = (wl3.attempting);
                                  wl_deferred = (wl3.wl_deferred);
                                  wl_deferred_to_tac =
                                    (wl3.wl_deferred_to_tac);
                                  ctr = (wl3.ctr);
                                  defer_ok = (wl3.defer_ok);
                                  smt_ok = (wl3.smt_ok);
                                  umax_heuristic_ok = (wl3.umax_heuristic_ok);
                                  tcenv = (wl3.tcenv);
                                  wl_implicits =
                                    (FStar_Compiler_List.op_At
                                       g_lift.FStar_TypeChecker_Common.implicits
                                       wl3.wl_implicits);
                                  repr_subcomp_allowed =
                                    (wl3.repr_subcomp_allowed)
                                } in
                              let wl5 =
                                solve_prob orig
                                  (FStar_Pervasives_Native.Some guard) [] wl4 in
                              let uu___7 = attempt sub_probs wl5 in
                              solve env uu___7)))) in
        let should_fail_since_repr_subcomp_not_allowed repr_subcomp_allowed
          c11 c21 =
          let uu___ =
            let uu___1 = FStar_TypeChecker_Env.norm_eff_name env c11 in
            let uu___2 = FStar_TypeChecker_Env.norm_eff_name env c21 in
            (uu___1, uu___2) in
          match uu___ with
          | (c12, c22) ->
              ((Prims.op_Negation wl.repr_subcomp_allowed) &&
                 (let uu___1 = FStar_Ident.lid_equals c12 c22 in
                  Prims.op_Negation uu___1))
                && (FStar_TypeChecker_Env.is_reifiable_effect env c22) in
        let solve_layered_sub c11 c21 =
          (let uu___1 =
             FStar_Compiler_Effect.op_Less_Bar
               (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffectsApp") in
           if uu___1
           then
             let uu___2 =
               let uu___3 =
                 FStar_Compiler_Effect.op_Bar_Greater c11
                   FStar_Syntax_Syntax.mk_Comp in
               FStar_Compiler_Effect.op_Bar_Greater uu___3
                 FStar_Syntax_Print.comp_to_string in
             let uu___3 =
               let uu___4 =
                 FStar_Compiler_Effect.op_Bar_Greater c21
                   FStar_Syntax_Syntax.mk_Comp in
               FStar_Compiler_Effect.op_Bar_Greater uu___4
                 FStar_Syntax_Print.comp_to_string in
             FStar_Compiler_Util.print2
               "solve_layered_sub c1: %s and c2: %s\n" uu___2 uu___3
           else ());
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then solve_eq c11 c21 FStar_TypeChecker_Env.trivial_guard
          else
            (let r = FStar_TypeChecker_Env.get_range env in
             let uu___2 =
               should_fail_since_repr_subcomp_not_allowed
                 wl.repr_subcomp_allowed c11.FStar_Syntax_Syntax.effect_name
                 c21.FStar_Syntax_Syntax.effect_name in
             if uu___2
             then
               let uu___3 =
                 mklstr
                   (fun uu___4 ->
                      let uu___5 =
                        FStar_Ident.string_of_lid
                          c11.FStar_Syntax_Syntax.effect_name in
                      let uu___6 =
                        FStar_Ident.string_of_lid
                          c21.FStar_Syntax_Syntax.effect_name in
                      FStar_Compiler_Util.format2
                        "Cannot lift from %s to %s, it needs a lift\n" uu___5
                        uu___6) in
               giveup env uu___3 orig
             else
               (let subcomp_name =
                  let uu___4 =
                    let uu___5 =
                      FStar_Compiler_Effect.op_Bar_Greater
                        c11.FStar_Syntax_Syntax.effect_name
                        FStar_Ident.ident_of_lid in
                    FStar_Compiler_Effect.op_Bar_Greater uu___5
                      FStar_Ident.string_of_id in
                  let uu___5 =
                    let uu___6 =
                      FStar_Compiler_Effect.op_Bar_Greater
                        c21.FStar_Syntax_Syntax.effect_name
                        FStar_Ident.ident_of_lid in
                    FStar_Compiler_Effect.op_Bar_Greater uu___6
                      FStar_Ident.string_of_id in
                  FStar_Compiler_Util.format2 "%s <: %s" uu___4 uu___5 in
                let lift_c1 edge =
                  let guard_indexed_effect_uvars = true in
                  let uu___4 =
                    let uu___5 =
                      FStar_Compiler_Effect.op_Bar_Greater c11
                        FStar_Syntax_Syntax.mk_Comp in
                    FStar_Compiler_Effect.op_Bar_Greater uu___5
                      ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                         env guard_indexed_effect_uvars) in
                  FStar_Compiler_Effect.op_Bar_Greater uu___4
                    (fun uu___5 ->
                       match uu___5 with
                       | (c, g) ->
                           let uu___6 = FStar_Syntax_Util.comp_to_comp_typ c in
                           (uu___6, g)) in
                let uu___4 =
                  let uu___5 =
                    FStar_TypeChecker_Env.exists_polymonadic_subcomp env
                      c11.FStar_Syntax_Syntax.effect_name
                      c21.FStar_Syntax_Syntax.effect_name in
                  match uu___5 with
                  | FStar_Pervasives_Native.None ->
                      let uu___6 =
                        FStar_TypeChecker_Env.monad_leq env
                          c11.FStar_Syntax_Syntax.effect_name
                          c21.FStar_Syntax_Syntax.effect_name in
                      (match uu___6 with
                       | FStar_Pervasives_Native.None ->
                           (c11, FStar_TypeChecker_Env.trivial_guard,
                             FStar_Pervasives_Native.None, false)
                       | FStar_Pervasives_Native.Some edge ->
                           let uu___7 = lift_c1 edge in
                           (match uu___7 with
                            | (c12, g_lift) ->
                                let uu___8 =
                                  let uu___9 =
                                    let uu___10 =
                                      FStar_Compiler_Effect.op_Bar_Greater
                                        c21.FStar_Syntax_Syntax.effect_name
                                        (FStar_TypeChecker_Env.get_effect_decl
                                           env) in
                                    FStar_Compiler_Effect.op_Bar_Greater
                                      uu___10
                                      FStar_Syntax_Util.get_stronger_vc_combinator in
                                  FStar_Compiler_Effect.op_Bar_Greater uu___9
                                    (fun ts ->
                                       let uu___10 =
                                         let uu___11 =
                                           FStar_TypeChecker_Env.inst_tscheme_with
                                             ts
                                             c21.FStar_Syntax_Syntax.comp_univs in
                                         FStar_Compiler_Effect.op_Bar_Greater
                                           uu___11
                                           FStar_Pervasives_Native.snd in
                                       FStar_Compiler_Effect.op_Bar_Greater
                                         uu___10
                                         (fun uu___11 ->
                                            FStar_Pervasives_Native.Some
                                              uu___11)) in
                                (c12, g_lift, uu___8, false)))
                  | FStar_Pervasives_Native.Some t ->
                      let uu___6 =
                        let uu___7 =
                          let uu___8 =
                            FStar_TypeChecker_Env.inst_tscheme_with t
                              c21.FStar_Syntax_Syntax.comp_univs in
                          FStar_Compiler_Effect.op_Bar_Greater uu___8
                            FStar_Pervasives_Native.snd in
                        FStar_Compiler_Effect.op_Bar_Greater uu___7
                          (fun uu___8 -> FStar_Pervasives_Native.Some uu___8) in
                      (c11, FStar_TypeChecker_Env.trivial_guard, uu___6,
                        true) in
                match uu___4 with
                | (c12, g_lift, stronger_t_opt, is_polymonadic) ->
                    if FStar_Compiler_Util.is_none stronger_t_opt
                    then
                      let uu___5 =
                        mklstr
                          (fun uu___6 ->
                             let uu___7 =
                               FStar_Syntax_Print.lid_to_string
                                 c12.FStar_Syntax_Syntax.effect_name in
                             let uu___8 =
                               FStar_Syntax_Print.lid_to_string
                                 c21.FStar_Syntax_Syntax.effect_name in
                             FStar_Compiler_Util.format2
                               "incompatible monad ordering: %s </: %s"
                               uu___7 uu___8) in
                      giveup env uu___5 orig
                    else
                      (let stronger_t =
                         FStar_Compiler_Effect.op_Bar_Greater stronger_t_opt
                           FStar_Compiler_Util.must in
                       let wl1 =
                         extend_wl wl
                           g_lift.FStar_TypeChecker_Common.deferred
                           g_lift.FStar_TypeChecker_Common.deferred_to_tac
                           g_lift.FStar_TypeChecker_Common.implicits in
                       (let uu___7 =
                          ((is_polymonadic &&
                              (FStar_TypeChecker_Env.is_erasable_effect env
                                 c12.FStar_Syntax_Syntax.effect_name))
                             &&
                             (let uu___8 =
                                FStar_TypeChecker_Env.is_erasable_effect env
                                  c21.FStar_Syntax_Syntax.effect_name in
                              Prims.op_Negation uu___8))
                            &&
                            (let uu___8 =
                               FStar_TypeChecker_Normalize.non_info_norm env
                                 c12.FStar_Syntax_Syntax.result_typ in
                             Prims.op_Negation uu___8) in
                        if uu___7
                        then
                          let uu___8 =
                            let uu___9 =
                              let uu___10 =
                                FStar_Ident.string_of_lid
                                  c12.FStar_Syntax_Syntax.effect_name in
                              let uu___11 =
                                FStar_Ident.string_of_lid
                                  c21.FStar_Syntax_Syntax.effect_name in
                              let uu___12 =
                                FStar_Syntax_Print.term_to_string
                                  c12.FStar_Syntax_Syntax.result_typ in
                              FStar_Compiler_Util.format3
                                "Cannot lift erasable expression from %s ~> %s since its type %s is informative"
                                uu___10 uu___11 uu___12 in
                            (FStar_Errors.Error_TypeError, uu___9) in
                          FStar_Errors.raise_error uu___8 r
                        else ());
                       (let uu___7 =
                          if is_polymonadic
                          then ([], wl1)
                          else
                            (let rec is_uvar t =
                               let uu___9 =
                                 let uu___10 = FStar_Syntax_Subst.compress t in
                                 uu___10.FStar_Syntax_Syntax.n in
                               match uu___9 with
                               | FStar_Syntax_Syntax.Tm_uvar (uv, uu___10) ->
                                   let uu___11 =
                                     FStar_TypeChecker_DeferredImplicits.should_defer_uvar_to_user_tac
                                       env uv in
                                   Prims.op_Negation uu___11
                               | FStar_Syntax_Syntax.Tm_uinst (t1, uu___10)
                                   -> is_uvar t1
                               | FStar_Syntax_Syntax.Tm_app (t1, uu___10) ->
                                   is_uvar t1
                               | uu___10 -> false in
                             FStar_Compiler_List.fold_right2
                               (fun uu___9 ->
                                  fun uu___10 ->
                                    fun uu___11 ->
                                      match (uu___9, uu___10, uu___11) with
                                      | ((a1, uu___12), (a2, uu___13),
                                         (is_sub_probs, wl2)) ->
                                          let uu___14 = is_uvar a1 in
                                          if uu___14
                                          then
                                            ((let uu___16 =
                                                FStar_Compiler_Effect.op_Less_Bar
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  (FStar_Options.Other
                                                     "LayeredEffectsEqns") in
                                              if uu___16
                                              then
                                                let uu___17 =
                                                  FStar_Syntax_Print.term_to_string
                                                    a1 in
                                                let uu___18 =
                                                  FStar_Syntax_Print.term_to_string
                                                    a2 in
                                                FStar_Compiler_Util.print2
                                                  "Layered Effects teq (rel c1 index uvar) %s = %s\n"
                                                  uu___17 uu___18
                                              else ());
                                             (let uu___16 =
                                                sub_prob wl2 a1
                                                  FStar_TypeChecker_Common.EQ
                                                  a2
                                                  "l.h.s. effect index uvar" in
                                              match uu___16 with
                                              | (p, wl3) ->
                                                  ((p :: is_sub_probs), wl3)))
                                          else (is_sub_probs, wl2))
                               c12.FStar_Syntax_Syntax.effect_args
                               c21.FStar_Syntax_Syntax.effect_args ([], wl1)) in
                        match uu___7 with
                        | (is_sub_probs, wl2) ->
                            let uu___8 =
                              sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                                problem.FStar_TypeChecker_Common.relation
                                c21.FStar_Syntax_Syntax.result_typ
                                "result type" in
                            (match uu___8 with
                             | (ret_sub_prob, wl3) ->
                                 let stronger_t_shape_error s =
                                   let uu___9 =
                                     FStar_Ident.string_of_lid
                                       c21.FStar_Syntax_Syntax.effect_name in
                                   let uu___10 =
                                     FStar_Syntax_Print.term_to_string
                                       stronger_t in
                                   FStar_Compiler_Util.format3
                                     "Unexpected shape of stronger for %s, reason: %s (t:%s)"
                                     uu___9 s uu___10 in
                                 let uu___9 =
                                   let uu___10 =
                                     let uu___11 =
                                       FStar_Syntax_Subst.compress stronger_t in
                                     uu___11.FStar_Syntax_Syntax.n in
                                   match uu___10 with
                                   | FStar_Syntax_Syntax.Tm_arrow (bs, c)
                                       when
                                       (FStar_Compiler_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
                                       let uu___11 =
                                         FStar_Syntax_Subst.open_comp bs c in
                                       (match uu___11 with
                                        | (bs', c3) ->
                                            let a =
                                              FStar_Compiler_List.hd bs' in
                                            let bs1 =
                                              FStar_Compiler_List.tail bs' in
                                            let uu___12 =
                                              let uu___13 =
                                                FStar_Compiler_Effect.op_Bar_Greater
                                                  bs1
                                                  (FStar_Compiler_List.splitAt
                                                     ((FStar_Compiler_List.length
                                                         bs1)
                                                        - Prims.int_one)) in
                                              FStar_Compiler_Effect.op_Bar_Greater
                                                uu___13
                                                (fun uu___14 ->
                                                   match uu___14 with
                                                   | (l1, l2) ->
                                                       let uu___15 =
                                                         FStar_Compiler_List.hd
                                                           l2 in
                                                       (l1, uu___15)) in
                                            (match uu___12 with
                                             | (rest_bs, f_b) ->
                                                 (a, rest_bs, f_b, c3)))
                                   | uu___11 ->
                                       let uu___12 =
                                         let uu___13 =
                                           stronger_t_shape_error
                                             "not an arrow or not enough binders" in
                                         (FStar_Errors.Fatal_UnexpectedExpressionType,
                                           uu___13) in
                                       FStar_Errors.raise_error uu___12 r in
                                 (match uu___9 with
                                  | (a_b, rest_bs, f_b, stronger_c) ->
                                      let uu___10 =
                                        let guard_indexed_effect_uvars =
                                          false in
                                        FStar_TypeChecker_Env.uvars_for_binders
                                          env rest_bs
                                          [FStar_Syntax_Syntax.NT
                                             ((a_b.FStar_Syntax_Syntax.binder_bv),
                                               (c21.FStar_Syntax_Syntax.result_typ))]
                                          guard_indexed_effect_uvars
                                          (fun b ->
                                             let uu___11 =
                                               FStar_Syntax_Print.binder_to_string
                                                 b in
                                             let uu___12 =
                                               FStar_Ident.string_of_lid
                                                 c21.FStar_Syntax_Syntax.effect_name in
                                             let uu___13 =
                                               FStar_Compiler_Range.string_of_range
                                                 r in
                                             FStar_Compiler_Util.format3
                                               "implicit for binder %s in subcomp of %s at %s"
                                               uu___11 uu___12 uu___13) r in
                                      (match uu___10 with
                                       | (rest_bs_uvars,
                                          rest_uvars_guard_tms, g_uvars) ->
                                           let wl4 =
                                             {
                                               attempting = (wl3.attempting);
                                               wl_deferred =
                                                 (wl3.wl_deferred);
                                               wl_deferred_to_tac =
                                                 (wl3.wl_deferred_to_tac);
                                               ctr = (wl3.ctr);
                                               defer_ok = (wl3.defer_ok);
                                               smt_ok = (wl3.smt_ok);
                                               umax_heuristic_ok =
                                                 (wl3.umax_heuristic_ok);
                                               tcenv = (wl3.tcenv);
                                               wl_implicits =
                                                 (FStar_Compiler_List.op_At
                                                    g_uvars.FStar_TypeChecker_Common.implicits
                                                    wl3.wl_implicits);
                                               repr_subcomp_allowed =
                                                 (wl3.repr_subcomp_allowed)
                                             } in
                                           let substs =
                                             FStar_Compiler_List.map2
                                               (fun b ->
                                                  fun t ->
                                                    FStar_Syntax_Syntax.NT
                                                      ((b.FStar_Syntax_Syntax.binder_bv),
                                                        t)) (a_b :: rest_bs)
                                               ((c21.FStar_Syntax_Syntax.result_typ)
                                               :: rest_bs_uvars) in
                                           let uu___11 =
                                             let f_sort_is =
                                               let uu___12 =
                                                 let uu___13 =
                                                   FStar_TypeChecker_Env.is_layered_effect
                                                     env
                                                     c12.FStar_Syntax_Syntax.effect_name in
                                                 let uu___14 =
                                                   stronger_t_shape_error
                                                     "type of f is not a repr type" in
                                                 FStar_Syntax_Util.effect_indices_from_repr
                                                   (f_b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort
                                                   uu___13 r uu___14 in
                                               FStar_Compiler_Effect.op_Bar_Greater
                                                 uu___12
                                                 (FStar_Compiler_List.map
                                                    (FStar_Syntax_Subst.subst
                                                       substs)) in
                                             let uu___12 =
                                               FStar_Compiler_Effect.op_Bar_Greater
                                                 c12.FStar_Syntax_Syntax.effect_args
                                                 (FStar_Compiler_List.map
                                                    FStar_Pervasives_Native.fst) in
                                             FStar_Compiler_List.fold_left2
                                               (fun uu___13 ->
                                                  fun f_sort_i ->
                                                    fun c1_i ->
                                                      match uu___13 with
                                                      | (ps, wl5) ->
                                                          ((let uu___15 =
                                                              FStar_Compiler_Effect.op_Less_Bar
                                                                (FStar_TypeChecker_Env.debug
                                                                   env)
                                                                (FStar_Options.Other
                                                                   "LayeredEffectsEqns") in
                                                            if uu___15
                                                            then
                                                              let uu___16 =
                                                                FStar_Syntax_Print.term_to_string
                                                                  f_sort_i in
                                                              let uu___17 =
                                                                FStar_Syntax_Print.term_to_string
                                                                  c1_i in
                                                              FStar_Compiler_Util.print3
                                                                "Layered Effects (%s) %s = %s\n"
                                                                subcomp_name
                                                                uu___16
                                                                uu___17
                                                            else ());
                                                           (let uu___15 =
                                                              sub_prob wl5
                                                                f_sort_i
                                                                FStar_TypeChecker_Common.EQ
                                                                c1_i
                                                                "indices of c1" in
                                                            match uu___15
                                                            with
                                                            | (p, wl6) ->
                                                                ((FStar_Compiler_List.op_At
                                                                    ps 
                                                                    [p]),
                                                                  wl6))))
                                               ([], wl4) f_sort_is uu___12 in
                                           (match uu___11 with
                                            | (f_sub_probs, wl5) ->
                                                let stronger_ct =
                                                  let uu___12 =
                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                      stronger_c
                                                      (FStar_Syntax_Subst.subst_comp
                                                         substs) in
                                                  FStar_Compiler_Effect.op_Bar_Greater
                                                    uu___12
                                                    FStar_Syntax_Util.comp_to_comp_typ in
                                                let uu___12 =
                                                  let g_sort_is =
                                                    let uu___13 =
                                                      FStar_TypeChecker_Env.is_layered_effect
                                                        env
                                                        c21.FStar_Syntax_Syntax.effect_name in
                                                    let uu___14 =
                                                      stronger_t_shape_error
                                                        "subcomp return type is not a repr" in
                                                    FStar_Syntax_Util.effect_indices_from_repr
                                                      stronger_ct.FStar_Syntax_Syntax.result_typ
                                                      uu___13 r uu___14 in
                                                  let uu___13 =
                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                      c21.FStar_Syntax_Syntax.effect_args
                                                      (FStar_Compiler_List.map
                                                         FStar_Pervasives_Native.fst) in
                                                  FStar_Compiler_List.fold_left2
                                                    (fun uu___14 ->
                                                       fun g_sort_i ->
                                                         fun c2_i ->
                                                           match uu___14 with
                                                           | (ps, wl6) ->
                                                               ((let uu___16
                                                                   =
                                                                   FStar_Compiler_Effect.op_Less_Bar
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env)
                                                                    (FStar_Options.Other
                                                                    "LayeredEffectsEqns") in
                                                                 if uu___16
                                                                 then
                                                                   let uu___17
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    g_sort_i in
                                                                   let uu___18
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    c2_i in
                                                                   FStar_Compiler_Util.print3
                                                                    "Layered Effects (%s) %s = %s\n"
                                                                    subcomp_name
                                                                    uu___17
                                                                    uu___18
                                                                 else ());
                                                                (let uu___16
                                                                   =
                                                                   sub_prob
                                                                    wl6
                                                                    g_sort_i
                                                                    FStar_TypeChecker_Common.EQ
                                                                    c2_i
                                                                    "indices of c2" in
                                                                 match uu___16
                                                                 with
                                                                 | (p, wl7)
                                                                    ->
                                                                    ((FStar_Compiler_List.op_At
                                                                    ps [p]),
                                                                    wl7))))
                                                    ([], wl5) g_sort_is
                                                    uu___13 in
                                                (match uu___12 with
                                                 | (g_sub_probs, wl6) ->
                                                     let fml =
                                                       let uu___13 =
                                                         let uu___14 =
                                                           FStar_Compiler_List.hd
                                                             stronger_ct.FStar_Syntax_Syntax.comp_univs in
                                                         let uu___15 =
                                                           let uu___16 =
                                                             FStar_Compiler_List.hd
                                                               stronger_ct.FStar_Syntax_Syntax.effect_args in
                                                           FStar_Pervasives_Native.fst
                                                             uu___16 in
                                                         (uu___14, uu___15) in
                                                       match uu___13 with
                                                       | (u, wp) ->
                                                           FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                             env u
                                                             stronger_ct.FStar_Syntax_Syntax.result_typ
                                                             wp
                                                             FStar_Compiler_Range.dummyRange in
                                                     let sub_probs =
                                                       ret_sub_prob ::
                                                       (FStar_Compiler_List.op_At
                                                          is_sub_probs
                                                          (FStar_Compiler_List.op_At
                                                             f_sub_probs
                                                             g_sub_probs)) in
                                                     let guard =
                                                       let guard1 =
                                                         let uu___13 =
                                                           let uu___14 =
                                                             FStar_Compiler_List.map
                                                               p_guard
                                                               sub_probs in
                                                           FStar_Compiler_List.op_At
                                                             uu___14
                                                             rest_uvars_guard_tms in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu___13 in
                                                       match g_lift.FStar_TypeChecker_Common.guard_f
                                                       with
                                                       | FStar_TypeChecker_Common.Trivial
                                                           -> guard1
                                                       | FStar_TypeChecker_Common.NonTrivial
                                                           f ->
                                                           FStar_Syntax_Util.mk_conj
                                                             guard1 f in
                                                     let wl7 =
                                                       let uu___13 =
                                                         let uu___14 =
                                                           FStar_Syntax_Util.mk_conj
                                                             guard fml in
                                                         FStar_Compiler_Effect.op_Less_Bar
                                                           (fun uu___15 ->
                                                              FStar_Pervasives_Native.Some
                                                                uu___15)
                                                           uu___14 in
                                                       solve_prob orig
                                                         uu___13 [] wl6 in
                                                     let uu___13 =
                                                       attempt sub_probs wl7 in
                                                     solve env uu___13))))))))) in
        let solve_sub c11 edge c21 =
          if
            problem.FStar_TypeChecker_Common.relation <>
              FStar_TypeChecker_Common.SUB
          then failwith "impossible: solve_sub"
          else ();
          (let r = FStar_TypeChecker_Env.get_range env in
           let lift_c1 uu___1 =
             let univs =
               match c11.FStar_Syntax_Syntax.comp_univs with
               | [] ->
                   let uu___2 =
                     env.FStar_TypeChecker_Env.universe_of env
                       c11.FStar_Syntax_Syntax.result_typ in
                   [uu___2]
               | x -> x in
             let c12 =
               {
                 FStar_Syntax_Syntax.comp_univs = univs;
                 FStar_Syntax_Syntax.effect_name =
                   (c11.FStar_Syntax_Syntax.effect_name);
                 FStar_Syntax_Syntax.result_typ =
                   (c11.FStar_Syntax_Syntax.result_typ);
                 FStar_Syntax_Syntax.effect_args =
                   (c11.FStar_Syntax_Syntax.effect_args);
                 FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
               } in
             let guard_indexed_effect_uvars = true in
             let uu___2 =
               let uu___3 =
                 FStar_Compiler_Effect.op_Bar_Greater
                   {
                     FStar_Syntax_Syntax.comp_univs = univs;
                     FStar_Syntax_Syntax.effect_name =
                       (c12.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ =
                       (c12.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args =
                       (c12.FStar_Syntax_Syntax.effect_args);
                     FStar_Syntax_Syntax.flags =
                       (c12.FStar_Syntax_Syntax.flags)
                   } FStar_Syntax_Syntax.mk_Comp in
               FStar_Compiler_Effect.op_Bar_Greater uu___3
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env guard_indexed_effect_uvars) in
             FStar_Compiler_Effect.op_Bar_Greater uu___2
               (fun uu___3 ->
                  match uu___3 with
                  | (c, g) ->
                      let uu___4 =
                        let uu___5 = FStar_TypeChecker_Env.is_trivial g in
                        Prims.op_Negation uu___5 in
                      if uu___4
                      then
                        let uu___5 =
                          let uu___6 =
                            let uu___7 =
                              FStar_Ident.string_of_lid
                                c12.FStar_Syntax_Syntax.effect_name in
                            let uu___8 =
                              FStar_Ident.string_of_lid
                                c21.FStar_Syntax_Syntax.effect_name in
                            FStar_Compiler_Util.format2
                              "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                              uu___7 uu___8 in
                          (FStar_Errors.Fatal_UnexpectedEffect, uu___6) in
                        FStar_Errors.raise_error uu___5 r
                      else FStar_Syntax_Util.comp_to_comp_typ c) in
           let uu___1 =
             should_fail_since_repr_subcomp_not_allowed
               wl.repr_subcomp_allowed c11.FStar_Syntax_Syntax.effect_name
               c21.FStar_Syntax_Syntax.effect_name in
           if uu___1
           then
             let uu___2 =
               mklstr
                 (fun uu___3 ->
                    let uu___4 =
                      FStar_Ident.string_of_lid
                        c11.FStar_Syntax_Syntax.effect_name in
                    let uu___5 =
                      FStar_Ident.string_of_lid
                        c21.FStar_Syntax_Syntax.effect_name in
                    FStar_Compiler_Util.format2
                      "Cannot lift from %s to %s, it needs a lift\n" uu___4
                      uu___5) in
             giveup env uu___2 orig
           else
             (let is_null_wp_2 =
                FStar_Compiler_Effect.op_Bar_Greater
                  c21.FStar_Syntax_Syntax.flags
                  (FStar_Compiler_Util.for_some
                     (fun uu___3 ->
                        match uu___3 with
                        | FStar_Syntax_Syntax.TOTAL -> true
                        | FStar_Syntax_Syntax.MLEFFECT -> true
                        | FStar_Syntax_Syntax.SOMETRIVIAL -> true
                        | uu___4 -> false)) in
              let uu___3 =
                match ((c11.FStar_Syntax_Syntax.effect_args),
                        (c21.FStar_Syntax_Syntax.effect_args))
                with
                | ((wp1, uu___4)::uu___5, (wp2, uu___6)::uu___7) ->
                    (wp1, wp2)
                | uu___4 ->
                    let uu___5 =
                      let uu___6 =
                        let uu___7 =
                          FStar_Syntax_Print.lid_to_string
                            c11.FStar_Syntax_Syntax.effect_name in
                        let uu___8 =
                          FStar_Syntax_Print.lid_to_string
                            c21.FStar_Syntax_Syntax.effect_name in
                        FStar_Compiler_Util.format2
                          "Got effects %s and %s, expected normalized effects"
                          uu___7 uu___8 in
                      (FStar_Errors.Fatal_ExpectNormalizedEffect, uu___6) in
                    FStar_Errors.raise_error uu___5
                      env.FStar_TypeChecker_Env.range in
              match uu___3 with
              | (wpc1, wpc2) ->
                  let uu___4 =
                    FStar_Compiler_Util.physical_equality wpc1 wpc2 in
                  if uu___4
                  then
                    let uu___5 =
                      problem_using_guard orig
                        c11.FStar_Syntax_Syntax.result_typ
                        problem.FStar_TypeChecker_Common.relation
                        c21.FStar_Syntax_Syntax.result_typ
                        FStar_Pervasives_Native.None "result type" in
                    solve_t env uu___5 wl
                  else
                    (let uu___6 =
                       let uu___7 =
                         FStar_TypeChecker_Env.effect_decl_opt env
                           c21.FStar_Syntax_Syntax.effect_name in
                       FStar_Compiler_Util.must uu___7 in
                     match uu___6 with
                     | (c2_decl, qualifiers) ->
                         let uu___7 =
                           FStar_Compiler_Effect.op_Bar_Greater qualifiers
                             (FStar_Compiler_List.contains
                                FStar_Syntax_Syntax.Reifiable) in
                         if uu___7
                         then
                           let c1_repr =
                             let uu___8 =
                               let uu___9 =
                                 let uu___10 = lift_c1 () in
                                 FStar_Syntax_Syntax.mk_Comp uu___10 in
                               let uu___10 =
                                 env.FStar_TypeChecker_Env.universe_of env
                                   c11.FStar_Syntax_Syntax.result_typ in
                               FStar_TypeChecker_Env.reify_comp env uu___9
                                 uu___10 in
                             norm_with_steps
                               "FStar.TypeChecker.Rel.norm_with_steps.4"
                               [FStar_TypeChecker_Env.UnfoldUntil
                                  FStar_Syntax_Syntax.delta_constant;
                               FStar_TypeChecker_Env.Weak;
                               FStar_TypeChecker_Env.HNF] env uu___8 in
                           let c2_repr =
                             let uu___8 =
                               let uu___9 = FStar_Syntax_Syntax.mk_Comp c21 in
                               let uu___10 =
                                 env.FStar_TypeChecker_Env.universe_of env
                                   c21.FStar_Syntax_Syntax.result_typ in
                               FStar_TypeChecker_Env.reify_comp env uu___9
                                 uu___10 in
                             norm_with_steps
                               "FStar.TypeChecker.Rel.norm_with_steps.5"
                               [FStar_TypeChecker_Env.UnfoldUntil
                                  FStar_Syntax_Syntax.delta_constant;
                               FStar_TypeChecker_Env.Weak;
                               FStar_TypeChecker_Env.HNF] env uu___8 in
                           let uu___8 =
                             let uu___9 =
                               let uu___10 =
                                 FStar_Syntax_Print.term_to_string c1_repr in
                               let uu___11 =
                                 FStar_Syntax_Print.term_to_string c2_repr in
                               FStar_Compiler_Util.format2
                                 "sub effect repr: %s <: %s" uu___10 uu___11 in
                             sub_prob wl c1_repr
                               problem.FStar_TypeChecker_Common.relation
                               c2_repr uu___9 in
                           (match uu___8 with
                            | (prob, wl1) ->
                                let wl2 =
                                  solve_prob orig
                                    (FStar_Pervasives_Native.Some
                                       (p_guard prob)) [] wl1 in
                                let uu___9 = attempt [prob] wl2 in
                                solve env uu___9)
                         else
                           (let g =
                              if env.FStar_TypeChecker_Env.lax
                              then FStar_Syntax_Util.t_true
                              else
                                (let wpc1_2 =
                                   let uu___10 = lift_c1 () in
                                   FStar_Compiler_Effect.op_Bar_Greater
                                     uu___10
                                     (fun ct ->
                                        FStar_Compiler_List.hd
                                          ct.FStar_Syntax_Syntax.effect_args) in
                                 if is_null_wp_2
                                 then
                                   ((let uu___11 =
                                       FStar_Compiler_Effect.op_Less_Bar
                                         (FStar_TypeChecker_Env.debug env)
                                         (FStar_Options.Other "Rel") in
                                     if uu___11
                                     then
                                       FStar_Compiler_Util.print_string
                                         "Using trivial wp ... \n"
                                     else ());
                                    (let c1_univ =
                                       env.FStar_TypeChecker_Env.universe_of
                                         env
                                         c11.FStar_Syntax_Syntax.result_typ in
                                     let trivial =
                                       let uu___11 =
                                         FStar_Compiler_Effect.op_Bar_Greater
                                           c2_decl
                                           FStar_Syntax_Util.get_wp_trivial_combinator in
                                       match uu___11 with
                                       | FStar_Pervasives_Native.None ->
                                           failwith
                                             "Rel doesn't yet handle undefined trivial combinator in an effect"
                                       | FStar_Pervasives_Native.Some t -> t in
                                     let uu___11 =
                                       let uu___12 =
                                         let uu___13 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl trivial in
                                         let uu___14 =
                                           let uu___15 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           [uu___15; wpc1_2] in
                                         (uu___13, uu___14) in
                                       FStar_Syntax_Syntax.Tm_app uu___12 in
                                     FStar_Syntax_Syntax.mk uu___11 r))
                                 else
                                   (let c2_univ =
                                      env.FStar_TypeChecker_Env.universe_of
                                        env
                                        c21.FStar_Syntax_Syntax.result_typ in
                                    let stronger =
                                      FStar_Compiler_Effect.op_Bar_Greater
                                        c2_decl
                                        FStar_Syntax_Util.get_stronger_vc_combinator in
                                    let uu___11 =
                                      let uu___12 =
                                        let uu___13 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl stronger in
                                        let uu___14 =
                                          let uu___15 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu___16 =
                                            let uu___17 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            [uu___17; wpc1_2] in
                                          uu___15 :: uu___16 in
                                        (uu___13, uu___14) in
                                      FStar_Syntax_Syntax.Tm_app uu___12 in
                                    FStar_Syntax_Syntax.mk uu___11 r)) in
                            (let uu___10 =
                               FStar_Compiler_Effect.op_Less_Bar
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu___10
                             then
                               let uu___11 =
                                 let uu___12 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.Iota;
                                     FStar_TypeChecker_Env.Eager_unfolding;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.Simplify] env g in
                                 FStar_Syntax_Print.term_to_string uu___12 in
                               FStar_Compiler_Util.print1
                                 "WP guard (simplifed) is (%s)\n" uu___11
                             else ());
                            (let uu___10 =
                               sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             match uu___10 with
                             | (base_prob, wl1) ->
                                 let wl2 =
                                   let uu___11 =
                                     let uu___12 =
                                       FStar_Syntax_Util.mk_conj
                                         (p_guard base_prob) g in
                                     FStar_Compiler_Effect.op_Less_Bar
                                       (fun uu___13 ->
                                          FStar_Pervasives_Native.Some
                                            uu___13) uu___12 in
                                   solve_prob orig uu___11 [] wl1 in
                                 let uu___11 = attempt [base_prob] wl2 in
                                 solve env uu___11))))) in
        let uu___ = FStar_Compiler_Util.physical_equality c1 c2 in
        if uu___
        then
          let uu___1 = solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu___1
        else
          ((let uu___3 =
              FStar_Compiler_Effect.op_Less_Bar
                (FStar_TypeChecker_Env.debug env) (FStar_Options.Other "Rel") in
            if uu___3
            then
              let uu___4 = FStar_Syntax_Print.comp_to_string c1 in
              let uu___5 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Compiler_Util.print3 "solve_c %s %s %s\n" uu___4
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu___5
            else ());
           (let uu___3 =
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    FStar_Compiler_Effect.op_Bar_Greater c1
                      FStar_Syntax_Util.comp_effect_name in
                  FStar_Compiler_Effect.op_Bar_Greater uu___6
                    (FStar_TypeChecker_Env.norm_eff_name env) in
                let uu___6 =
                  let uu___7 =
                    FStar_Compiler_Effect.op_Bar_Greater c2
                      FStar_Syntax_Util.comp_effect_name in
                  FStar_Compiler_Effect.op_Bar_Greater uu___7
                    (FStar_TypeChecker_Env.norm_eff_name env) in
                (uu___5, uu___6) in
              match uu___4 with
              | (eff1, eff2) ->
                  let uu___5 = FStar_Ident.lid_equals eff1 eff2 in
                  if uu___5
                  then (c1, c2)
                  else
                    FStar_TypeChecker_Normalize.ghost_to_pure2 env (c1, c2) in
            match uu___3 with
            | (c11, c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal (t1, uu___4),
                    FStar_Syntax_Syntax.Total (t2, uu___5)) when
                     FStar_TypeChecker_Env.non_informative env t2 ->
                     let uu___6 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu___6 wl
                 | (FStar_Syntax_Syntax.GTotal uu___4,
                    FStar_Syntax_Syntax.Total uu___5) ->
                     let uu___6 =
                       FStar_Thunk.mkv
                         "incompatible monad ordering: GTot </: Tot" in
                     giveup env uu___6 orig
                 | (FStar_Syntax_Syntax.Total (t1, uu___4),
                    FStar_Syntax_Syntax.Total (t2, uu___5)) ->
                     let uu___6 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu___6 wl
                 | (FStar_Syntax_Syntax.GTotal (t1, uu___4),
                    FStar_Syntax_Syntax.GTotal (t2, uu___5)) ->
                     let uu___6 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu___6 wl
                 | (FStar_Syntax_Syntax.Total (t1, uu___4),
                    FStar_Syntax_Syntax.GTotal (t2, uu___5)) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.SUB
                     ->
                     let uu___6 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu___6 wl
                 | (FStar_Syntax_Syntax.Total (t1, uu___4),
                    FStar_Syntax_Syntax.GTotal (t2, uu___5)) ->
                     let uu___6 = FStar_Thunk.mkv "GTot =/= Tot" in
                     giveup env uu___6 orig
                 | (FStar_Syntax_Syntax.GTotal uu___4,
                    FStar_Syntax_Syntax.Comp uu___5) ->
                     let uu___6 =
                       let uu___7 =
                         let uu___8 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_Compiler_Effect.op_Less_Bar
                           FStar_Syntax_Syntax.mk_Comp uu___8 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (problem.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu___7;
                         FStar_TypeChecker_Common.relation =
                           (problem.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (problem.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (problem.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (problem.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (problem.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (problem.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (problem.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (problem.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu___6 wl
                 | (FStar_Syntax_Syntax.Total uu___4,
                    FStar_Syntax_Syntax.Comp uu___5) ->
                     let uu___6 =
                       let uu___7 =
                         let uu___8 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_Compiler_Effect.op_Less_Bar
                           FStar_Syntax_Syntax.mk_Comp uu___8 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (problem.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu___7;
                         FStar_TypeChecker_Common.relation =
                           (problem.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (problem.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (problem.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (problem.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (problem.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (problem.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (problem.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (problem.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu___6 wl
                 | (FStar_Syntax_Syntax.Comp uu___4,
                    FStar_Syntax_Syntax.GTotal uu___5) ->
                     let uu___6 =
                       let uu___7 =
                         let uu___8 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_Compiler_Effect.op_Less_Bar
                           FStar_Syntax_Syntax.mk_Comp uu___8 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (problem.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (problem.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (problem.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu___7;
                         FStar_TypeChecker_Common.element =
                           (problem.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (problem.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (problem.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (problem.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (problem.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (problem.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu___6 wl
                 | (FStar_Syntax_Syntax.Comp uu___4,
                    FStar_Syntax_Syntax.Total uu___5) ->
                     let uu___6 =
                       let uu___7 =
                         let uu___8 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_Compiler_Effect.op_Less_Bar
                           FStar_Syntax_Syntax.mk_Comp uu___8 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (problem.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (problem.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (problem.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu___7;
                         FStar_TypeChecker_Common.element =
                           (problem.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (problem.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (problem.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (problem.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (problem.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (problem.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu___6 wl
                 | (FStar_Syntax_Syntax.Comp uu___4, FStar_Syntax_Syntax.Comp
                    uu___5) ->
                     let uu___6 =
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
                               FStar_TypeChecker_Common.SUB)) in
                     if uu___6
                     then
                       let uu___7 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type" in
                       solve_t env uu___7 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu___8 =
                            let uu___9 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name in
                            if uu___9
                            then (c1_comp, c2_comp)
                            else
                              (let uu___11 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11 in
                               let uu___12 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21 in
                               (uu___11, uu___12)) in
                          match uu___8 with
                          | (c1_comp1, c2_comp1) ->
                              solve_eq c1_comp1 c2_comp1
                                FStar_TypeChecker_Env.trivial_guard
                        else
                          (let c12 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c11 in
                           let c22 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c21 in
                           (let uu___10 =
                              FStar_Compiler_Effect.op_Less_Bar
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu___10
                            then
                              let uu___11 =
                                FStar_Ident.string_of_lid
                                  c12.FStar_Syntax_Syntax.effect_name in
                              let uu___12 =
                                FStar_Ident.string_of_lid
                                  c22.FStar_Syntax_Syntax.effect_name in
                              FStar_Compiler_Util.print2
                                "solve_c for %s and %s\n" uu___11 uu___12
                            else ());
                           (let uu___10 =
                              FStar_TypeChecker_Env.is_layered_effect env
                                c22.FStar_Syntax_Syntax.effect_name in
                            if uu___10
                            then solve_layered_sub c12 c22
                            else
                              (let uu___12 =
                                 FStar_TypeChecker_Env.monad_leq env
                                   c12.FStar_Syntax_Syntax.effect_name
                                   c22.FStar_Syntax_Syntax.effect_name in
                               match uu___12 with
                               | FStar_Pervasives_Native.None ->
                                   let uu___13 =
                                     mklstr
                                       (fun uu___14 ->
                                          let uu___15 =
                                            FStar_Syntax_Print.lid_to_string
                                              c12.FStar_Syntax_Syntax.effect_name in
                                          let uu___16 =
                                            FStar_Syntax_Print.lid_to_string
                                              c22.FStar_Syntax_Syntax.effect_name in
                                          FStar_Compiler_Util.format2
                                            "incompatible monad ordering: %s </: %s"
                                            uu___15 uu___16) in
                                   giveup env uu___13 orig
                               | FStar_Pervasives_Native.Some edge ->
                                   solve_sub c12 edge c22)))))))
let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g ->
    let uu___ =
      FStar_Compiler_Effect.op_Bar_Greater
        g.FStar_TypeChecker_Common.implicits
        (FStar_Compiler_List.map
           (fun i ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm)) in
    FStar_Compiler_Effect.op_Bar_Greater uu___ (FStar_String.concat ", ")
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs ->
    let vars =
      let uu___ =
        FStar_Compiler_Effect.op_Bar_Greater
          (FStar_Pervasives_Native.fst ineqs)
          (FStar_Compiler_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_Compiler_Effect.op_Bar_Greater uu___ (FStar_String.concat ", ") in
    let ineqs1 =
      let uu___ =
        FStar_Compiler_Effect.op_Bar_Greater
          (FStar_Pervasives_Native.snd ineqs)
          (FStar_Compiler_List.map
             (fun uu___1 ->
                match uu___1 with
                | (u1, u2) ->
                    let uu___2 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu___3 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Compiler_Util.format2 "%s < %s" uu___2 uu___3)) in
      FStar_Compiler_Effect.op_Bar_Greater uu___ (FStar_String.concat ", ") in
    FStar_Compiler_Util.format2 "Solving for {%s}; inequalities are {%s}"
      vars ineqs1
let (guard_to_string :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> Prims.string)
  =
  fun env ->
    fun g ->
      match ((g.FStar_TypeChecker_Common.guard_f),
              (g.FStar_TypeChecker_Common.deferred),
              (g.FStar_TypeChecker_Common.univ_ineqs))
      with
      | (FStar_TypeChecker_Common.Trivial, [], (uu___, [])) when
          let uu___1 = FStar_Options.print_implicits () in
          Prims.op_Negation uu___1 -> "{}"
      | uu___ ->
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu___1 =
                  ((FStar_Compiler_Effect.op_Less_Bar
                      (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_Compiler_Effect.op_Less_Bar
                        (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ()) in
                if uu___1
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry defs =
            let uu___1 =
              FStar_Compiler_List.map
                (fun uu___2 ->
                   match uu___2 with
                   | (uu___3, msg, x) ->
                       let uu___4 =
                         let uu___5 = prob_to_string env x in
                         Prims.op_Hat ": " uu___5 in
                       Prims.op_Hat msg uu___4) defs in
            FStar_Compiler_Effect.op_Bar_Greater uu___1
              (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu___1 = carry g.FStar_TypeChecker_Common.deferred in
          let uu___2 = carry g.FStar_TypeChecker_Common.deferred_to_tac in
          let uu___3 = ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs in
          FStar_Compiler_Util.format5
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t deferred_to_tac={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form uu___1 uu___2 uu___3 imps
let (new_t_problem :
  worklist ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
              FStar_Compiler_Range.range ->
                (FStar_TypeChecker_Common.prob * worklist))
  =
  fun wl ->
    fun env ->
      fun lhs ->
        fun rel ->
          fun rhs ->
            fun elt ->
              fun loc ->
                let reason =
                  let uu___ =
                    (FStar_Compiler_Effect.op_Less_Bar
                       (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_Compiler_Effect.op_Less_Bar
                         (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel")) in
                  if uu___
                  then
                    let uu___1 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs in
                    let uu___2 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs in
                    FStar_Compiler_Util.format3 "Top-level:\n%s\n\t%s\n%s"
                      uu___1 (rel_to_string rel) uu___2
                  else "TOP" in
                let uu___ = new_problem wl env lhs rel rhs elt loc reason in
                match uu___ with
                | (p, wl1) ->
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
  fun wl ->
    fun env ->
      fun t1 ->
        fun rel ->
          fun t2 ->
            let x =
              let uu___ =
                let uu___1 = FStar_TypeChecker_Env.get_range env in
                FStar_Compiler_Effect.op_Less_Bar
                  (fun uu___2 -> FStar_Pervasives_Native.Some uu___2) uu___1 in
              FStar_Syntax_Syntax.new_bv uu___ t1 in
            let uu___ =
              let uu___1 = FStar_TypeChecker_Env.get_range env in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu___1 in
            match uu___ with | (p, wl1) -> (p, x, wl1)
let (solve_and_commit :
  FStar_TypeChecker_Env.env ->
    worklist ->
      ((FStar_TypeChecker_Common.prob * lstring) ->
         (FStar_TypeChecker_Common.deferred *
           FStar_TypeChecker_Common.deferred *
           FStar_TypeChecker_Common.implicits) FStar_Pervasives_Native.option)
        ->
        (FStar_TypeChecker_Common.deferred *
          FStar_TypeChecker_Common.deferred *
          FStar_TypeChecker_Common.implicits) FStar_Pervasives_Native.option)
  =
  fun env ->
    fun wl ->
      fun err ->
        let tx = FStar_Syntax_Unionfind.new_transaction () in
        (let uu___1 =
           FStar_Compiler_Effect.op_Less_Bar
             (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench") in
         if uu___1
         then
           let uu___2 =
             FStar_Common.string_of_list
               (fun p -> FStar_Compiler_Util.string_of_int (p_pid p))
               wl.attempting in
           FStar_Compiler_Util.print1 "solving problems %s {\n" uu___2
         else ());
        (let uu___1 =
           FStar_Compiler_Util.record_time (fun uu___2 -> solve env wl) in
         match uu___1 with
         | (sol, ms) ->
             ((let uu___3 =
                 FStar_Compiler_Effect.op_Less_Bar
                   (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench") in
               if uu___3
               then
                 let uu___4 = FStar_Compiler_Util.string_of_int ms in
                 FStar_Compiler_Util.print1 "} solved in %s ms\n" uu___4
               else ());
              (match sol with
               | Success (deferred, defer_to_tac, implicits) ->
                   let uu___3 =
                     FStar_Compiler_Util.record_time
                       (fun uu___4 -> FStar_Syntax_Unionfind.commit tx) in
                   (match uu___3 with
                    | ((), ms1) ->
                        ((let uu___5 =
                            FStar_Compiler_Effect.op_Less_Bar
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench") in
                          if uu___5
                          then
                            let uu___6 =
                              FStar_Compiler_Util.string_of_int ms1 in
                            FStar_Compiler_Util.print1 "committed in %s ms\n"
                              uu___6
                          else ());
                         FStar_Pervasives_Native.Some
                           (deferred, defer_to_tac, implicits)))
               | Failed (d, s) ->
                   ((let uu___4 =
                       (FStar_Compiler_Effect.op_Less_Bar
                          (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_Compiler_Effect.op_Less_Bar
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel")) in
                     if uu___4
                     then
                       let uu___5 = explain env d s in
                       FStar_Compiler_Effect.op_Less_Bar
                         FStar_Compiler_Util.print_string uu___5
                     else ());
                    (let result = err (d, s) in
                     FStar_Syntax_Unionfind.rollback tx; result)))))
let (with_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Common.deferred
        * FStar_TypeChecker_Common.implicits) FStar_Pervasives_Native.option
        -> FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env ->
    fun prob ->
      fun dopt ->
        match dopt with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (deferred, defer_to_tac, implicits) ->
            let uu___ =
              let uu___1 =
                let uu___2 =
                  FStar_Compiler_Effect.op_Bar_Greater (p_guard prob)
                    (fun uu___3 -> FStar_TypeChecker_Common.NonTrivial uu___3) in
                {
                  FStar_TypeChecker_Common.guard_f = uu___2;
                  FStar_TypeChecker_Common.deferred_to_tac = defer_to_tac;
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                } in
              simplify_guard env uu___1 in
            FStar_Compiler_Effect.op_Less_Bar
              (fun uu___1 -> FStar_Pervasives_Native.Some uu___1) uu___
let (try_teq :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun smt_ok ->
    fun env ->
      fun t1 ->
        fun t2 ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_TypeChecker_Env.current_module env in
              FStar_Ident.string_of_lid uu___2 in
            FStar_Pervasives_Native.Some uu___1 in
          FStar_Profiling.profile
            (fun uu___1 ->
               (let uu___3 =
                  FStar_Compiler_Effect.op_Less_Bar
                    (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel") in
                if uu___3
                then
                  let uu___4 = FStar_Syntax_Print.term_to_string t1 in
                  let uu___5 = FStar_Syntax_Print.term_to_string t2 in
                  let uu___6 =
                    FStar_TypeChecker_Env.print_gamma
                      env.FStar_TypeChecker_Env.gamma in
                  FStar_Compiler_Util.print3 "try_teq of %s and %s in %s {\n"
                    uu___4 uu___5 uu___6
                else ());
               (let uu___3 =
                  let uu___4 = FStar_TypeChecker_Env.get_range env in
                  new_t_problem (empty_worklist env) env t1
                    FStar_TypeChecker_Common.EQ t2
                    FStar_Pervasives_Native.None uu___4 in
                match uu___3 with
                | (prob, wl) ->
                    let g =
                      let uu___4 =
                        solve_and_commit env (singleton wl prob smt_ok)
                          (fun uu___5 -> FStar_Pervasives_Native.None) in
                      FStar_Compiler_Effect.op_Less_Bar (with_guard env prob)
                        uu___4 in
                    ((let uu___5 =
                        FStar_Compiler_Effect.op_Less_Bar
                          (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel") in
                      if uu___5
                      then
                        let uu___6 =
                          FStar_Common.string_of_option (guard_to_string env)
                            g in
                        FStar_Compiler_Util.print1 "} res = %s\n" uu___6
                      else ());
                     g))) uu___ "FStar.TypeChecker.Rel.try_teq"
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu___ = try_teq true env t1 t2 in
        match uu___ with
        | FStar_Pervasives_Native.None ->
            ((let uu___2 = FStar_TypeChecker_Env.get_range env in
              let uu___3 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1 in
              FStar_Errors.log_issue uu___2 uu___3);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu___2 =
                FStar_Compiler_Effect.op_Less_Bar
                  (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu___2
              then
                let uu___3 = FStar_Syntax_Print.term_to_string t1 in
                let uu___4 = FStar_Syntax_Print.term_to_string t2 in
                let uu___5 = guard_to_string env g in
                FStar_Compiler_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu___3 uu___4
                  uu___5
              else ());
             g)
let (get_teq_predicate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        (let uu___1 =
           FStar_Compiler_Effect.op_Less_Bar
             (FStar_TypeChecker_Env.debug env) (FStar_Options.Other "Rel") in
         if uu___1
         then
           let uu___2 = FStar_Syntax_Print.term_to_string t1 in
           let uu___3 = FStar_Syntax_Print.term_to_string t2 in
           FStar_Compiler_Util.print2 "get_teq_predicate of %s and %s {\n"
             uu___2 uu___3
         else ());
        (let uu___1 =
           new_t_prob (empty_worklist env) env t1 FStar_TypeChecker_Common.EQ
             t2 in
         match uu___1 with
         | (prob, x, wl) ->
             let g =
               let uu___2 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu___3 -> FStar_Pervasives_Native.None) in
               FStar_Compiler_Effect.op_Less_Bar (with_guard env prob) uu___2 in
             ((let uu___3 =
                 FStar_Compiler_Effect.op_Less_Bar
                   (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel") in
               if uu___3
               then
                 let uu___4 =
                   FStar_Common.string_of_option (guard_to_string env) g in
                 FStar_Compiler_Util.print1 "} res teq predicate = %s\n"
                   uu___4
               else ());
              (match g with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   let uu___3 =
                     let uu___4 = FStar_Syntax_Syntax.mk_binder x in
                     FStar_TypeChecker_Env.abstract_guard uu___4 g1 in
                   FStar_Pervasives_Native.Some uu___3)))
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env ->
    fun e ->
      fun t1 ->
        fun t2 ->
          let uu___ = FStar_TypeChecker_Env.get_range env in
          let uu___1 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1 in
          FStar_Errors.log_issue uu___ uu___1
let (sub_or_eq_comp :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.comp ->
          FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env ->
    fun use_eq ->
      fun c1 ->
        fun c2 ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_TypeChecker_Env.current_module env in
              FStar_Ident.string_of_lid uu___2 in
            FStar_Pervasives_Native.Some uu___1 in
          FStar_Profiling.profile
            (fun uu___1 ->
               let rel =
                 if use_eq
                 then FStar_TypeChecker_Common.EQ
                 else FStar_TypeChecker_Common.SUB in
               (let uu___3 =
                  FStar_Compiler_Effect.op_Less_Bar
                    (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel") in
                if uu___3
                then
                  let uu___4 = FStar_Syntax_Print.comp_to_string c1 in
                  let uu___5 = FStar_Syntax_Print.comp_to_string c2 in
                  FStar_Compiler_Util.print3
                    "sub_comp of %s --and-- %s --with-- %s\n" uu___4 uu___5
                    (if rel = FStar_TypeChecker_Common.EQ
                     then "EQ"
                     else "SUB")
                else ());
               (let uu___3 =
                  let uu___4 = FStar_TypeChecker_Env.get_range env in
                  new_problem (empty_worklist env) env c1 rel c2
                    FStar_Pervasives_Native.None uu___4 "sub_comp" in
                match uu___3 with
                | (prob, wl) ->
                    let wl1 =
                      {
                        attempting = (wl.attempting);
                        wl_deferred = (wl.wl_deferred);
                        wl_deferred_to_tac = (wl.wl_deferred_to_tac);
                        ctr = (wl.ctr);
                        defer_ok = (wl.defer_ok);
                        smt_ok = (wl.smt_ok);
                        umax_heuristic_ok = (wl.umax_heuristic_ok);
                        tcenv = (wl.tcenv);
                        wl_implicits = (wl.wl_implicits);
                        repr_subcomp_allowed = true
                      } in
                    let prob1 = FStar_TypeChecker_Common.CProb prob in
                    (def_check_prob "sub_comp" prob1;
                     (let uu___5 =
                        FStar_Compiler_Util.record_time
                          (fun uu___6 ->
                             let uu___7 =
                               solve_and_commit env
                                 (singleton wl1 prob1 true)
                                 (fun uu___8 -> FStar_Pervasives_Native.None) in
                             FStar_Compiler_Effect.op_Less_Bar
                               (with_guard env prob1) uu___7) in
                      match uu___5 with
                      | (r, ms) ->
                          ((let uu___7 =
                              FStar_Compiler_Effect.op_Less_Bar
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "RelBench") in
                            if uu___7
                            then
                              let uu___8 =
                                FStar_Syntax_Print.comp_to_string c1 in
                              let uu___9 =
                                FStar_Syntax_Print.comp_to_string c2 in
                              let uu___10 =
                                FStar_Compiler_Util.string_of_int ms in
                              FStar_Compiler_Util.print4
                                "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                                uu___8 uu___9
                                (if rel = FStar_TypeChecker_Common.EQ
                                 then "EQ"
                                 else "SUB") uu___10
                            else ());
                           r))))) uu___ "FStar.TypeChecker.Rel.sub_comp"
let (sub_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  = fun env -> fun c1 -> fun c2 -> sub_or_eq_comp env false c1 c2
let (eq_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  = fun env -> fun c1 -> fun c2 -> sub_or_eq_comp env true c1 c2
let (solve_universe_inequalities' :
  FStar_Syntax_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list *
        (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe)
        Prims.list) -> unit)
  =
  fun tx ->
    fun env ->
      fun uu___ ->
        match uu___ with
        | (variables, ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu___2 =
                 let uu___3 =
                   let uu___4 = FStar_Syntax_Print.univ_to_string u1 in
                   let uu___5 = FStar_Syntax_Print.univ_to_string u2 in
                   FStar_Compiler_Util.format2
                     "Universe %s and %s are incompatible" uu___4 uu___5 in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu___3) in
               let uu___3 = FStar_TypeChecker_Env.get_range env in
               FStar_Errors.raise_error uu___2 uu___3) in
            let equiv v v' =
              let uu___1 =
                let uu___2 = FStar_Syntax_Subst.compress_univ v in
                let uu___3 = FStar_Syntax_Subst.compress_univ v' in
                (uu___2, uu___3) in
              match uu___1 with
              | (FStar_Syntax_Syntax.U_unif v0, FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu___2 -> false in
            let sols =
              FStar_Compiler_Effect.op_Bar_Greater variables
                (FStar_Compiler_List.collect
                   (fun v ->
                      let uu___1 = FStar_Syntax_Subst.compress_univ v in
                      match uu___1 with
                      | FStar_Syntax_Syntax.U_unif uu___2 ->
                          let lower_bounds_of_v =
                            FStar_Compiler_Effect.op_Bar_Greater ineqs
                              (FStar_Compiler_List.collect
                                 (fun uu___3 ->
                                    match uu___3 with
                                    | (u, v') ->
                                        let uu___4 = equiv v v' in
                                        if uu___4
                                        then
                                          let uu___5 =
                                            FStar_Compiler_Effect.op_Bar_Greater
                                              variables
                                              (FStar_Compiler_Util.for_some
                                                 (equiv u)) in
                                          (if uu___5 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v)]
                      | uu___2 -> [])) in
            let uu___1 =
              let wl =
                let uu___2 = empty_worklist env in
                {
                  attempting = (uu___2.attempting);
                  wl_deferred = (uu___2.wl_deferred);
                  wl_deferred_to_tac = (uu___2.wl_deferred_to_tac);
                  ctr = (uu___2.ctr);
                  defer_ok = NoDefer;
                  smt_ok = (uu___2.smt_ok);
                  umax_heuristic_ok = (uu___2.umax_heuristic_ok);
                  tcenv = (uu___2.tcenv);
                  wl_implicits = (uu___2.wl_implicits);
                  repr_subcomp_allowed = (uu___2.repr_subcomp_allowed)
                } in
              FStar_Compiler_Effect.op_Bar_Greater sols
                (FStar_Compiler_List.map
                   (fun uu___2 ->
                      match uu___2 with
                      | (lb, v) ->
                          let uu___3 =
                            solve_universe_eq (~- Prims.int_one) wl lb v in
                          (match uu___3 with
                           | USolved wl1 -> ()
                           | uu___4 -> fail lb v))) in
            let rec check_ineq uu___2 =
              match uu___2 with
              | (u, v) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v1 =
                    FStar_TypeChecker_Normalize.normalize_universe env v in
                  (match (u1, v1) with
                   | (FStar_Syntax_Syntax.U_zero, uu___3) -> true
                   | (FStar_Syntax_Syntax.U_succ u0,
                      FStar_Syntax_Syntax.U_succ v0) -> check_ineq (u0, v0)
                   | (FStar_Syntax_Syntax.U_name u0,
                      FStar_Syntax_Syntax.U_name v0) ->
                       FStar_Ident.ident_equals u0 v0
                   | (FStar_Syntax_Syntax.U_unif u0,
                      FStar_Syntax_Syntax.U_unif v0) ->
                       FStar_Syntax_Unionfind.univ_equiv u0 v0
                   | (FStar_Syntax_Syntax.U_name uu___3,
                      FStar_Syntax_Syntax.U_succ v0) -> check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif uu___3,
                      FStar_Syntax_Syntax.U_succ v0) -> check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us, uu___3) ->
                       FStar_Compiler_Effect.op_Bar_Greater us
                         (FStar_Compiler_Util.for_all
                            (fun u2 -> check_ineq (u2, v1)))
                   | (uu___3, FStar_Syntax_Syntax.U_max vs) ->
                       FStar_Compiler_Effect.op_Bar_Greater vs
                         (FStar_Compiler_Util.for_some
                            (fun v2 -> check_ineq (u1, v2)))
                   | uu___3 -> false) in
            let uu___2 =
              FStar_Compiler_Effect.op_Bar_Greater ineqs
                (FStar_Compiler_Util.for_all
                   (fun uu___3 ->
                      match uu___3 with
                      | (u, v) ->
                          let uu___4 = check_ineq (u, v) in
                          if uu___4
                          then true
                          else
                            ((let uu___7 =
                                FStar_Compiler_Effect.op_Less_Bar
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu___7
                              then
                                let uu___8 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu___9 =
                                  FStar_Syntax_Print.univ_to_string v in
                                FStar_Compiler_Util.print2 "%s </= %s" uu___8
                                  uu___9
                              else ());
                             false))) in
            if uu___2
            then ()
            else
              ((let uu___5 =
                  FStar_Compiler_Effect.op_Less_Bar
                    (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu___5
                then
                  ((let uu___7 = ineqs_to_string (variables, ineqs) in
                    FStar_Compiler_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu___7);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu___8 = ineqs_to_string (variables, ineqs) in
                    FStar_Compiler_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu___8))
                else ());
               (let uu___5 = FStar_TypeChecker_Env.get_range env in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu___5))
let (solve_universe_inequalities :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe
      * FStar_Syntax_Syntax.universe) Prims.list) -> unit)
  =
  fun env ->
    fun ineqs ->
      let tx = FStar_Syntax_Unionfind.new_transaction () in
      solve_universe_inequalities' tx env ineqs;
      FStar_Syntax_Unionfind.commit tx
let (try_solve_deferred_constraints :
  defer_ok_t ->
    Prims.bool ->
      Prims.bool ->
        FStar_TypeChecker_Env.env ->
          FStar_TypeChecker_Common.guard_t ->
            FStar_TypeChecker_Common.guard_t)
  =
  fun defer_ok ->
    fun smt_ok ->
      fun deferred_to_tac_ok ->
        fun env ->
          fun g ->
            let uu___ =
              let uu___1 =
                let uu___2 = FStar_TypeChecker_Env.current_module env in
                FStar_Ident.string_of_lid uu___2 in
              FStar_Pervasives_Native.Some uu___1 in
            FStar_Profiling.profile
              (fun uu___1 ->
                 let fail uu___2 =
                   match uu___2 with
                   | (d, s) ->
                       let msg = explain env d s in
                       FStar_Errors.raise_error
                         (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints,
                           msg) (p_loc d) in
                 let wl =
                   let uu___2 =
                     wl_of_guard env g.FStar_TypeChecker_Common.deferred in
                   {
                     attempting = (uu___2.attempting);
                     wl_deferred = (uu___2.wl_deferred);
                     wl_deferred_to_tac = (uu___2.wl_deferred_to_tac);
                     ctr = (uu___2.ctr);
                     defer_ok;
                     smt_ok;
                     umax_heuristic_ok = (uu___2.umax_heuristic_ok);
                     tcenv = (uu___2.tcenv);
                     wl_implicits = (uu___2.wl_implicits);
                     repr_subcomp_allowed = (uu___2.repr_subcomp_allowed)
                   } in
                 (let uu___3 =
                    FStar_Compiler_Effect.op_Less_Bar
                      (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel") in
                  if uu___3
                  then
                    let uu___4 =
                      FStar_Compiler_Util.string_of_bool deferred_to_tac_ok in
                    let uu___5 = wl_to_string wl in
                    let uu___6 =
                      FStar_Compiler_Util.string_of_int
                        (FStar_Compiler_List.length
                           g.FStar_TypeChecker_Common.implicits) in
                    FStar_Compiler_Util.print4
                      "Trying to solve carried problems (defer_ok=%s) (deferred_to_tac_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
                      (string_of_defer_ok defer_ok) uu___4 uu___5 uu___6
                  else ());
                 (let g1 =
                    let uu___3 = solve_and_commit env wl fail in
                    match uu___3 with
                    | FStar_Pervasives_Native.Some
                        (uu___4::uu___5, uu___6, uu___7) when
                        defer_ok = NoDefer ->
                        failwith
                          "Impossible: Unexpected deferred constraints remain"
                    | FStar_Pervasives_Native.Some
                        (deferred, defer_to_tac, imps) ->
                        {
                          FStar_TypeChecker_Common.guard_f =
                            (g.FStar_TypeChecker_Common.guard_f);
                          FStar_TypeChecker_Common.deferred_to_tac =
                            (FStar_Compiler_List.op_At
                               g.FStar_TypeChecker_Common.deferred_to_tac
                               defer_to_tac);
                          FStar_TypeChecker_Common.deferred = deferred;
                          FStar_TypeChecker_Common.univ_ineqs =
                            (g.FStar_TypeChecker_Common.univ_ineqs);
                          FStar_TypeChecker_Common.implicits =
                            (FStar_Compiler_List.op_At
                               g.FStar_TypeChecker_Common.implicits imps)
                        }
                    | uu___4 ->
                        failwith
                          "Impossible: should have raised a failure already" in
                  solve_universe_inequalities env
                    g1.FStar_TypeChecker_Common.univ_ineqs;
                  (let g2 =
                     if deferred_to_tac_ok
                     then
                       let uu___4 =
                         let uu___5 =
                           let uu___6 =
                             FStar_TypeChecker_Env.current_module env in
                           FStar_Ident.string_of_lid uu___6 in
                         FStar_Pervasives_Native.Some uu___5 in
                       FStar_Profiling.profile
                         (fun uu___5 ->
                            FStar_TypeChecker_DeferredImplicits.solve_deferred_to_tactic_goals
                              env g1) uu___4
                         "FStar.TypeChecker.Rel.solve_deferred_to_tactic_goals"
                     else g1 in
                   (let uu___5 =
                      FStar_Compiler_Effect.op_Less_Bar
                        (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "ResolveImplicitsHook") in
                    if uu___5
                    then
                      let uu___6 = guard_to_string env g2 in
                      let uu___7 =
                        FStar_Compiler_Util.string_of_int
                          (FStar_Compiler_List.length
                             g2.FStar_TypeChecker_Common.implicits) in
                      FStar_Compiler_Util.print2
                        "ResolveImplicitsHook: Solved deferred to tactic goals, remaining guard is\n%s (and %s implicits)\n"
                        uu___6 uu___7
                    else ());
                   {
                     FStar_TypeChecker_Common.guard_f =
                       (g2.FStar_TypeChecker_Common.guard_f);
                     FStar_TypeChecker_Common.deferred_to_tac =
                       (g2.FStar_TypeChecker_Common.deferred_to_tac);
                     FStar_TypeChecker_Common.deferred =
                       (g2.FStar_TypeChecker_Common.deferred);
                     FStar_TypeChecker_Common.univ_ineqs = ([], []);
                     FStar_TypeChecker_Common.implicits =
                       (g2.FStar_TypeChecker_Common.implicits)
                   }))) uu___
              "FStar.TypeChecker.Rel.try_solve_deferred_constraints"
let (solve_deferred_constraints :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun g ->
      let defer_ok = NoDefer in
      let smt_ok = true in
      let deferred_to_tac_ok = true in
      try_solve_deferred_constraints defer_ok smt_ok deferred_to_tac_ok env g
let (solve_non_tactic_deferred_constraints :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun maybe_defer_flex_flex ->
    fun env ->
      fun g ->
        let defer_ok =
          if maybe_defer_flex_flex then DeferFlexFlexOnly else NoDefer in
        let smt_ok = true in
        let deferred_to_tac_ok = false in
        try_solve_deferred_constraints defer_ok smt_ok deferred_to_tac_ok env
          g
let (discharge_guard' :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_TypeChecker_Common.guard_t ->
        Prims.bool ->
          FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun use_env_range_msg ->
    fun env ->
      fun g ->
        fun use_smt ->
          let debug =
            ((FStar_Compiler_Effect.op_Less_Bar
                (FStar_TypeChecker_Env.debug env) (FStar_Options.Other "Rel"))
               ||
               (FStar_Compiler_Effect.op_Less_Bar
                  (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "SMTQuery")))
              ||
              (FStar_Compiler_Effect.op_Less_Bar
                 (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Tac")) in
          (let uu___1 =
             FStar_Compiler_Effect.op_Less_Bar
               (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "ResolveImplicitsHook") in
           if uu___1
           then
             let uu___2 = guard_to_string env g in
             FStar_Compiler_Util.print1
               "///////////////////ResolveImplicitsHook: discharge_guard'\nguard = %s\n"
               uu___2
           else ());
          (let g1 =
             let defer_ok = NoDefer in
             let deferred_to_tac_ok = true in
             try_solve_deferred_constraints defer_ok use_smt
               deferred_to_tac_ok env g in
           let ret_g =
             {
               FStar_TypeChecker_Common.guard_f =
                 FStar_TypeChecker_Common.Trivial;
               FStar_TypeChecker_Common.deferred_to_tac =
                 (g1.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (g1.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (g1.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (g1.FStar_TypeChecker_Common.implicits)
             } in
           let uu___1 =
             let uu___2 = FStar_TypeChecker_Env.should_verify env in
             Prims.op_Negation uu___2 in
           if uu___1
           then FStar_Pervasives_Native.Some ret_g
           else
             (match g1.FStar_TypeChecker_Common.guard_f with
              | FStar_TypeChecker_Common.Trivial ->
                  FStar_Pervasives_Native.Some ret_g
              | FStar_TypeChecker_Common.NonTrivial vc ->
                  (if debug
                   then
                     (let uu___4 = FStar_TypeChecker_Env.get_range env in
                      let uu___5 =
                        let uu___6 = FStar_Syntax_Print.term_to_string vc in
                        FStar_Compiler_Util.format1
                          "Before normalization VC=\n%s\n" uu___6 in
                      FStar_Errors.diag uu___4 uu___5)
                   else ();
                   (let vc1 =
                      let uu___4 =
                        let uu___5 =
                          let uu___6 =
                            FStar_TypeChecker_Env.current_module env in
                          FStar_Ident.string_of_lid uu___6 in
                        FStar_Pervasives_Native.Some uu___5 in
                      FStar_Profiling.profile
                        (fun uu___5 ->
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env vc) uu___4
                        "FStar.TypeChecker.Rel.vc_normalization" in
                    if debug
                    then
                      (let uu___5 = FStar_TypeChecker_Env.get_range env in
                       let uu___6 =
                         let uu___7 = FStar_Syntax_Print.term_to_string vc1 in
                         FStar_Compiler_Util.format1
                           "After normalization VC=\n%s\n" uu___7 in
                       FStar_Errors.diag uu___5 uu___6)
                    else ();
                    (let uu___6 = FStar_TypeChecker_Env.get_range env in
                     FStar_TypeChecker_Env.def_check_closed_in_env uu___6
                       "discharge_guard'" env vc1);
                    (let uu___6 = FStar_TypeChecker_Common.check_trivial vc1 in
                     match uu___6 with
                     | FStar_TypeChecker_Common.Trivial ->
                         FStar_Pervasives_Native.Some ret_g
                     | FStar_TypeChecker_Common.NonTrivial vc2 ->
                         if Prims.op_Negation use_smt
                         then
                           (if debug
                            then
                              (let uu___8 =
                                 FStar_TypeChecker_Env.get_range env in
                               let uu___9 =
                                 let uu___10 =
                                   FStar_Syntax_Print.term_to_string vc2 in
                                 FStar_Compiler_Util.format1
                                   "Cannot solve without SMT : %s\n" uu___10 in
                               FStar_Errors.diag uu___8 uu___9)
                            else ();
                            FStar_Pervasives_Native.None)
                         else
                           (if debug
                            then
                              (let uu___10 =
                                 FStar_TypeChecker_Env.get_range env in
                               let uu___11 =
                                 let uu___12 =
                                   FStar_Syntax_Print.term_to_string vc2 in
                                 FStar_Compiler_Util.format1
                                   "Checking VC=\n%s\n" uu___12 in
                               FStar_Errors.diag uu___10 uu___11)
                            else ();
                            (let vcs =
                               let uu___10 = FStar_Options.use_tactics () in
                               if uu___10
                               then
                                 FStar_Options.with_saved_options
                                   (fun uu___11 ->
                                      (let uu___13 =
                                         FStar_Options.set_options
                                           "--no_tactics" in
                                       FStar_Compiler_Effect.op_Less_Bar
                                         (fun uu___14 -> ()) uu___13);
                                      (let vcs1 =
                                         (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                           env vc2 in
                                       (let uu___14 =
                                          FStar_Options.profile_enabled
                                            FStar_Pervasives_Native.None
                                            "FStar.TypeChecker" in
                                        if uu___14
                                        then
                                          let uu___15 =
                                            FStar_Compiler_Util.string_of_int
                                              (FStar_Compiler_List.length
                                                 vcs1) in
                                          FStar_Compiler_Util.print1
                                            "Tactic preprocessing produced %s goals\n"
                                            uu___15
                                        else ());
                                       (let vcs2 =
                                          FStar_Compiler_List.map
                                            (fun uu___14 ->
                                               match uu___14 with
                                               | (env1, goal, opts) ->
                                                   let uu___15 =
                                                     norm_with_steps
                                                       "FStar.TypeChecker.Rel.norm_with_steps.7"
                                                       [FStar_TypeChecker_Env.Simplify;
                                                       FStar_TypeChecker_Env.Primops]
                                                       env1 goal in
                                                   (env1, uu___15, opts))
                                            vcs1 in
                                        let vcs3 =
                                          FStar_Compiler_List.map
                                            (fun uu___14 ->
                                               match uu___14 with
                                               | (env1, goal, opts) ->
                                                   let uu___15 =
                                                     (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.handle_smt_goal
                                                       env1 goal in
                                                   FStar_Compiler_Effect.op_Bar_Greater
                                                     uu___15
                                                     (FStar_Compiler_List.map
                                                        (fun uu___16 ->
                                                           match uu___16 with
                                                           | (env2, goal1) ->
                                                               (env2, goal1,
                                                                 opts))))
                                            vcs2 in
                                        FStar_Compiler_List.flatten vcs3)))
                               else
                                 (let uu___12 =
                                    let uu___13 = FStar_Options.peek () in
                                    (env, vc2, uu___13) in
                                  [uu___12]) in
                             let vcs1 =
                               let uu___10 = FStar_Options.split_queries () in
                               if uu___10
                               then
                                 FStar_Compiler_Effect.op_Bar_Greater vcs
                                   (FStar_Compiler_List.collect
                                      (fun uu___11 ->
                                         match uu___11 with
                                         | (env1, goal, opts) ->
                                             let uu___12 =
                                               FStar_TypeChecker_Env.split_smt_query
                                                 env1 goal in
                                             (match uu___12 with
                                              | FStar_Pervasives_Native.None
                                                  -> [(env1, goal, opts)]
                                              | FStar_Pervasives_Native.Some
                                                  goals ->
                                                  FStar_Compiler_Effect.op_Bar_Greater
                                                    goals
                                                    (FStar_Compiler_List.map
                                                       (fun uu___13 ->
                                                          match uu___13 with
                                                          | (env2, goal1) ->
                                                              (env2, goal1,
                                                                opts))))))
                               else vcs in
                             FStar_Compiler_Effect.op_Bar_Greater vcs1
                               (FStar_Compiler_List.iter
                                  (fun uu___10 ->
                                     match uu___10 with
                                     | (env1, goal, opts) ->
                                         let uu___11 =
                                           FStar_TypeChecker_Common.check_trivial
                                             goal in
                                         (match uu___11 with
                                          | FStar_TypeChecker_Common.Trivial
                                              ->
                                              if debug
                                              then
                                                FStar_Compiler_Util.print_string
                                                  "Goal completely solved by tactic\n"
                                              else ()
                                          | FStar_TypeChecker_Common.NonTrivial
                                              goal1 ->
                                              (FStar_Options.push ();
                                               FStar_Options.set opts;
                                               if debug
                                               then
                                                 (let uu___15 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1 in
                                                  let uu___16 =
                                                    let uu___17 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1 in
                                                    let uu___18 =
                                                      FStar_TypeChecker_Env.string_of_proof_ns
                                                        env1 in
                                                    FStar_Compiler_Util.format2
                                                      "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                      uu___17 uu___18 in
                                                  FStar_Errors.diag uu___15
                                                    uu___16)
                                               else ();
                                               if debug
                                               then
                                                 (let uu___16 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1 in
                                                  let uu___17 =
                                                    let uu___18 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1 in
                                                    FStar_Compiler_Util.format1
                                                      "Before calling solver VC=\n%s\n"
                                                      uu___18 in
                                                  FStar_Errors.diag uu___16
                                                    uu___17)
                                               else ();
                                               (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve
                                                 use_env_range_msg env1 goal1;
                                               FStar_Options.pop ())))));
                            FStar_Pervasives_Native.Some ret_g))))))
let (discharge_guard_no_smt :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun g ->
      let uu___ = discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu___ with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None ->
          let uu___1 = FStar_TypeChecker_Env.get_range env in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu___1
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun g ->
      let uu___ = discharge_guard' FStar_Pervasives_Native.None env g true in
      match uu___ with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu___ = try_teq false env t1 t2 in
        match uu___ with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some g ->
            discharge_guard' FStar_Pervasives_Native.None env g false
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        (let uu___1 =
           FStar_Compiler_Effect.op_Less_Bar
             (FStar_TypeChecker_Env.debug env) (FStar_Options.Other "Rel") in
         if uu___1
         then
           let uu___2 = FStar_TypeChecker_Normalize.term_to_string env t1 in
           let uu___3 = FStar_TypeChecker_Normalize.term_to_string env t2 in
           FStar_Compiler_Util.print2 "try_subtype_no_smt of %s and %s\n"
             uu___2 uu___3
         else ());
        (let uu___1 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2 in
         match uu___1 with
         | (prob, x, wl) ->
             let g =
               let uu___2 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu___3 -> FStar_Pervasives_Native.None) in
               FStar_Compiler_Effect.op_Less_Bar (with_guard env prob) uu___2 in
             (match g with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu___2 =
                      let uu___3 = FStar_Syntax_Syntax.mk_binder x in
                      [uu___3] in
                    FStar_TypeChecker_Env.close_guard env uu___2 g1 in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
let (check_subtyping :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.bv * FStar_TypeChecker_Common.guard_t)
          FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStar_TypeChecker_Env.current_module env in
            FStar_Ident.string_of_lid uu___2 in
          FStar_Pervasives_Native.Some uu___1 in
        FStar_Profiling.profile
          (fun uu___1 ->
             (let uu___3 =
                FStar_Compiler_Effect.op_Less_Bar
                  (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu___3
              then
                let uu___4 =
                  FStar_TypeChecker_Normalize.term_to_string env t1 in
                let uu___5 =
                  FStar_TypeChecker_Normalize.term_to_string env t2 in
                FStar_Compiler_Util.print2 "check_subtyping of %s and %s\n"
                  uu___4 uu___5
              else ());
             (let uu___3 =
                new_t_prob (empty_worklist env) env t1
                  FStar_TypeChecker_Common.SUB t2 in
              match uu___3 with
              | (prob, x, wl) ->
                  let g =
                    let uu___4 =
                      solve_and_commit env (singleton wl prob true)
                        (fun uu___5 -> FStar_Pervasives_Native.None) in
                    FStar_Compiler_Effect.op_Less_Bar (with_guard env prob)
                      uu___4 in
                  ((let uu___5 =
                      (FStar_Compiler_Effect.op_Less_Bar
                         (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                        && (FStar_Compiler_Util.is_some g) in
                    if uu___5
                    then
                      let uu___6 =
                        FStar_TypeChecker_Normalize.term_to_string env t1 in
                      let uu___7 =
                        FStar_TypeChecker_Normalize.term_to_string env t2 in
                      let uu___8 =
                        let uu___9 = FStar_Compiler_Util.must g in
                        guard_to_string env uu___9 in
                      FStar_Compiler_Util.print3
                        "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                        uu___6 uu___7 uu___8
                    else ());
                   (match g with
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None
                    | FStar_Pervasives_Native.Some g1 ->
                        FStar_Pervasives_Native.Some (x, g1))))) uu___
          "FStar.TypeChecker.Rel.check_subtyping"
let (get_subtyping_predicate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu___ = check_subtyping env t1 t2 in
        match uu___ with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x, g) ->
            let uu___1 =
              let uu___2 = FStar_Syntax_Syntax.mk_binder x in
              FStar_TypeChecker_Env.abstract_guard uu___2 g in
            FStar_Pervasives_Native.Some uu___1
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu___ = check_subtyping env t1 t2 in
        match uu___ with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x, g) ->
            let uu___1 =
              let uu___2 =
                let uu___3 = FStar_Syntax_Syntax.mk_binder x in [uu___3] in
              FStar_TypeChecker_Env.close_guard env uu___2 g in
            FStar_Pervasives_Native.Some uu___1
let (try_solve_single_valued_implicits :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      FStar_TypeChecker_Env.implicits ->
        (FStar_TypeChecker_Env.implicits * Prims.bool))
  =
  fun env ->
    fun is_tac ->
      fun imps ->
        if is_tac
        then (imps, false)
        else
          (let imp_value imp =
             let uu___1 =
               ((imp.FStar_TypeChecker_Common.imp_uvar),
                 (imp.FStar_TypeChecker_Common.imp_range)) in
             match uu___1 with
             | (ctx_u, r) ->
                 let t_norm =
                   let uu___2 = FStar_Syntax_Util.ctx_uvar_typ ctx_u in
                   FStar_TypeChecker_Normalize.normalize
                     FStar_TypeChecker_Normalize.whnf_steps env uu___2 in
                 let uu___2 =
                   let uu___3 = FStar_Syntax_Subst.compress t_norm in
                   uu___3.FStar_Syntax_Syntax.n in
                 (match uu___2 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.unit_lid
                      ->
                      let uu___3 =
                        FStar_Compiler_Effect.op_Bar_Greater r
                          FStar_Syntax_Syntax.unit_const_with_range in
                      FStar_Compiler_Effect.op_Bar_Greater uu___3
                        (fun uu___4 -> FStar_Pervasives_Native.Some uu___4)
                  | FStar_Syntax_Syntax.Tm_refine (b, uu___3) when
                      FStar_Syntax_Util.is_unit b.FStar_Syntax_Syntax.sort ->
                      let uu___4 =
                        FStar_Compiler_Effect.op_Bar_Greater r
                          FStar_Syntax_Syntax.unit_const_with_range in
                      FStar_Compiler_Effect.op_Bar_Greater uu___4
                        (fun uu___5 -> FStar_Pervasives_Native.Some uu___5)
                  | uu___3 -> FStar_Pervasives_Native.None) in
           let b =
             FStar_Compiler_List.fold_left
               (fun b1 ->
                  fun imp ->
                    let uu___1 =
                      (let uu___2 =
                         FStar_Syntax_Unionfind.find
                           (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
                       FStar_Compiler_Effect.op_Bar_Greater uu___2
                         FStar_Compiler_Util.is_none)
                        &&
                        (let uu___2 =
                           FStar_Syntax_Util.ctx_uvar_should_check
                             imp.FStar_TypeChecker_Common.imp_uvar in
                         uu___2 = FStar_Syntax_Syntax.Strict) in
                    if uu___1
                    then
                      let uu___2 = imp_value imp in
                      match uu___2 with
                      | FStar_Pervasives_Native.Some tm ->
                          (commit env
                             [TERM
                                ((imp.FStar_TypeChecker_Common.imp_uvar), tm)];
                           true)
                      | FStar_Pervasives_Native.None -> b1
                    else b1) false imps in
           (imps, b))
let maybe_set_guard_uvar :
  'uuuuu .
    'uuuuu ->
      FStar_Syntax_Syntax.ctx_uvar -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env ->
    fun uv ->
      fun tm ->
        let uu___ = FStar_Syntax_Util.ctx_uvar_kind uv in
        match uu___ with
        | FStar_Pervasives.Inl (FStar_Pervasives_Native.None) -> false
        | FStar_Pervasives.Inl (FStar_Pervasives_Native.Some g_uv) ->
            ((let uu___2 = FStar_Options.debug_any () in
              if uu___2
              then
                let uu___3 = FStar_Syntax_Print.ctx_uvar_to_string uv in
                let uu___4 = FStar_Syntax_Print.ctx_uvar_to_string g_uv in
                let uu___5 = FStar_Syntax_Print.term_to_string tm in
                FStar_Compiler_Util.print3
                  "Uvar %s has guard uvar %s, setting guard to %s\n" uu___3
                  uu___4 uu___5
              else ());
             commit env [TERM (g_uv, tm)];
             true)
        | FStar_Pervasives.Inr uu___1 ->
            failwith "Impossible (maybe_set_guard_uvar)"
let (core_check_and_maybe_add_to_guard_uvar :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.ctx_uvar ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ ->
          Prims.bool -> FStar_TypeChecker_Env.core_check_ret_t)
  =
  fun env ->
    fun uv ->
      fun t ->
        fun k ->
          fun must_tot ->
            let debug f =
              let uu___ = FStar_Options.debug_any () in
              if uu___ then f () else () in
            let uu___ =
              let uu___1 = FStar_Syntax_Util.ctx_uvar_should_check uv in
              FStar_Syntax_Syntax.uu___is_Allow_untyped uu___1 in
            if uu___
            then
              ((let uu___2 =
                  maybe_set_guard_uvar env uv FStar_Syntax_Util.t_true in
                ());
               FStar_Pervasives.Inl FStar_Pervasives_Native.None)
            else
              (let uu___2 =
                 env.FStar_TypeChecker_Env.core_check env t k must_tot in
               match uu___2 with
               | FStar_Pervasives.Inl (FStar_Pervasives_Native.None) ->
                   (debug
                      (fun uu___4 ->
                         let uu___5 =
                           FStar_Syntax_Print.ctx_uvar_to_string uv in
                         FStar_Compiler_Util.print1
                           "Core checking of uvar %s ok (no guard)\n" uu___5);
                    (let uu___5 =
                       maybe_set_guard_uvar env uv FStar_Syntax_Util.t_true in
                     ());
                    FStar_Pervasives.Inl FStar_Pervasives_Native.None)
               | FStar_Pervasives.Inl (FStar_Pervasives_Native.Some vc) ->
                   (debug
                      (fun uu___4 ->
                         let uu___5 =
                           FStar_Syntax_Print.ctx_uvar_to_string uv in
                         let uu___6 = FStar_Syntax_Print.term_to_string t in
                         let uu___7 = FStar_Syntax_Print.term_to_string vc in
                         FStar_Compiler_Util.print3
                           "Core checking of uvar %s solved to %s ok with guard: %s\n"
                           uu___5 uu___6 uu___7);
                    (let uu___4 = maybe_set_guard_uvar env uv vc in
                     if uu___4
                     then FStar_Pervasives.Inl FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives.Inl (FStar_Pervasives_Native.Some vc)))
               | FStar_Pervasives.Inr err ->
                   (debug
                      (fun uu___4 ->
                         let uu___5 =
                           let uu___6 = FStar_TypeChecker_Env.get_range env in
                           FStar_Compiler_Range.string_of_range uu___6 in
                         let uu___6 = err true in
                         let uu___7 = FStar_Syntax_Print.term_to_string t in
                         let uu___8 = FStar_Syntax_Print.term_to_string k in
                         let uu___9 = err false in
                         FStar_Compiler_Util.print5
                           "(%s) Core checking failed (%s) on term %s and type %s\n%s\n"
                           uu___5 uu___6 uu___7 uu___8 uu___9);
                    FStar_Pervasives.Inr err))
let (check_implicit_solution :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.ctx_uvar ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          Prims.bool -> Prims.string -> FStar_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun uv ->
      fun t ->
        fun k ->
          fun must_tot ->
            fun reason ->
              let t1 =
                let uu___ =
                  let uu___1 = FStar_Syntax_Subst.compress t in
                  uu___1.FStar_Syntax_Syntax.n in
                match uu___ with
                | FStar_Syntax_Syntax.Tm_abs
                    (bs, body, FStar_Pervasives_Native.Some rc) ->
                    {
                      FStar_Syntax_Syntax.n =
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, body,
                             (FStar_Pervasives_Native.Some
                                {
                                  FStar_Syntax_Syntax.residual_effect =
                                    (rc.FStar_Syntax_Syntax.residual_effect);
                                  FStar_Syntax_Syntax.residual_typ =
                                    FStar_Pervasives_Native.None;
                                  FStar_Syntax_Syntax.residual_flags =
                                    (rc.FStar_Syntax_Syntax.residual_flags)
                                })));
                      FStar_Syntax_Syntax.pos = (t.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars = (t.FStar_Syntax_Syntax.vars);
                      FStar_Syntax_Syntax.hash_code =
                        (t.FStar_Syntax_Syntax.hash_code)
                    }
                | uu___1 -> t in
              let uu___ = FStar_TypeChecker_Env.clear_expected_typ env in
              match uu___ with
              | (env1, uu___1) ->
                  let fallback uu___2 =
                    let uu___3 =
                      let uu___4 =
                        FStar_TypeChecker_Env.set_expected_typ
                          {
                            FStar_TypeChecker_Env.solver =
                              (env1.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (env1.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (env1.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (env1.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (env1.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (env1.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (env1.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (env1.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (env1.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (env1.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (env1.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (env1.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (env1.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (env1.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (env1.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (env1.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq_strict =
                              (env1.FStar_TypeChecker_Env.use_eq_strict);
                            FStar_TypeChecker_Env.is_iface =
                              (env1.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (env1.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax =
                              (env1.FStar_TypeChecker_Env.lax);
                            FStar_TypeChecker_Env.lax_universes =
                              (env1.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (env1.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (env1.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (env1.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (env1.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (env1.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
                              (env1.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                            FStar_TypeChecker_Env.universe_of =
                              (env1.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                              =
                              (env1.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                            FStar_TypeChecker_Env.teq_nosmt_force =
                              (env1.FStar_TypeChecker_Env.teq_nosmt_force);
                            FStar_TypeChecker_Env.subtype_nosmt_force =
                              (env1.FStar_TypeChecker_Env.subtype_nosmt_force);
                            FStar_TypeChecker_Env.use_bv_sorts = true;
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (env1.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (env1.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (env1.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (env1.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (env1.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (env1.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (env1.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.mpreprocess =
                              (env1.FStar_TypeChecker_Env.mpreprocess);
                            FStar_TypeChecker_Env.postprocess =
                              (env1.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.identifier_info =
                              (env1.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (env1.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (env1.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (env1.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (env1.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (env1.FStar_TypeChecker_Env.erasable_types_tab);
                            FStar_TypeChecker_Env.enable_defer_to_tac =
                              (env1.FStar_TypeChecker_Env.enable_defer_to_tac);
                            FStar_TypeChecker_Env.unif_allow_ref_guards =
                              (env1.FStar_TypeChecker_Env.unif_allow_ref_guards);
                            FStar_TypeChecker_Env.erase_erasable_args =
                              (env1.FStar_TypeChecker_Env.erase_erasable_args);
                            FStar_TypeChecker_Env.core_check =
                              (env1.FStar_TypeChecker_Env.core_check)
                          } k in
                      env1.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                        uu___4 t1 must_tot in
                    match uu___3 with
                    | (k', g) ->
                        let uu___4 = get_subtyping_predicate env1 k' k in
                        (match uu___4 with
                         | FStar_Pervasives_Native.None ->
                             let uu___5 =
                               FStar_TypeChecker_Err.expected_expression_of_type
                                 env1 k t1 k' in
                             FStar_Errors.raise_error uu___5
                               t1.FStar_Syntax_Syntax.pos
                         | FStar_Pervasives_Native.Some f ->
                             let uu___5 =
                               FStar_TypeChecker_Env.apply_guard f t1 in
                             FStar_TypeChecker_Env.conj_guard uu___5 g) in
                  if
                    (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1) &&
                      (Prims.op_Negation env1.FStar_TypeChecker_Env.lax)
                  then
                    let uu___2 =
                      core_check_and_maybe_add_to_guard_uvar env1 uv t1 k
                        must_tot in
                    (match uu___2 with
                     | FStar_Pervasives.Inl (FStar_Pervasives_Native.None) ->
                         FStar_TypeChecker_Common.trivial_guard
                     | FStar_Pervasives.Inl (FStar_Pervasives_Native.Some g)
                         ->
                         {
                           FStar_TypeChecker_Common.guard_f =
                             (FStar_TypeChecker_Common.NonTrivial g);
                           FStar_TypeChecker_Common.deferred_to_tac =
                             (FStar_TypeChecker_Common.trivial_guard.FStar_TypeChecker_Common.deferred_to_tac);
                           FStar_TypeChecker_Common.deferred =
                             (FStar_TypeChecker_Common.trivial_guard.FStar_TypeChecker_Common.deferred);
                           FStar_TypeChecker_Common.univ_ineqs =
                             (FStar_TypeChecker_Common.trivial_guard.FStar_TypeChecker_Common.univ_ineqs);
                           FStar_TypeChecker_Common.implicits =
                             (FStar_TypeChecker_Common.trivial_guard.FStar_TypeChecker_Common.implicits)
                         }
                     | FStar_Pervasives.Inr print_err -> fallback ())
                  else
                    ((let uu___4 =
                        maybe_set_guard_uvar env1 uv FStar_Syntax_Util.t_true in
                      ());
                     fallback ())
let (check_implicit_solution_and_discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.implicit ->
      Prims.bool ->
        FStar_TypeChecker_Env.implicits FStar_Pervasives_Native.option)
  =
  fun env ->
    fun imp ->
      fun force_univ_constraints ->
        let uu___ = imp in
        match uu___ with
        | { FStar_TypeChecker_Common.imp_reason = reason;
            FStar_TypeChecker_Common.imp_uvar = ctx_u;
            FStar_TypeChecker_Common.imp_tm = tm;
            FStar_TypeChecker_Common.imp_range = r;_} ->
            let env1 =
              {
                FStar_TypeChecker_Env.solver =
                  (env.FStar_TypeChecker_Env.solver);
                FStar_TypeChecker_Env.range =
                  (env.FStar_TypeChecker_Env.range);
                FStar_TypeChecker_Env.curmodule =
                  (env.FStar_TypeChecker_Env.curmodule);
                FStar_TypeChecker_Env.gamma =
                  (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                FStar_TypeChecker_Env.gamma_sig =
                  (env.FStar_TypeChecker_Env.gamma_sig);
                FStar_TypeChecker_Env.gamma_cache =
                  (env.FStar_TypeChecker_Env.gamma_cache);
                FStar_TypeChecker_Env.modules =
                  (env.FStar_TypeChecker_Env.modules);
                FStar_TypeChecker_Env.expected_typ =
                  (env.FStar_TypeChecker_Env.expected_typ);
                FStar_TypeChecker_Env.sigtab =
                  (env.FStar_TypeChecker_Env.sigtab);
                FStar_TypeChecker_Env.attrtab =
                  (env.FStar_TypeChecker_Env.attrtab);
                FStar_TypeChecker_Env.instantiate_imp =
                  (env.FStar_TypeChecker_Env.instantiate_imp);
                FStar_TypeChecker_Env.effects =
                  (env.FStar_TypeChecker_Env.effects);
                FStar_TypeChecker_Env.generalize =
                  (env.FStar_TypeChecker_Env.generalize);
                FStar_TypeChecker_Env.letrecs =
                  (env.FStar_TypeChecker_Env.letrecs);
                FStar_TypeChecker_Env.top_level =
                  (env.FStar_TypeChecker_Env.top_level);
                FStar_TypeChecker_Env.check_uvars =
                  (env.FStar_TypeChecker_Env.check_uvars);
                FStar_TypeChecker_Env.use_eq_strict =
                  (env.FStar_TypeChecker_Env.use_eq_strict);
                FStar_TypeChecker_Env.is_iface =
                  (env.FStar_TypeChecker_Env.is_iface);
                FStar_TypeChecker_Env.admit =
                  (env.FStar_TypeChecker_Env.admit);
                FStar_TypeChecker_Env.lax = (env.FStar_TypeChecker_Env.lax);
                FStar_TypeChecker_Env.lax_universes =
                  (env.FStar_TypeChecker_Env.lax_universes);
                FStar_TypeChecker_Env.phase1 =
                  (env.FStar_TypeChecker_Env.phase1);
                FStar_TypeChecker_Env.failhard =
                  (env.FStar_TypeChecker_Env.failhard);
                FStar_TypeChecker_Env.nosynth =
                  (env.FStar_TypeChecker_Env.nosynth);
                FStar_TypeChecker_Env.uvar_subtyping =
                  (env.FStar_TypeChecker_Env.uvar_subtyping);
                FStar_TypeChecker_Env.tc_term =
                  (env.FStar_TypeChecker_Env.tc_term);
                FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
                  (env.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                FStar_TypeChecker_Env.universe_of =
                  (env.FStar_TypeChecker_Env.universe_of);
                FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
                  (env.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                FStar_TypeChecker_Env.teq_nosmt_force =
                  (env.FStar_TypeChecker_Env.teq_nosmt_force);
                FStar_TypeChecker_Env.subtype_nosmt_force =
                  (env.FStar_TypeChecker_Env.subtype_nosmt_force);
                FStar_TypeChecker_Env.use_bv_sorts =
                  (env.FStar_TypeChecker_Env.use_bv_sorts);
                FStar_TypeChecker_Env.qtbl_name_and_index =
                  (env.FStar_TypeChecker_Env.qtbl_name_and_index);
                FStar_TypeChecker_Env.normalized_eff_names =
                  (env.FStar_TypeChecker_Env.normalized_eff_names);
                FStar_TypeChecker_Env.fv_delta_depths =
                  (env.FStar_TypeChecker_Env.fv_delta_depths);
                FStar_TypeChecker_Env.proof_ns =
                  (env.FStar_TypeChecker_Env.proof_ns);
                FStar_TypeChecker_Env.synth_hook =
                  (env.FStar_TypeChecker_Env.synth_hook);
                FStar_TypeChecker_Env.try_solve_implicits_hook =
                  (env.FStar_TypeChecker_Env.try_solve_implicits_hook);
                FStar_TypeChecker_Env.splice =
                  (env.FStar_TypeChecker_Env.splice);
                FStar_TypeChecker_Env.mpreprocess =
                  (env.FStar_TypeChecker_Env.mpreprocess);
                FStar_TypeChecker_Env.postprocess =
                  (env.FStar_TypeChecker_Env.postprocess);
                FStar_TypeChecker_Env.identifier_info =
                  (env.FStar_TypeChecker_Env.identifier_info);
                FStar_TypeChecker_Env.tc_hooks =
                  (env.FStar_TypeChecker_Env.tc_hooks);
                FStar_TypeChecker_Env.dsenv =
                  (env.FStar_TypeChecker_Env.dsenv);
                FStar_TypeChecker_Env.nbe = (env.FStar_TypeChecker_Env.nbe);
                FStar_TypeChecker_Env.strict_args_tab =
                  (env.FStar_TypeChecker_Env.strict_args_tab);
                FStar_TypeChecker_Env.erasable_types_tab =
                  (env.FStar_TypeChecker_Env.erasable_types_tab);
                FStar_TypeChecker_Env.enable_defer_to_tac =
                  (env.FStar_TypeChecker_Env.enable_defer_to_tac);
                FStar_TypeChecker_Env.unif_allow_ref_guards =
                  (env.FStar_TypeChecker_Env.unif_allow_ref_guards);
                FStar_TypeChecker_Env.erase_erasable_args =
                  (env.FStar_TypeChecker_Env.erase_erasable_args);
                FStar_TypeChecker_Env.core_check =
                  (env.FStar_TypeChecker_Env.core_check)
              } in
            ((let uu___2 =
                FStar_Compiler_Effect.op_Less_Bar
                  (FStar_TypeChecker_Env.debug env1)
                  (FStar_Options.Other "Rel") in
              if uu___2
              then
                let uu___3 =
                  FStar_Syntax_Print.uvar_to_string
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
                let uu___4 = FStar_Syntax_Print.term_to_string tm in
                let uu___5 =
                  let uu___6 = FStar_Syntax_Util.ctx_uvar_typ ctx_u in
                  FStar_Syntax_Print.term_to_string uu___6 in
                let uu___6 = FStar_Compiler_Range.string_of_range r in
                FStar_Compiler_Util.print5
                  "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                  uu___3 uu___4 uu___5 reason uu___6
              else ());
             (let g =
                let must_tot =
                  let uu___2 =
                    (env1.FStar_TypeChecker_Env.phase1 ||
                       env1.FStar_TypeChecker_Env.lax)
                      ||
                      (let uu___3 =
                         FStar_Syntax_Util.ctx_uvar_should_check ctx_u in
                       FStar_Syntax_Syntax.uu___is_Allow_ghost uu___3) in
                  Prims.op_Negation uu___2 in
                let uu___2 =
                  let uu___3 =
                    FStar_Syntax_Print.uvar_to_string
                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
                  let uu___4 =
                    FStar_TypeChecker_Normalize.term_to_string env1 tm in
                  let uu___5 =
                    let uu___6 = FStar_Syntax_Util.ctx_uvar_typ ctx_u in
                    FStar_TypeChecker_Normalize.term_to_string env1 uu___6 in
                  FStar_Compiler_Util.format3
                    "While checking implicit %s set to %s of expected type %s"
                    uu___3 uu___4 uu___5 in
                FStar_Errors.with_ctx uu___2
                  (fun uu___3 ->
                     let uu___4 = FStar_Syntax_Util.ctx_uvar_typ ctx_u in
                     check_implicit_solution env1 ctx_u tm uu___4 must_tot
                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_reason) in
              let uu___2 =
                (Prims.op_Negation force_univ_constraints) &&
                  (FStar_Compiler_List.existsb
                     (fun uu___3 ->
                        match uu___3 with
                        | (reason1, uu___4, uu___5) ->
                            reason1 =
                              FStar_TypeChecker_Common.Deferred_univ_constraint)
                     g.FStar_TypeChecker_Common.deferred) in
              if uu___2
              then FStar_Pervasives_Native.None
              else
                (let g' =
                   let uu___4 =
                     discharge_guard'
                       (FStar_Pervasives_Native.Some
                          (fun uu___5 ->
                             let uu___6 =
                               FStar_Syntax_Print.term_to_string tm in
                             let uu___7 =
                               FStar_Compiler_Range.string_of_range r in
                             let uu___8 =
                               FStar_Compiler_Range.string_of_range
                                 tm.FStar_Syntax_Syntax.pos in
                             FStar_Compiler_Util.format4
                               "%s (Introduced at %s for %s resolved at %s)"
                               uu___6 uu___7 reason uu___8)) env1 g true in
                   match uu___4 with
                   | FStar_Pervasives_Native.Some g1 -> g1
                   | FStar_Pervasives_Native.None ->
                       failwith
                         "Impossible, with use_smt = true, discharge_guard' must return Some" in
                 FStar_Compiler_Effect.op_Bar_Greater
                   g'.FStar_TypeChecker_Common.implicits
                   (fun uu___4 -> FStar_Pervasives_Native.Some uu___4))))
let rec (unresolved : FStar_Syntax_Syntax.ctx_uvar -> Prims.bool) =
  fun ctx_u ->
    let uu___ =
      FStar_Syntax_Unionfind.find ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
    match uu___ with
    | FStar_Pervasives_Native.Some r ->
        (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
         | FStar_Pervasives_Native.None -> false
         | FStar_Pervasives_Native.Some uu___1 ->
             let uu___2 =
               let uu___3 = FStar_Syntax_Subst.compress r in
               uu___3.FStar_Syntax_Syntax.n in
             (match uu___2 with
              | FStar_Syntax_Syntax.Tm_uvar (ctx_u', uu___3) ->
                  unresolved ctx_u'
              | uu___3 -> false))
    | FStar_Pervasives_Native.None -> true
let (pick_a_univ_deffered_implicit :
  tagged_implicits ->
    (FStar_TypeChecker_Env.implicit FStar_Pervasives_Native.option *
      tagged_implicits))
  =
  fun out ->
    let uu___ =
      FStar_Compiler_List.partition
        (fun uu___1 ->
           match uu___1 with
           | (uu___2, status) ->
               status = Implicit_checking_defers_univ_constraint) out in
    match uu___ with
    | (imps_with_deferred_univs, rest) ->
        (match imps_with_deferred_univs with
         | [] -> (FStar_Pervasives_Native.None, out)
         | hd::tl ->
             let uu___1 =
               let uu___2 =
                 FStar_Compiler_Effect.op_Bar_Greater hd
                   FStar_Pervasives_Native.fst in
               FStar_Compiler_Effect.op_Bar_Greater uu___2
                 (fun uu___3 -> FStar_Pervasives_Native.Some uu___3) in
             (uu___1, (FStar_Compiler_List.op_At tl rest)))
let (is_implicit_resolved :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.implicit -> Prims.bool)
  =
  fun env ->
    fun i ->
      let uu___ =
        let uu___1 =
          FStar_Compiler_Effect.op_Bar_Greater
            i.FStar_TypeChecker_Common.imp_tm FStar_Syntax_Free.uvars in
        FStar_Compiler_Effect.op_Bar_Greater uu___1
          FStar_Compiler_Util.set_elements in
      FStar_Compiler_Effect.op_Bar_Greater uu___
        (FStar_Compiler_List.for_all
           (fun uv ->
              let uu___1 = FStar_Syntax_Util.ctx_uvar_should_check uv in
              FStar_Syntax_Syntax.uu___is_Allow_unresolved uu___1))
let rec (check_implicit_solution_for_tac :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.implicit ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env ->
    fun i ->
      let uu___ = i in
      match uu___ with
      | { FStar_TypeChecker_Common.imp_reason = reason;
          FStar_TypeChecker_Common.imp_uvar = ctx_u;
          FStar_TypeChecker_Common.imp_tm = tm;
          FStar_TypeChecker_Common.imp_range = r;_} ->
          let uvar_ty = FStar_Syntax_Util.ctx_uvar_typ ctx_u in
          let uvar_should_check =
            FStar_Syntax_Util.ctx_uvar_should_check ctx_u in
          if
            (FStar_Syntax_Syntax.uu___is_Allow_untyped uvar_should_check) ||
              (FStar_Syntax_Syntax.uu___is_Already_checked uvar_should_check)
          then FStar_Pervasives_Native.None
          else
            (let env1 =
               {
                 FStar_TypeChecker_Env.solver =
                   (env.FStar_TypeChecker_Env.solver);
                 FStar_TypeChecker_Env.range =
                   (env.FStar_TypeChecker_Env.range);
                 FStar_TypeChecker_Env.curmodule =
                   (env.FStar_TypeChecker_Env.curmodule);
                 FStar_TypeChecker_Env.gamma =
                   (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                 FStar_TypeChecker_Env.gamma_sig =
                   (env.FStar_TypeChecker_Env.gamma_sig);
                 FStar_TypeChecker_Env.gamma_cache =
                   (env.FStar_TypeChecker_Env.gamma_cache);
                 FStar_TypeChecker_Env.modules =
                   (env.FStar_TypeChecker_Env.modules);
                 FStar_TypeChecker_Env.expected_typ =
                   (env.FStar_TypeChecker_Env.expected_typ);
                 FStar_TypeChecker_Env.sigtab =
                   (env.FStar_TypeChecker_Env.sigtab);
                 FStar_TypeChecker_Env.attrtab =
                   (env.FStar_TypeChecker_Env.attrtab);
                 FStar_TypeChecker_Env.instantiate_imp =
                   (env.FStar_TypeChecker_Env.instantiate_imp);
                 FStar_TypeChecker_Env.effects =
                   (env.FStar_TypeChecker_Env.effects);
                 FStar_TypeChecker_Env.generalize =
                   (env.FStar_TypeChecker_Env.generalize);
                 FStar_TypeChecker_Env.letrecs =
                   (env.FStar_TypeChecker_Env.letrecs);
                 FStar_TypeChecker_Env.top_level =
                   (env.FStar_TypeChecker_Env.top_level);
                 FStar_TypeChecker_Env.check_uvars =
                   (env.FStar_TypeChecker_Env.check_uvars);
                 FStar_TypeChecker_Env.use_eq_strict =
                   (env.FStar_TypeChecker_Env.use_eq_strict);
                 FStar_TypeChecker_Env.is_iface =
                   (env.FStar_TypeChecker_Env.is_iface);
                 FStar_TypeChecker_Env.admit =
                   (env.FStar_TypeChecker_Env.admit);
                 FStar_TypeChecker_Env.lax = (env.FStar_TypeChecker_Env.lax);
                 FStar_TypeChecker_Env.lax_universes =
                   (env.FStar_TypeChecker_Env.lax_universes);
                 FStar_TypeChecker_Env.phase1 =
                   (env.FStar_TypeChecker_Env.phase1);
                 FStar_TypeChecker_Env.failhard =
                   (env.FStar_TypeChecker_Env.failhard);
                 FStar_TypeChecker_Env.nosynth =
                   (env.FStar_TypeChecker_Env.nosynth);
                 FStar_TypeChecker_Env.uvar_subtyping =
                   (env.FStar_TypeChecker_Env.uvar_subtyping);
                 FStar_TypeChecker_Env.tc_term =
                   (env.FStar_TypeChecker_Env.tc_term);
                 FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
                   (env.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                 FStar_TypeChecker_Env.universe_of =
                   (env.FStar_TypeChecker_Env.universe_of);
                 FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
                   (env.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                 FStar_TypeChecker_Env.teq_nosmt_force =
                   (env.FStar_TypeChecker_Env.teq_nosmt_force);
                 FStar_TypeChecker_Env.subtype_nosmt_force =
                   (env.FStar_TypeChecker_Env.subtype_nosmt_force);
                 FStar_TypeChecker_Env.use_bv_sorts =
                   (env.FStar_TypeChecker_Env.use_bv_sorts);
                 FStar_TypeChecker_Env.qtbl_name_and_index =
                   (env.FStar_TypeChecker_Env.qtbl_name_and_index);
                 FStar_TypeChecker_Env.normalized_eff_names =
                   (env.FStar_TypeChecker_Env.normalized_eff_names);
                 FStar_TypeChecker_Env.fv_delta_depths =
                   (env.FStar_TypeChecker_Env.fv_delta_depths);
                 FStar_TypeChecker_Env.proof_ns =
                   (env.FStar_TypeChecker_Env.proof_ns);
                 FStar_TypeChecker_Env.synth_hook =
                   (env.FStar_TypeChecker_Env.synth_hook);
                 FStar_TypeChecker_Env.try_solve_implicits_hook =
                   (env.FStar_TypeChecker_Env.try_solve_implicits_hook);
                 FStar_TypeChecker_Env.splice =
                   (env.FStar_TypeChecker_Env.splice);
                 FStar_TypeChecker_Env.mpreprocess =
                   (env.FStar_TypeChecker_Env.mpreprocess);
                 FStar_TypeChecker_Env.postprocess =
                   (env.FStar_TypeChecker_Env.postprocess);
                 FStar_TypeChecker_Env.identifier_info =
                   (env.FStar_TypeChecker_Env.identifier_info);
                 FStar_TypeChecker_Env.tc_hooks =
                   (env.FStar_TypeChecker_Env.tc_hooks);
                 FStar_TypeChecker_Env.dsenv =
                   (env.FStar_TypeChecker_Env.dsenv);
                 FStar_TypeChecker_Env.nbe = (env.FStar_TypeChecker_Env.nbe);
                 FStar_TypeChecker_Env.strict_args_tab =
                   (env.FStar_TypeChecker_Env.strict_args_tab);
                 FStar_TypeChecker_Env.erasable_types_tab =
                   (env.FStar_TypeChecker_Env.erasable_types_tab);
                 FStar_TypeChecker_Env.enable_defer_to_tac =
                   (env.FStar_TypeChecker_Env.enable_defer_to_tac);
                 FStar_TypeChecker_Env.unif_allow_ref_guards =
                   (env.FStar_TypeChecker_Env.unif_allow_ref_guards);
                 FStar_TypeChecker_Env.erase_erasable_args =
                   (env.FStar_TypeChecker_Env.erase_erasable_args);
                 FStar_TypeChecker_Env.core_check =
                   (env.FStar_TypeChecker_Env.core_check)
               } in
             let uu___2 =
               core_check_and_maybe_add_to_guard_uvar env1 ctx_u tm uvar_ty
                 false in
             match uu___2 with
             | FStar_Pervasives.Inl (FStar_Pervasives_Native.None) ->
                 FStar_Pervasives_Native.None
             | FStar_Pervasives.Inl (FStar_Pervasives_Native.Some g) ->
                 let g1 =
                   {
                     FStar_TypeChecker_Common.guard_f =
                       (FStar_TypeChecker_Common.NonTrivial g);
                     FStar_TypeChecker_Common.deferred_to_tac =
                       (FStar_TypeChecker_Common.trivial_guard.FStar_TypeChecker_Common.deferred_to_tac);
                     FStar_TypeChecker_Common.deferred =
                       (FStar_TypeChecker_Common.trivial_guard.FStar_TypeChecker_Common.deferred);
                     FStar_TypeChecker_Common.univ_ineqs =
                       (FStar_TypeChecker_Common.trivial_guard.FStar_TypeChecker_Common.univ_ineqs);
                     FStar_TypeChecker_Common.implicits =
                       (FStar_TypeChecker_Common.trivial_guard.FStar_TypeChecker_Common.implicits)
                   } in
                 (force_trivial_guard env1 g1; FStar_Pervasives_Native.None)
             | FStar_Pervasives.Inr err ->
                 ((let uu___4 = FStar_TypeChecker_Env.get_range env1 in
                   let uu___5 =
                     let uu___6 =
                       let uu___7 = FStar_Syntax_Print.term_to_string tm in
                       let uu___8 = FStar_Syntax_Print.term_to_string uvar_ty in
                       let uu___9 = err false in
                       FStar_Compiler_Util.format3
                         "Term %s computed by tactic does not have type %s, because %s"
                         uu___7 uu___8 uu___9 in
                     (FStar_Errors.Error_TypeError, uu___6) in
                   FStar_Errors.log_issue uu___4 uu___5);
                  FStar_Pervasives_Native.None))
and (resolve_implicits' :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      FStar_TypeChecker_Env.implicits ->
        (FStar_TypeChecker_Common.implicit * implicit_checking_status)
          Prims.list)
  =
  fun env ->
    fun is_tac ->
      fun implicits ->
        let rec until_fixpoint acc implicits1 =
          let uu___ = acc in
          match uu___ with
          | (out, changed) ->
              (match implicits1 with
               | [] ->
                   if Prims.op_Negation changed
                   then
                     let uu___1 =
                       let uu___2 =
                         FStar_Compiler_List.map FStar_Pervasives_Native.fst
                           out in
                       try_solve_single_valued_implicits env is_tac uu___2 in
                     (match uu___1 with
                      | (imps, changed1) ->
                          if changed1
                          then until_fixpoint ([], false) imps
                          else
                            (let uu___3 = pick_a_univ_deffered_implicit out in
                             match uu___3 with
                             | (imp_opt, rest) ->
                                 (match imp_opt with
                                  | FStar_Pervasives_Native.None -> rest
                                  | FStar_Pervasives_Native.Some imp ->
                                      let force_univ_constraints = true in
                                      let imps1 =
                                        let uu___4 =
                                          check_implicit_solution_and_discharge_guard
                                            env imp force_univ_constraints in
                                        FStar_Compiler_Effect.op_Bar_Greater
                                          uu___4 FStar_Compiler_Util.must in
                                      let uu___4 =
                                        let uu___5 =
                                          FStar_Compiler_List.map
                                            FStar_Pervasives_Native.fst rest in
                                        FStar_Compiler_List.op_At imps1
                                          uu___5 in
                                      until_fixpoint ([], false) uu___4)))
                   else
                     (let uu___2 =
                        FStar_Compiler_List.map FStar_Pervasives_Native.fst
                          out in
                      until_fixpoint ([], false) uu___2)
               | hd::tl ->
                   let uu___1 = hd in
                   (match uu___1 with
                    | { FStar_TypeChecker_Common.imp_reason = reason;
                        FStar_TypeChecker_Common.imp_uvar = ctx_u;
                        FStar_TypeChecker_Common.imp_tm = tm;
                        FStar_TypeChecker_Common.imp_range = r;_} ->
                        let uu___2 =
                          FStar_Syntax_Unionfind.find_decoration
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
                        (match uu___2 with
                         | {
                             FStar_Syntax_Syntax.uvar_decoration_typ =
                               uvar_decoration_typ;
                             FStar_Syntax_Syntax.uvar_decoration_should_check
                               = uvar_decoration_should_check;
                             FStar_Syntax_Syntax.uvar_decoration_kind =
                               uu___3;_}
                             ->
                             ((let uu___5 =
                                 FStar_Compiler_Effect.op_Less_Bar
                                   (FStar_TypeChecker_Env.debug env)
                                   (FStar_Options.Other "Rel") in
                               if uu___5
                               then
                                 let uu___6 =
                                   FStar_Syntax_Print.term_to_string tm in
                                 let uu___7 =
                                   FStar_Syntax_Print.ctx_uvar_to_string
                                     ctx_u in
                                 let uu___8 =
                                   FStar_Compiler_Util.string_of_bool is_tac in
                                 FStar_Compiler_Util.print3
                                   "resolve_implicits' loop, imp_tm = %s and ctx_u = %s, is_tac: %s\n"
                                   uu___6 uu___7 uu___8
                               else ());
                              if
                                FStar_Syntax_Syntax.uu___is_Allow_unresolved
                                  uvar_decoration_should_check
                              then until_fixpoint (out, true) tl
                              else
                                (let uu___6 = unresolved ctx_u in
                                 if uu___6
                                 then
                                   (if flex_uvar_has_meta_tac ctx_u
                                    then
                                      let t = run_meta_arg_tac ctx_u in
                                      let extra =
                                        let uu___7 = teq_nosmt env t tm in
                                        match uu___7 with
                                        | FStar_Pervasives_Native.None ->
                                            failwith
                                              "resolve_implicits: unifying with an unresolved uvar failed?"
                                        | FStar_Pervasives_Native.Some g ->
                                            g.FStar_TypeChecker_Common.implicits in
                                      until_fixpoint (out, true)
                                        (FStar_Compiler_List.op_At extra tl)
                                    else
                                      until_fixpoint
                                        (((hd, Implicit_unresolved) :: out),
                                          changed) tl)
                                 else
                                   if
                                     (FStar_Syntax_Syntax.uu___is_Allow_untyped
                                        uvar_decoration_should_check)
                                       ||
                                       (FStar_Syntax_Syntax.uu___is_Already_checked
                                          uvar_decoration_should_check)
                                   then until_fixpoint (out, true) tl
                                   else
                                     (let env1 =
                                        {
                                          FStar_TypeChecker_Env.solver =
                                            (env.FStar_TypeChecker_Env.solver);
                                          FStar_TypeChecker_Env.range =
                                            (env.FStar_TypeChecker_Env.range);
                                          FStar_TypeChecker_Env.curmodule =
                                            (env.FStar_TypeChecker_Env.curmodule);
                                          FStar_TypeChecker_Env.gamma =
                                            (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                          FStar_TypeChecker_Env.gamma_sig =
                                            (env.FStar_TypeChecker_Env.gamma_sig);
                                          FStar_TypeChecker_Env.gamma_cache =
                                            (env.FStar_TypeChecker_Env.gamma_cache);
                                          FStar_TypeChecker_Env.modules =
                                            (env.FStar_TypeChecker_Env.modules);
                                          FStar_TypeChecker_Env.expected_typ
                                            =
                                            (env.FStar_TypeChecker_Env.expected_typ);
                                          FStar_TypeChecker_Env.sigtab =
                                            (env.FStar_TypeChecker_Env.sigtab);
                                          FStar_TypeChecker_Env.attrtab =
                                            (env.FStar_TypeChecker_Env.attrtab);
                                          FStar_TypeChecker_Env.instantiate_imp
                                            =
                                            (env.FStar_TypeChecker_Env.instantiate_imp);
                                          FStar_TypeChecker_Env.effects =
                                            (env.FStar_TypeChecker_Env.effects);
                                          FStar_TypeChecker_Env.generalize =
                                            (env.FStar_TypeChecker_Env.generalize);
                                          FStar_TypeChecker_Env.letrecs =
                                            (env.FStar_TypeChecker_Env.letrecs);
                                          FStar_TypeChecker_Env.top_level =
                                            (env.FStar_TypeChecker_Env.top_level);
                                          FStar_TypeChecker_Env.check_uvars =
                                            (env.FStar_TypeChecker_Env.check_uvars);
                                          FStar_TypeChecker_Env.use_eq_strict
                                            =
                                            (env.FStar_TypeChecker_Env.use_eq_strict);
                                          FStar_TypeChecker_Env.is_iface =
                                            (env.FStar_TypeChecker_Env.is_iface);
                                          FStar_TypeChecker_Env.admit =
                                            (env.FStar_TypeChecker_Env.admit);
                                          FStar_TypeChecker_Env.lax =
                                            (env.FStar_TypeChecker_Env.lax);
                                          FStar_TypeChecker_Env.lax_universes
                                            =
                                            (env.FStar_TypeChecker_Env.lax_universes);
                                          FStar_TypeChecker_Env.phase1 =
                                            (env.FStar_TypeChecker_Env.phase1);
                                          FStar_TypeChecker_Env.failhard =
                                            (env.FStar_TypeChecker_Env.failhard);
                                          FStar_TypeChecker_Env.nosynth =
                                            (env.FStar_TypeChecker_Env.nosynth);
                                          FStar_TypeChecker_Env.uvar_subtyping
                                            =
                                            (env.FStar_TypeChecker_Env.uvar_subtyping);
                                          FStar_TypeChecker_Env.tc_term =
                                            (env.FStar_TypeChecker_Env.tc_term);
                                          FStar_TypeChecker_Env.typeof_tot_or_gtot_term
                                            =
                                            (env.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                                          FStar_TypeChecker_Env.universe_of =
                                            (env.FStar_TypeChecker_Env.universe_of);
                                          FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                            =
                                            (env.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                          FStar_TypeChecker_Env.teq_nosmt_force
                                            =
                                            (env.FStar_TypeChecker_Env.teq_nosmt_force);
                                          FStar_TypeChecker_Env.subtype_nosmt_force
                                            =
                                            (env.FStar_TypeChecker_Env.subtype_nosmt_force);
                                          FStar_TypeChecker_Env.use_bv_sorts
                                            =
                                            (env.FStar_TypeChecker_Env.use_bv_sorts);
                                          FStar_TypeChecker_Env.qtbl_name_and_index
                                            =
                                            (env.FStar_TypeChecker_Env.qtbl_name_and_index);
                                          FStar_TypeChecker_Env.normalized_eff_names
                                            =
                                            (env.FStar_TypeChecker_Env.normalized_eff_names);
                                          FStar_TypeChecker_Env.fv_delta_depths
                                            =
                                            (env.FStar_TypeChecker_Env.fv_delta_depths);
                                          FStar_TypeChecker_Env.proof_ns =
                                            (env.FStar_TypeChecker_Env.proof_ns);
                                          FStar_TypeChecker_Env.synth_hook =
                                            (env.FStar_TypeChecker_Env.synth_hook);
                                          FStar_TypeChecker_Env.try_solve_implicits_hook
                                            =
                                            (env.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                          FStar_TypeChecker_Env.splice =
                                            (env.FStar_TypeChecker_Env.splice);
                                          FStar_TypeChecker_Env.mpreprocess =
                                            (env.FStar_TypeChecker_Env.mpreprocess);
                                          FStar_TypeChecker_Env.postprocess =
                                            (env.FStar_TypeChecker_Env.postprocess);
                                          FStar_TypeChecker_Env.identifier_info
                                            =
                                            (env.FStar_TypeChecker_Env.identifier_info);
                                          FStar_TypeChecker_Env.tc_hooks =
                                            (env.FStar_TypeChecker_Env.tc_hooks);
                                          FStar_TypeChecker_Env.dsenv =
                                            (env.FStar_TypeChecker_Env.dsenv);
                                          FStar_TypeChecker_Env.nbe =
                                            (env.FStar_TypeChecker_Env.nbe);
                                          FStar_TypeChecker_Env.strict_args_tab
                                            =
                                            (env.FStar_TypeChecker_Env.strict_args_tab);
                                          FStar_TypeChecker_Env.erasable_types_tab
                                            =
                                            (env.FStar_TypeChecker_Env.erasable_types_tab);
                                          FStar_TypeChecker_Env.enable_defer_to_tac
                                            =
                                            (env.FStar_TypeChecker_Env.enable_defer_to_tac);
                                          FStar_TypeChecker_Env.unif_allow_ref_guards
                                            =
                                            (env.FStar_TypeChecker_Env.unif_allow_ref_guards);
                                          FStar_TypeChecker_Env.erase_erasable_args
                                            =
                                            (env.FStar_TypeChecker_Env.erase_erasable_args);
                                          FStar_TypeChecker_Env.core_check =
                                            (env.FStar_TypeChecker_Env.core_check)
                                        } in
                                      let tm1 =
                                        norm_with_steps
                                          "FStar.TypeChecker.Rel.norm_with_steps.8"
                                          [FStar_TypeChecker_Env.Beta] env1
                                          tm in
                                      let hd1 =
                                        {
                                          FStar_TypeChecker_Common.imp_reason
                                            =
                                            (hd.FStar_TypeChecker_Common.imp_reason);
                                          FStar_TypeChecker_Common.imp_uvar =
                                            (hd.FStar_TypeChecker_Common.imp_uvar);
                                          FStar_TypeChecker_Common.imp_tm =
                                            tm1;
                                          FStar_TypeChecker_Common.imp_range
                                            =
                                            (hd.FStar_TypeChecker_Common.imp_range)
                                        } in
                                      let tm_ok_for_tac uu___9 =
                                        let uu___10 =
                                          is_implicit_resolved env1 hd1 in
                                        if uu___10
                                        then
                                          (if
                                             env1.FStar_TypeChecker_Env.phase1
                                           then FStar_Pervasives_Native.None
                                           else
                                             check_implicit_solution_for_tac
                                               env1 hd1)
                                        else FStar_Pervasives_Native.None in
                                      if is_tac
                                      then
                                        let uu___9 = tm_ok_for_tac () in
                                        match uu___9 with
                                        | FStar_Pervasives_Native.None ->
                                            until_fixpoint (out, true) tl
                                        | FStar_Pervasives_Native.Some
                                            (tm2, ty) ->
                                            until_fixpoint
                                              (((hd1,
                                                  (Implicit_has_typing_guard
                                                     (tm2, ty))) :: out),
                                                changed) tl
                                      else
                                        (let force_univ_constraints = false in
                                         let imps_opt =
                                           check_implicit_solution_and_discharge_guard
                                             env1 hd1 force_univ_constraints in
                                         match imps_opt with
                                         | FStar_Pervasives_Native.None ->
                                             until_fixpoint
                                               (((hd1,
                                                   Implicit_checking_defers_univ_constraint)
                                                 :: out), changed) tl
                                         | FStar_Pervasives_Native.Some imps
                                             ->
                                             let uu___10 =
                                               let uu___11 =
                                                 let uu___12 =
                                                   FStar_Compiler_Effect.op_Bar_Greater
                                                     imps
                                                     (FStar_Compiler_List.map
                                                        (fun i ->
                                                           (i,
                                                             Implicit_unresolved))) in
                                                 FStar_Compiler_List.op_At
                                                   uu___12 out in
                                               (uu___11, true) in
                                             until_fixpoint uu___10 tl))))))) in
        until_fixpoint ([], false) implicits
and (resolve_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun g ->
      (let uu___1 =
         FStar_Compiler_Effect.op_Less_Bar (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook") in
       if uu___1
       then
         let uu___2 = guard_to_string env g in
         FStar_Compiler_Util.print1
           "//////////////////////////ResolveImplicitsHook: resolve_implicits////////////\nguard = %s\n"
           uu___2
       else ());
      (let tagged_implicits1 =
         resolve_implicits' env false g.FStar_TypeChecker_Common.implicits in
       let uu___1 =
         FStar_Compiler_List.map FStar_Pervasives_Native.fst
           tagged_implicits1 in
       {
         FStar_TypeChecker_Common.guard_f =
           (g.FStar_TypeChecker_Common.guard_f);
         FStar_TypeChecker_Common.deferred_to_tac =
           (g.FStar_TypeChecker_Common.deferred_to_tac);
         FStar_TypeChecker_Common.deferred =
           (g.FStar_TypeChecker_Common.deferred);
         FStar_TypeChecker_Common.univ_ineqs =
           (g.FStar_TypeChecker_Common.univ_ineqs);
         FStar_TypeChecker_Common.implicits = uu___1
       })
and (force_trivial_guard :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.guard_t -> unit) =
  fun env ->
    fun g ->
      (let uu___1 =
         FStar_Compiler_Effect.op_Less_Bar (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook") in
       if uu___1
       then
         let uu___2 = guard_to_string env g in
         FStar_Compiler_Util.print1
           "//////////////////////////ResolveImplicitsHook: force_trivial_guard////////////\nguard = %s\n"
           uu___2
       else ());
      (let g1 = solve_deferred_constraints env g in
       let g2 = resolve_implicits env g1 in
       match g2.FStar_TypeChecker_Common.implicits with
       | [] ->
           let uu___1 = discharge_guard env g2 in
           FStar_Compiler_Effect.op_Less_Bar (fun uu___2 -> ()) uu___1
       | imp::uu___1 ->
           let uu___2 =
             let uu___3 =
               let uu___4 =
                 FStar_Syntax_Print.uvar_to_string
                   (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
               let uu___5 =
                 let uu___6 =
                   FStar_Syntax_Util.ctx_uvar_typ
                     imp.FStar_TypeChecker_Common.imp_uvar in
                 FStar_TypeChecker_Normalize.term_to_string env uu___6 in
               FStar_Compiler_Util.format3
                 "Failed to resolve implicit argument %s of type %s introduced for %s"
                 uu___4 uu___5 imp.FStar_TypeChecker_Common.imp_reason in
             (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu___3) in
           FStar_Errors.raise_error uu___2
             imp.FStar_TypeChecker_Common.imp_range)
let (resolve_implicits_tac :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> tagged_implicits)
  =
  fun env ->
    fun g -> resolve_implicits' env true g.FStar_TypeChecker_Common.implicits
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu___ = subtype_nosmt env t1 t2 in
        match uu___ with
        | FStar_Pervasives_Native.None -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
let (teq_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env ->
    fun t1 ->
      fun t2 -> let uu___ = teq env t1 t2 in force_trivial_guard env uu___
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu___ = teq_nosmt env t1 t2 in
        match uu___ with
        | FStar_Pervasives_Native.None -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
let (layered_effect_teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        Prims.string FStar_Pervasives_Native.option ->
          FStar_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        fun reason ->
          (let uu___1 =
             FStar_Compiler_Effect.op_Less_Bar
               (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffectsEqns") in
           if uu___1
           then
             let uu___2 =
               let uu___3 =
                 FStar_Compiler_Effect.op_Bar_Greater reason
                   FStar_Compiler_Util.is_none in
               if uu___3
               then "_"
               else
                 FStar_Compiler_Effect.op_Bar_Greater reason
                   FStar_Compiler_Util.must in
             let uu___3 = FStar_Syntax_Print.term_to_string t1 in
             let uu___4 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Compiler_Util.print3 "Layered Effect (%s) %s = %s\n"
               uu___2 uu___3 uu___4
           else ());
          teq env t1 t2
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Common.guard_t)
  =
  fun u1 ->
    fun u2 ->
      {
        FStar_TypeChecker_Common.guard_f =
          (FStar_TypeChecker_Common.trivial_guard.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred_to_tac =
          (FStar_TypeChecker_Common.trivial_guard.FStar_TypeChecker_Common.deferred_to_tac);
        FStar_TypeChecker_Common.deferred =
          (FStar_TypeChecker_Common.trivial_guard.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (FStar_TypeChecker_Common.trivial_guard.FStar_TypeChecker_Common.implicits)
      }