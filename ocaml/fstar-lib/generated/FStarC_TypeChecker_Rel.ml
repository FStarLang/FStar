open Prims
type match_result =
  | MisMatch of (FStarC_Syntax_Syntax.delta_depth
  FStar_Pervasives_Native.option * FStarC_Syntax_Syntax.delta_depth
  FStar_Pervasives_Native.option) 
  | HeadMatch of Prims.bool 
  | FullMatch 
let (uu___is_MisMatch : match_result -> Prims.bool) =
  fun projectee ->
    match projectee with | MisMatch _0 -> true | uu___ -> false
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStarC_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStarC_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
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
  | Implicit_has_typing_guard of (FStarC_Syntax_Syntax.term *
  FStarC_Syntax_Syntax.typ) 
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
    (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.typ))
  =
  fun projectee -> match projectee with | Implicit_has_typing_guard _0 -> _0
let (dbg_Disch : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "Disch"
let (dbg_Discharge : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "Discharge"
let (dbg_EQ : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "EQ"
let (dbg_ExplainRel : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "ExplainRel"
let (dbg_GenUniverses : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "GenUniverses"
let (dbg_ImplicitTrace : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "ImplicitTrace"
let (dbg_Imps : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "Imps"
let (dbg_LayeredEffectsApp : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "LayeredEffectsApp"
let (dbg_LayeredEffectsEqns : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "LayeredEffectsEqns"
let (dbg_Rel : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "Rel"
let (dbg_RelBench : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "RelBench"
let (dbg_RelDelta : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "RelDelta"
let (dbg_RelTop : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "RelTop"
let (dbg_ResolveImplicitsHook : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "ResolveImplicitsHook"
let (dbg_Simplification : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "Simplification"
let (dbg_SMTQuery : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "SMTQuery"
let (dbg_Tac : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "Tac"
let (showable_implicit_checking_status :
  implicit_checking_status FStarC_Class_Show.showable) =
  {
    FStarC_Class_Show.show =
      (fun uu___ ->
         match uu___ with
         | Implicit_unresolved -> "Implicit_unresolved"
         | Implicit_checking_defers_univ_constraint ->
             "Implicit_checking_defers_univ_constraint"
         | Implicit_has_typing_guard (tm, typ) -> "Implicit_has_typing_guard")
  }
type tagged_implicits =
  (FStarC_TypeChecker_Common.implicit * implicit_checking_status) Prims.list
let (is_base_type :
  FStarC_TypeChecker_Env.env -> FStarC_Syntax_Syntax.typ -> Prims.bool) =
  fun env ->
    fun typ ->
      let t = FStarC_TypeChecker_Normalize.unfold_whnf env typ in
      let uu___ = FStarC_Syntax_Util.head_and_args t in
      match uu___ with
      | (head, args) ->
          let uu___1 =
            let uu___2 =
              let uu___3 = FStarC_Syntax_Util.un_uinst head in
              FStarC_Syntax_Util.unascribe uu___3 in
            uu___2.FStarC_Syntax_Syntax.n in
          (match uu___1 with
           | FStarC_Syntax_Syntax.Tm_name uu___2 -> true
           | FStarC_Syntax_Syntax.Tm_fvar uu___2 -> true
           | FStarC_Syntax_Syntax.Tm_type uu___2 -> true
           | uu___2 -> false)
let (term_is_uvar :
  FStarC_Syntax_Syntax.ctx_uvar -> FStarC_Syntax_Syntax.term -> Prims.bool) =
  fun uv ->
    fun t ->
      let uu___ =
        let uu___1 = FStarC_Syntax_Util.unascribe t in
        uu___1.FStarC_Syntax_Syntax.n in
      match uu___ with
      | FStarC_Syntax_Syntax.Tm_uvar (uv', uu___1) ->
          FStarC_Syntax_Unionfind.equiv uv.FStarC_Syntax_Syntax.ctx_uvar_head
            uv'.FStarC_Syntax_Syntax.ctx_uvar_head
      | uu___1 -> false
let (binders_as_bv_set :
  FStarC_Syntax_Syntax.binders ->
    FStarC_Syntax_Syntax.bv FStarC_Compiler_FlatSet.t)
  =
  fun uu___ ->
    (fun bs ->
       let uu___ =
         FStarC_Compiler_List.map (fun b -> b.FStarC_Syntax_Syntax.binder_bv)
           bs in
       Obj.magic
         (FStarC_Class_Setlike.from_list ()
            (Obj.magic
               (FStarC_Compiler_FlatSet.setlike_flat_set
                  FStarC_Syntax_Syntax.ord_bv)) uu___)) uu___
type lstring = Prims.string FStarC_Thunk.t
let (mklstr : (unit -> Prims.string) -> Prims.string FStarC_Thunk.thunk) =
  fun f ->
    let uf = FStarC_Syntax_Unionfind.get () in
    FStarC_Thunk.mk
      (fun uu___ ->
         let tx = FStarC_Syntax_Unionfind.new_transaction () in
         FStarC_Syntax_Unionfind.set uf;
         (let r = f () in FStarC_Syntax_Unionfind.rollback tx; r))
type uvi =
  | TERM of (FStarC_Syntax_Syntax.ctx_uvar * FStarC_Syntax_Syntax.term) 
  | UNIV of (FStarC_Syntax_Syntax.universe_uvar *
  FStarC_Syntax_Syntax.universe) 
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee -> match projectee with | TERM _0 -> true | uu___ -> false
let (__proj__TERM__item___0 :
  uvi -> (FStarC_Syntax_Syntax.ctx_uvar * FStarC_Syntax_Syntax.term)) =
  fun projectee -> match projectee with | TERM _0 -> _0
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee -> match projectee with | UNIV _0 -> true | uu___ -> false
let (__proj__UNIV__item___0 :
  uvi -> (FStarC_Syntax_Syntax.universe_uvar * FStarC_Syntax_Syntax.universe))
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
let (uu___0 : defer_ok_t FStarC_Class_Show.showable) =
  {
    FStarC_Class_Show.show =
      (fun uu___ ->
         match uu___ with
         | NoDefer -> "NoDefer"
         | DeferAny -> "DeferAny"
         | DeferFlexFlexOnly -> "DeferFlexFlexOnly")
  }
type worklist =
  {
  attempting: FStarC_TypeChecker_Common.probs ;
  wl_deferred:
    (Prims.int * FStarC_TypeChecker_Common.deferred_reason * lstring *
      FStarC_TypeChecker_Common.prob) FStarC_Compiler_CList.clist
    ;
  wl_deferred_to_tac:
    (Prims.int * FStarC_TypeChecker_Common.deferred_reason * lstring *
      FStarC_TypeChecker_Common.prob) FStarC_Compiler_CList.clist
    ;
  ctr: Prims.int ;
  defer_ok: defer_ok_t ;
  smt_ok: Prims.bool ;
  umax_heuristic_ok: Prims.bool ;
  tcenv: FStarC_TypeChecker_Env.env ;
  wl_implicits: FStarC_TypeChecker_Common.implicits_t ;
  repr_subcomp_allowed: Prims.bool ;
  typeclass_variables: FStarC_Syntax_Syntax.ctx_uvar FStarC_Compiler_RBSet.t }
let (__proj__Mkworklist__item__attempting :
  worklist -> FStarC_TypeChecker_Common.probs) =
  fun projectee ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits; repr_subcomp_allowed;
        typeclass_variables;_} -> attempting
let (__proj__Mkworklist__item__wl_deferred :
  worklist ->
    (Prims.int * FStarC_TypeChecker_Common.deferred_reason * lstring *
      FStarC_TypeChecker_Common.prob) FStarC_Compiler_CList.clist)
  =
  fun projectee ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits; repr_subcomp_allowed;
        typeclass_variables;_} -> wl_deferred
let (__proj__Mkworklist__item__wl_deferred_to_tac :
  worklist ->
    (Prims.int * FStarC_TypeChecker_Common.deferred_reason * lstring *
      FStarC_TypeChecker_Common.prob) FStarC_Compiler_CList.clist)
  =
  fun projectee ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits; repr_subcomp_allowed;
        typeclass_variables;_} -> wl_deferred_to_tac
let (__proj__Mkworklist__item__ctr : worklist -> Prims.int) =
  fun projectee ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits; repr_subcomp_allowed;
        typeclass_variables;_} -> ctr
let (__proj__Mkworklist__item__defer_ok : worklist -> defer_ok_t) =
  fun projectee ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits; repr_subcomp_allowed;
        typeclass_variables;_} -> defer_ok
let (__proj__Mkworklist__item__smt_ok : worklist -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits; repr_subcomp_allowed;
        typeclass_variables;_} -> smt_ok
let (__proj__Mkworklist__item__umax_heuristic_ok : worklist -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits; repr_subcomp_allowed;
        typeclass_variables;_} -> umax_heuristic_ok
let (__proj__Mkworklist__item__tcenv :
  worklist -> FStarC_TypeChecker_Env.env) =
  fun projectee ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits; repr_subcomp_allowed;
        typeclass_variables;_} -> tcenv
let (__proj__Mkworklist__item__wl_implicits :
  worklist -> FStarC_TypeChecker_Common.implicits_t) =
  fun projectee ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits; repr_subcomp_allowed;
        typeclass_variables;_} -> wl_implicits
let (__proj__Mkworklist__item__repr_subcomp_allowed : worklist -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits; repr_subcomp_allowed;
        typeclass_variables;_} -> repr_subcomp_allowed
let (__proj__Mkworklist__item__typeclass_variables :
  worklist -> FStarC_Syntax_Syntax.ctx_uvar FStarC_Compiler_RBSet.t) =
  fun projectee ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits; repr_subcomp_allowed;
        typeclass_variables;_} -> typeclass_variables
let (as_deferred :
  (Prims.int * FStarC_TypeChecker_Common.deferred_reason * lstring *
    FStarC_TypeChecker_Common.prob) FStarC_Compiler_CList.clist ->
    FStarC_TypeChecker_Common.deferred)
  =
  fun wl_def ->
    FStarC_Compiler_CList.map
      (fun uu___ ->
         match uu___ with
         | (uu___1, reason, m, p) ->
             let uu___2 = FStarC_Thunk.force m in (reason, uu___2, p)) wl_def
let (as_wl_deferred :
  worklist ->
    FStarC_TypeChecker_Common.deferred ->
      (Prims.int * FStarC_TypeChecker_Common.deferred_reason * lstring *
        FStarC_TypeChecker_Common.prob) FStarC_Compiler_CList.clist)
  =
  fun wl ->
    fun d ->
      FStarC_Compiler_CList.map
        (fun uu___ ->
           match uu___ with
           | (reason, m, p) ->
               let uu___1 = FStarC_Thunk.mkv m in
               ((wl.ctr), reason, uu___1, p)) d
let (new_uvar :
  Prims.string ->
    worklist ->
      FStarC_Compiler_Range_Type.range ->
        FStarC_Syntax_Syntax.binding Prims.list ->
          FStarC_Syntax_Syntax.binder Prims.list ->
            FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
              FStarC_Syntax_Syntax.should_check_uvar ->
                FStarC_Syntax_Syntax.ctx_uvar_meta_t
                  FStar_Pervasives_Native.option ->
                  (FStarC_Syntax_Syntax.ctx_uvar * FStarC_Syntax_Syntax.term
                    * worklist))
  =
  fun reason ->
    fun wl ->
      fun r ->
        fun gamma ->
          fun binders ->
            fun k ->
              fun should_check ->
                fun meta ->
                  let decoration =
                    {
                      FStarC_Syntax_Syntax.uvar_decoration_typ = k;
                      FStarC_Syntax_Syntax.uvar_decoration_typedness_depends_on
                        = [];
                      FStarC_Syntax_Syntax.uvar_decoration_should_check =
                        should_check;
                      FStarC_Syntax_Syntax.uvar_decoration_should_unrefine =
                        false
                    } in
                  let ctx_uvar =
                    let uu___ = FStarC_Syntax_Unionfind.fresh decoration r in
                    {
                      FStarC_Syntax_Syntax.ctx_uvar_head = uu___;
                      FStarC_Syntax_Syntax.ctx_uvar_gamma = gamma;
                      FStarC_Syntax_Syntax.ctx_uvar_binders = binders;
                      FStarC_Syntax_Syntax.ctx_uvar_reason = reason;
                      FStarC_Syntax_Syntax.ctx_uvar_range = r;
                      FStarC_Syntax_Syntax.ctx_uvar_meta = meta
                    } in
                  FStarC_TypeChecker_Common.check_uvar_ctx_invariant reason r
                    true gamma binders;
                  (let t =
                     FStarC_Syntax_Syntax.mk
                       (FStarC_Syntax_Syntax.Tm_uvar
                          (ctx_uvar, ([], FStarC_Syntax_Syntax.NoUseRange)))
                       r in
                   let imp =
                     {
                       FStarC_TypeChecker_Common.imp_reason = reason;
                       FStarC_TypeChecker_Common.imp_uvar = ctx_uvar;
                       FStarC_TypeChecker_Common.imp_tm = t;
                       FStarC_TypeChecker_Common.imp_range = r
                     } in
                   (let uu___2 =
                      FStarC_Compiler_Effect.op_Bang dbg_ImplicitTrace in
                    if uu___2
                    then
                      let uu___3 =
                        FStarC_Class_Show.show
                          FStarC_Syntax_Print.showable_uvar
                          ctx_uvar.FStarC_Syntax_Syntax.ctx_uvar_head in
                      FStarC_Compiler_Util.print1
                        "Just created uvar (Rel) {%s}\n" uu___3
                    else ());
                   (let uu___2 =
                      let uu___3 =
                        Obj.magic
                          (FStarC_Class_Listlike.cons ()
                             (Obj.magic
                                (FStarC_Compiler_CList.listlike_clist ()))
                             imp (Obj.magic wl.wl_implicits)) in
                      {
                        attempting = (wl.attempting);
                        wl_deferred = (wl.wl_deferred);
                        wl_deferred_to_tac = (wl.wl_deferred_to_tac);
                        ctr = (wl.ctr);
                        defer_ok = (wl.defer_ok);
                        smt_ok = (wl.smt_ok);
                        umax_heuristic_ok = (wl.umax_heuristic_ok);
                        tcenv = (wl.tcenv);
                        wl_implicits = uu___3;
                        repr_subcomp_allowed = (wl.repr_subcomp_allowed);
                        typeclass_variables = (wl.typeclass_variables)
                      } in
                    (ctx_uvar, t, uu___2)))
let (copy_uvar :
  FStarC_Syntax_Syntax.ctx_uvar ->
    FStarC_Syntax_Syntax.binders ->
      FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
        worklist ->
          (FStarC_Syntax_Syntax.ctx_uvar * FStarC_Syntax_Syntax.term *
            worklist))
  =
  fun u ->
    fun bs ->
      fun t ->
        fun wl ->
          let env =
            let uu___ = wl.tcenv in
            {
              FStarC_TypeChecker_Env.solver =
                (uu___.FStarC_TypeChecker_Env.solver);
              FStarC_TypeChecker_Env.range =
                (uu___.FStarC_TypeChecker_Env.range);
              FStarC_TypeChecker_Env.curmodule =
                (uu___.FStarC_TypeChecker_Env.curmodule);
              FStarC_TypeChecker_Env.gamma =
                (u.FStarC_Syntax_Syntax.ctx_uvar_gamma);
              FStarC_TypeChecker_Env.gamma_sig =
                (uu___.FStarC_TypeChecker_Env.gamma_sig);
              FStarC_TypeChecker_Env.gamma_cache =
                (uu___.FStarC_TypeChecker_Env.gamma_cache);
              FStarC_TypeChecker_Env.modules =
                (uu___.FStarC_TypeChecker_Env.modules);
              FStarC_TypeChecker_Env.expected_typ =
                (uu___.FStarC_TypeChecker_Env.expected_typ);
              FStarC_TypeChecker_Env.sigtab =
                (uu___.FStarC_TypeChecker_Env.sigtab);
              FStarC_TypeChecker_Env.attrtab =
                (uu___.FStarC_TypeChecker_Env.attrtab);
              FStarC_TypeChecker_Env.instantiate_imp =
                (uu___.FStarC_TypeChecker_Env.instantiate_imp);
              FStarC_TypeChecker_Env.effects =
                (uu___.FStarC_TypeChecker_Env.effects);
              FStarC_TypeChecker_Env.generalize =
                (uu___.FStarC_TypeChecker_Env.generalize);
              FStarC_TypeChecker_Env.letrecs =
                (uu___.FStarC_TypeChecker_Env.letrecs);
              FStarC_TypeChecker_Env.top_level =
                (uu___.FStarC_TypeChecker_Env.top_level);
              FStarC_TypeChecker_Env.check_uvars =
                (uu___.FStarC_TypeChecker_Env.check_uvars);
              FStarC_TypeChecker_Env.use_eq_strict =
                (uu___.FStarC_TypeChecker_Env.use_eq_strict);
              FStarC_TypeChecker_Env.is_iface =
                (uu___.FStarC_TypeChecker_Env.is_iface);
              FStarC_TypeChecker_Env.admit =
                (uu___.FStarC_TypeChecker_Env.admit);
              FStarC_TypeChecker_Env.lax_universes =
                (uu___.FStarC_TypeChecker_Env.lax_universes);
              FStarC_TypeChecker_Env.phase1 =
                (uu___.FStarC_TypeChecker_Env.phase1);
              FStarC_TypeChecker_Env.failhard =
                (uu___.FStarC_TypeChecker_Env.failhard);
              FStarC_TypeChecker_Env.flychecking =
                (uu___.FStarC_TypeChecker_Env.flychecking);
              FStarC_TypeChecker_Env.uvar_subtyping =
                (uu___.FStarC_TypeChecker_Env.uvar_subtyping);
              FStarC_TypeChecker_Env.intactics =
                (uu___.FStarC_TypeChecker_Env.intactics);
              FStarC_TypeChecker_Env.nocoerce =
                (uu___.FStarC_TypeChecker_Env.nocoerce);
              FStarC_TypeChecker_Env.tc_term =
                (uu___.FStarC_TypeChecker_Env.tc_term);
              FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
                (uu___.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
              FStarC_TypeChecker_Env.universe_of =
                (uu___.FStarC_TypeChecker_Env.universe_of);
              FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
                (uu___.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
              FStarC_TypeChecker_Env.teq_nosmt_force =
                (uu___.FStarC_TypeChecker_Env.teq_nosmt_force);
              FStarC_TypeChecker_Env.subtype_nosmt_force =
                (uu___.FStarC_TypeChecker_Env.subtype_nosmt_force);
              FStarC_TypeChecker_Env.qtbl_name_and_index =
                (uu___.FStarC_TypeChecker_Env.qtbl_name_and_index);
              FStarC_TypeChecker_Env.normalized_eff_names =
                (uu___.FStarC_TypeChecker_Env.normalized_eff_names);
              FStarC_TypeChecker_Env.fv_delta_depths =
                (uu___.FStarC_TypeChecker_Env.fv_delta_depths);
              FStarC_TypeChecker_Env.proof_ns =
                (uu___.FStarC_TypeChecker_Env.proof_ns);
              FStarC_TypeChecker_Env.synth_hook =
                (uu___.FStarC_TypeChecker_Env.synth_hook);
              FStarC_TypeChecker_Env.try_solve_implicits_hook =
                (uu___.FStarC_TypeChecker_Env.try_solve_implicits_hook);
              FStarC_TypeChecker_Env.splice =
                (uu___.FStarC_TypeChecker_Env.splice);
              FStarC_TypeChecker_Env.mpreprocess =
                (uu___.FStarC_TypeChecker_Env.mpreprocess);
              FStarC_TypeChecker_Env.postprocess =
                (uu___.FStarC_TypeChecker_Env.postprocess);
              FStarC_TypeChecker_Env.identifier_info =
                (uu___.FStarC_TypeChecker_Env.identifier_info);
              FStarC_TypeChecker_Env.tc_hooks =
                (uu___.FStarC_TypeChecker_Env.tc_hooks);
              FStarC_TypeChecker_Env.dsenv =
                (uu___.FStarC_TypeChecker_Env.dsenv);
              FStarC_TypeChecker_Env.nbe = (uu___.FStarC_TypeChecker_Env.nbe);
              FStarC_TypeChecker_Env.strict_args_tab =
                (uu___.FStarC_TypeChecker_Env.strict_args_tab);
              FStarC_TypeChecker_Env.erasable_types_tab =
                (uu___.FStarC_TypeChecker_Env.erasable_types_tab);
              FStarC_TypeChecker_Env.enable_defer_to_tac =
                (uu___.FStarC_TypeChecker_Env.enable_defer_to_tac);
              FStarC_TypeChecker_Env.unif_allow_ref_guards =
                (uu___.FStarC_TypeChecker_Env.unif_allow_ref_guards);
              FStarC_TypeChecker_Env.erase_erasable_args =
                (uu___.FStarC_TypeChecker_Env.erase_erasable_args);
              FStarC_TypeChecker_Env.core_check =
                (uu___.FStarC_TypeChecker_Env.core_check);
              FStarC_TypeChecker_Env.missing_decl =
                (uu___.FStarC_TypeChecker_Env.missing_decl)
            } in
          let env1 = FStarC_TypeChecker_Env.push_binders env bs in
          let uu___ = FStarC_TypeChecker_Env.all_binders env1 in
          let uu___1 = FStarC_Syntax_Util.ctx_uvar_should_check u in
          new_uvar
            (Prims.strcat "copy:" u.FStarC_Syntax_Syntax.ctx_uvar_reason) wl
            u.FStarC_Syntax_Syntax.ctx_uvar_range
            env1.FStarC_TypeChecker_Env.gamma uu___ t uu___1
            u.FStarC_Syntax_Syntax.ctx_uvar_meta
type solution =
  | Success of (FStarC_TypeChecker_Common.deferred *
  FStarC_TypeChecker_Common.deferred * FStarC_TypeChecker_Common.implicits_t)
  
  | Failed of (FStarC_TypeChecker_Common.prob * lstring) 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee -> match projectee with | Success _0 -> true | uu___ -> false
let (__proj__Success__item___0 :
  solution ->
    (FStarC_TypeChecker_Common.deferred * FStarC_TypeChecker_Common.deferred
      * FStarC_TypeChecker_Common.implicits_t))
  = fun projectee -> match projectee with | Success _0 -> _0
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee -> match projectee with | Failed _0 -> true | uu___ -> false
let (__proj__Failed__item___0 :
  solution -> (FStarC_TypeChecker_Common.prob * lstring)) =
  fun projectee -> match projectee with | Failed _0 -> _0
let (extend_wl :
  worklist ->
    FStarC_TypeChecker_Common.deferred ->
      FStarC_TypeChecker_Common.deferred ->
        FStarC_TypeChecker_Common.implicits_t -> worklist)
  =
  fun wl ->
    fun defers ->
      fun defer_to_tac ->
        fun imps ->
          let uu___ =
            let uu___1 = as_wl_deferred wl defers in
            FStarC_Class_Monoid.op_Plus_Plus
              (FStarC_Compiler_CList.monoid_clist ()) wl.wl_deferred uu___1 in
          let uu___1 =
            let uu___2 = as_wl_deferred wl defer_to_tac in
            FStarC_Class_Monoid.op_Plus_Plus
              (FStarC_Compiler_CList.monoid_clist ()) wl.wl_deferred_to_tac
              uu___2 in
          let uu___2 =
            FStarC_Class_Monoid.op_Plus_Plus
              (FStarC_Compiler_CList.monoid_clist ()) wl.wl_implicits imps in
          {
            attempting = (wl.attempting);
            wl_deferred = uu___;
            wl_deferred_to_tac = uu___1;
            ctr = (wl.ctr);
            defer_ok = (wl.defer_ok);
            smt_ok = (wl.smt_ok);
            umax_heuristic_ok = (wl.umax_heuristic_ok);
            tcenv = (wl.tcenv);
            wl_implicits = uu___2;
            repr_subcomp_allowed = (wl.repr_subcomp_allowed);
            typeclass_variables = (wl.typeclass_variables)
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
type tprob = FStarC_Syntax_Syntax.typ FStarC_TypeChecker_Common.problem
type cprob = FStarC_Syntax_Syntax.comp FStarC_TypeChecker_Common.problem
type 'a problem_t = 'a FStarC_TypeChecker_Common.problem
let (invert_rel :
  FStarC_TypeChecker_Common.rel -> FStarC_TypeChecker_Common.rel) =
  fun uu___ ->
    match uu___ with
    | FStarC_TypeChecker_Common.EQ -> FStarC_TypeChecker_Common.EQ
    | FStarC_TypeChecker_Common.SUB -> FStarC_TypeChecker_Common.SUBINV
    | FStarC_TypeChecker_Common.SUBINV -> FStarC_TypeChecker_Common.SUB
let invert :
  'uuuuu .
    'uuuuu FStarC_TypeChecker_Common.problem ->
      'uuuuu FStarC_TypeChecker_Common.problem
  =
  fun p ->
    {
      FStarC_TypeChecker_Common.pid = (p.FStarC_TypeChecker_Common.pid);
      FStarC_TypeChecker_Common.lhs = (p.FStarC_TypeChecker_Common.rhs);
      FStarC_TypeChecker_Common.relation =
        (invert_rel p.FStarC_TypeChecker_Common.relation);
      FStarC_TypeChecker_Common.rhs = (p.FStarC_TypeChecker_Common.lhs);
      FStarC_TypeChecker_Common.element =
        (p.FStarC_TypeChecker_Common.element);
      FStarC_TypeChecker_Common.logical_guard =
        (p.FStarC_TypeChecker_Common.logical_guard);
      FStarC_TypeChecker_Common.logical_guard_uvar =
        (p.FStarC_TypeChecker_Common.logical_guard_uvar);
      FStarC_TypeChecker_Common.reason = (p.FStarC_TypeChecker_Common.reason);
      FStarC_TypeChecker_Common.loc = (p.FStarC_TypeChecker_Common.loc);
      FStarC_TypeChecker_Common.rank = (p.FStarC_TypeChecker_Common.rank);
      FStarC_TypeChecker_Common.logical =
        (p.FStarC_TypeChecker_Common.logical)
    }
let maybe_invert :
  'uuuuu .
    'uuuuu FStarC_TypeChecker_Common.problem ->
      'uuuuu FStarC_TypeChecker_Common.problem
  =
  fun p ->
    if
      p.FStarC_TypeChecker_Common.relation = FStarC_TypeChecker_Common.SUBINV
    then invert p
    else p
let (maybe_invert_p :
  FStarC_TypeChecker_Common.prob -> FStarC_TypeChecker_Common.prob) =
  fun uu___ ->
    match uu___ with
    | FStarC_TypeChecker_Common.TProb p ->
        FStarC_TypeChecker_Common.TProb (maybe_invert p)
    | FStarC_TypeChecker_Common.CProb p ->
        FStarC_TypeChecker_Common.CProb (maybe_invert p)
let (make_prob_eq :
  FStarC_TypeChecker_Common.prob -> FStarC_TypeChecker_Common.prob) =
  fun uu___ ->
    match uu___ with
    | FStarC_TypeChecker_Common.TProb p ->
        FStarC_TypeChecker_Common.TProb
          {
            FStarC_TypeChecker_Common.pid = (p.FStarC_TypeChecker_Common.pid);
            FStarC_TypeChecker_Common.lhs = (p.FStarC_TypeChecker_Common.lhs);
            FStarC_TypeChecker_Common.relation = FStarC_TypeChecker_Common.EQ;
            FStarC_TypeChecker_Common.rhs = (p.FStarC_TypeChecker_Common.rhs);
            FStarC_TypeChecker_Common.element =
              (p.FStarC_TypeChecker_Common.element);
            FStarC_TypeChecker_Common.logical_guard =
              (p.FStarC_TypeChecker_Common.logical_guard);
            FStarC_TypeChecker_Common.logical_guard_uvar =
              (p.FStarC_TypeChecker_Common.logical_guard_uvar);
            FStarC_TypeChecker_Common.reason =
              (p.FStarC_TypeChecker_Common.reason);
            FStarC_TypeChecker_Common.loc = (p.FStarC_TypeChecker_Common.loc);
            FStarC_TypeChecker_Common.rank =
              (p.FStarC_TypeChecker_Common.rank);
            FStarC_TypeChecker_Common.logical =
              (p.FStarC_TypeChecker_Common.logical)
          }
    | FStarC_TypeChecker_Common.CProb p ->
        FStarC_TypeChecker_Common.CProb
          {
            FStarC_TypeChecker_Common.pid = (p.FStarC_TypeChecker_Common.pid);
            FStarC_TypeChecker_Common.lhs = (p.FStarC_TypeChecker_Common.lhs);
            FStarC_TypeChecker_Common.relation = FStarC_TypeChecker_Common.EQ;
            FStarC_TypeChecker_Common.rhs = (p.FStarC_TypeChecker_Common.rhs);
            FStarC_TypeChecker_Common.element =
              (p.FStarC_TypeChecker_Common.element);
            FStarC_TypeChecker_Common.logical_guard =
              (p.FStarC_TypeChecker_Common.logical_guard);
            FStarC_TypeChecker_Common.logical_guard_uvar =
              (p.FStarC_TypeChecker_Common.logical_guard_uvar);
            FStarC_TypeChecker_Common.reason =
              (p.FStarC_TypeChecker_Common.reason);
            FStarC_TypeChecker_Common.loc = (p.FStarC_TypeChecker_Common.loc);
            FStarC_TypeChecker_Common.rank =
              (p.FStarC_TypeChecker_Common.rank);
            FStarC_TypeChecker_Common.logical =
              (p.FStarC_TypeChecker_Common.logical)
          }
let (vary_rel :
  FStarC_TypeChecker_Common.rel -> variance -> FStarC_TypeChecker_Common.rel)
  =
  fun rel ->
    fun uu___ ->
      match uu___ with
      | INVARIANT -> FStarC_TypeChecker_Common.EQ
      | CONTRAVARIANT -> invert_rel rel
      | COVARIANT -> rel
let (p_pid : FStarC_TypeChecker_Common.prob -> Prims.int) =
  fun uu___ ->
    match uu___ with
    | FStarC_TypeChecker_Common.TProb p -> p.FStarC_TypeChecker_Common.pid
    | FStarC_TypeChecker_Common.CProb p -> p.FStarC_TypeChecker_Common.pid
let (p_rel : FStarC_TypeChecker_Common.prob -> FStarC_TypeChecker_Common.rel)
  =
  fun uu___ ->
    match uu___ with
    | FStarC_TypeChecker_Common.TProb p ->
        p.FStarC_TypeChecker_Common.relation
    | FStarC_TypeChecker_Common.CProb p ->
        p.FStarC_TypeChecker_Common.relation
let (p_reason : FStarC_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___ ->
    match uu___ with
    | FStarC_TypeChecker_Common.TProb p -> p.FStarC_TypeChecker_Common.reason
    | FStarC_TypeChecker_Common.CProb p -> p.FStarC_TypeChecker_Common.reason
let (p_loc :
  FStarC_TypeChecker_Common.prob -> FStarC_Compiler_Range_Type.range) =
  fun uu___ ->
    match uu___ with
    | FStarC_TypeChecker_Common.TProb p -> p.FStarC_TypeChecker_Common.loc
    | FStarC_TypeChecker_Common.CProb p -> p.FStarC_TypeChecker_Common.loc
let (p_element :
  FStarC_TypeChecker_Common.prob ->
    FStarC_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___ ->
    match uu___ with
    | FStarC_TypeChecker_Common.TProb p ->
        p.FStarC_TypeChecker_Common.element
    | FStarC_TypeChecker_Common.CProb p ->
        p.FStarC_TypeChecker_Common.element
let (p_guard : FStarC_TypeChecker_Common.prob -> FStarC_Syntax_Syntax.term) =
  fun uu___ ->
    match uu___ with
    | FStarC_TypeChecker_Common.TProb p ->
        p.FStarC_TypeChecker_Common.logical_guard
    | FStarC_TypeChecker_Common.CProb p ->
        p.FStarC_TypeChecker_Common.logical_guard
let (p_scope :
  FStarC_TypeChecker_Common.prob -> FStarC_Syntax_Syntax.binder Prims.list) =
  fun prob ->
    let r =
      match prob with
      | FStarC_TypeChecker_Common.TProb p ->
          let uu___ =
            match p_element prob with
            | FStar_Pervasives_Native.None -> []
            | FStar_Pervasives_Native.Some x ->
                let uu___1 = FStarC_Syntax_Syntax.mk_binder x in [uu___1] in
          FStarC_Compiler_List.op_At
            (p.FStarC_TypeChecker_Common.logical_guard_uvar).FStarC_Syntax_Syntax.ctx_uvar_binders
            uu___
      | FStarC_TypeChecker_Common.CProb p ->
          let uu___ =
            match p_element prob with
            | FStar_Pervasives_Native.None -> []
            | FStar_Pervasives_Native.Some x ->
                let uu___1 = FStarC_Syntax_Syntax.mk_binder x in [uu___1] in
          FStarC_Compiler_List.op_At
            (p.FStarC_TypeChecker_Common.logical_guard_uvar).FStarC_Syntax_Syntax.ctx_uvar_binders
            uu___ in
    r
let (p_guard_uvar :
  FStarC_TypeChecker_Common.prob -> FStarC_Syntax_Syntax.ctx_uvar) =
  fun uu___ ->
    match uu___ with
    | FStarC_TypeChecker_Common.TProb p ->
        p.FStarC_TypeChecker_Common.logical_guard_uvar
    | FStarC_TypeChecker_Common.CProb p ->
        p.FStarC_TypeChecker_Common.logical_guard_uvar
let (p_env :
  worklist -> FStarC_TypeChecker_Common.prob -> FStarC_TypeChecker_Env.env) =
  fun wl ->
    fun prob ->
      let uu___ = wl.tcenv in
      {
        FStarC_TypeChecker_Env.solver = (uu___.FStarC_TypeChecker_Env.solver);
        FStarC_TypeChecker_Env.range = (uu___.FStarC_TypeChecker_Env.range);
        FStarC_TypeChecker_Env.curmodule =
          (uu___.FStarC_TypeChecker_Env.curmodule);
        FStarC_TypeChecker_Env.gamma =
          ((p_guard_uvar prob).FStarC_Syntax_Syntax.ctx_uvar_gamma);
        FStarC_TypeChecker_Env.gamma_sig =
          (uu___.FStarC_TypeChecker_Env.gamma_sig);
        FStarC_TypeChecker_Env.gamma_cache =
          (uu___.FStarC_TypeChecker_Env.gamma_cache);
        FStarC_TypeChecker_Env.modules =
          (uu___.FStarC_TypeChecker_Env.modules);
        FStarC_TypeChecker_Env.expected_typ =
          (uu___.FStarC_TypeChecker_Env.expected_typ);
        FStarC_TypeChecker_Env.sigtab = (uu___.FStarC_TypeChecker_Env.sigtab);
        FStarC_TypeChecker_Env.attrtab =
          (uu___.FStarC_TypeChecker_Env.attrtab);
        FStarC_TypeChecker_Env.instantiate_imp =
          (uu___.FStarC_TypeChecker_Env.instantiate_imp);
        FStarC_TypeChecker_Env.effects =
          (uu___.FStarC_TypeChecker_Env.effects);
        FStarC_TypeChecker_Env.generalize =
          (uu___.FStarC_TypeChecker_Env.generalize);
        FStarC_TypeChecker_Env.letrecs =
          (uu___.FStarC_TypeChecker_Env.letrecs);
        FStarC_TypeChecker_Env.top_level =
          (uu___.FStarC_TypeChecker_Env.top_level);
        FStarC_TypeChecker_Env.check_uvars =
          (uu___.FStarC_TypeChecker_Env.check_uvars);
        FStarC_TypeChecker_Env.use_eq_strict =
          (uu___.FStarC_TypeChecker_Env.use_eq_strict);
        FStarC_TypeChecker_Env.is_iface =
          (uu___.FStarC_TypeChecker_Env.is_iface);
        FStarC_TypeChecker_Env.admit = (uu___.FStarC_TypeChecker_Env.admit);
        FStarC_TypeChecker_Env.lax_universes =
          (uu___.FStarC_TypeChecker_Env.lax_universes);
        FStarC_TypeChecker_Env.phase1 = (uu___.FStarC_TypeChecker_Env.phase1);
        FStarC_TypeChecker_Env.failhard =
          (uu___.FStarC_TypeChecker_Env.failhard);
        FStarC_TypeChecker_Env.flychecking =
          (uu___.FStarC_TypeChecker_Env.flychecking);
        FStarC_TypeChecker_Env.uvar_subtyping =
          (uu___.FStarC_TypeChecker_Env.uvar_subtyping);
        FStarC_TypeChecker_Env.intactics =
          (uu___.FStarC_TypeChecker_Env.intactics);
        FStarC_TypeChecker_Env.nocoerce =
          (uu___.FStarC_TypeChecker_Env.nocoerce);
        FStarC_TypeChecker_Env.tc_term =
          (uu___.FStarC_TypeChecker_Env.tc_term);
        FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
          (uu___.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
        FStarC_TypeChecker_Env.universe_of =
          (uu___.FStarC_TypeChecker_Env.universe_of);
        FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
          (uu___.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
        FStarC_TypeChecker_Env.teq_nosmt_force =
          (uu___.FStarC_TypeChecker_Env.teq_nosmt_force);
        FStarC_TypeChecker_Env.subtype_nosmt_force =
          (uu___.FStarC_TypeChecker_Env.subtype_nosmt_force);
        FStarC_TypeChecker_Env.qtbl_name_and_index =
          (uu___.FStarC_TypeChecker_Env.qtbl_name_and_index);
        FStarC_TypeChecker_Env.normalized_eff_names =
          (uu___.FStarC_TypeChecker_Env.normalized_eff_names);
        FStarC_TypeChecker_Env.fv_delta_depths =
          (uu___.FStarC_TypeChecker_Env.fv_delta_depths);
        FStarC_TypeChecker_Env.proof_ns =
          (uu___.FStarC_TypeChecker_Env.proof_ns);
        FStarC_TypeChecker_Env.synth_hook =
          (uu___.FStarC_TypeChecker_Env.synth_hook);
        FStarC_TypeChecker_Env.try_solve_implicits_hook =
          (uu___.FStarC_TypeChecker_Env.try_solve_implicits_hook);
        FStarC_TypeChecker_Env.splice = (uu___.FStarC_TypeChecker_Env.splice);
        FStarC_TypeChecker_Env.mpreprocess =
          (uu___.FStarC_TypeChecker_Env.mpreprocess);
        FStarC_TypeChecker_Env.postprocess =
          (uu___.FStarC_TypeChecker_Env.postprocess);
        FStarC_TypeChecker_Env.identifier_info =
          (uu___.FStarC_TypeChecker_Env.identifier_info);
        FStarC_TypeChecker_Env.tc_hooks =
          (uu___.FStarC_TypeChecker_Env.tc_hooks);
        FStarC_TypeChecker_Env.dsenv = (uu___.FStarC_TypeChecker_Env.dsenv);
        FStarC_TypeChecker_Env.nbe = (uu___.FStarC_TypeChecker_Env.nbe);
        FStarC_TypeChecker_Env.strict_args_tab =
          (uu___.FStarC_TypeChecker_Env.strict_args_tab);
        FStarC_TypeChecker_Env.erasable_types_tab =
          (uu___.FStarC_TypeChecker_Env.erasable_types_tab);
        FStarC_TypeChecker_Env.enable_defer_to_tac =
          (uu___.FStarC_TypeChecker_Env.enable_defer_to_tac);
        FStarC_TypeChecker_Env.unif_allow_ref_guards =
          (uu___.FStarC_TypeChecker_Env.unif_allow_ref_guards);
        FStarC_TypeChecker_Env.erase_erasable_args =
          (uu___.FStarC_TypeChecker_Env.erase_erasable_args);
        FStarC_TypeChecker_Env.core_check =
          (uu___.FStarC_TypeChecker_Env.core_check);
        FStarC_TypeChecker_Env.missing_decl =
          (uu___.FStarC_TypeChecker_Env.missing_decl)
      }
let (p_guard_env :
  worklist -> FStarC_TypeChecker_Common.prob -> FStarC_TypeChecker_Env.env) =
  fun wl ->
    fun prob ->
      let uu___ = wl.tcenv in
      {
        FStarC_TypeChecker_Env.solver = (uu___.FStarC_TypeChecker_Env.solver);
        FStarC_TypeChecker_Env.range = (uu___.FStarC_TypeChecker_Env.range);
        FStarC_TypeChecker_Env.curmodule =
          (uu___.FStarC_TypeChecker_Env.curmodule);
        FStarC_TypeChecker_Env.gamma =
          (FStarC_Compiler_List.op_At
             (match p_element prob with
              | FStar_Pervasives_Native.None -> []
              | FStar_Pervasives_Native.Some x ->
                  [FStarC_Syntax_Syntax.Binding_var x])
             (p_guard_uvar prob).FStarC_Syntax_Syntax.ctx_uvar_gamma);
        FStarC_TypeChecker_Env.gamma_sig =
          (uu___.FStarC_TypeChecker_Env.gamma_sig);
        FStarC_TypeChecker_Env.gamma_cache =
          (uu___.FStarC_TypeChecker_Env.gamma_cache);
        FStarC_TypeChecker_Env.modules =
          (uu___.FStarC_TypeChecker_Env.modules);
        FStarC_TypeChecker_Env.expected_typ =
          (uu___.FStarC_TypeChecker_Env.expected_typ);
        FStarC_TypeChecker_Env.sigtab = (uu___.FStarC_TypeChecker_Env.sigtab);
        FStarC_TypeChecker_Env.attrtab =
          (uu___.FStarC_TypeChecker_Env.attrtab);
        FStarC_TypeChecker_Env.instantiate_imp =
          (uu___.FStarC_TypeChecker_Env.instantiate_imp);
        FStarC_TypeChecker_Env.effects =
          (uu___.FStarC_TypeChecker_Env.effects);
        FStarC_TypeChecker_Env.generalize =
          (uu___.FStarC_TypeChecker_Env.generalize);
        FStarC_TypeChecker_Env.letrecs =
          (uu___.FStarC_TypeChecker_Env.letrecs);
        FStarC_TypeChecker_Env.top_level =
          (uu___.FStarC_TypeChecker_Env.top_level);
        FStarC_TypeChecker_Env.check_uvars =
          (uu___.FStarC_TypeChecker_Env.check_uvars);
        FStarC_TypeChecker_Env.use_eq_strict =
          (uu___.FStarC_TypeChecker_Env.use_eq_strict);
        FStarC_TypeChecker_Env.is_iface =
          (uu___.FStarC_TypeChecker_Env.is_iface);
        FStarC_TypeChecker_Env.admit = (uu___.FStarC_TypeChecker_Env.admit);
        FStarC_TypeChecker_Env.lax_universes =
          (uu___.FStarC_TypeChecker_Env.lax_universes);
        FStarC_TypeChecker_Env.phase1 = (uu___.FStarC_TypeChecker_Env.phase1);
        FStarC_TypeChecker_Env.failhard =
          (uu___.FStarC_TypeChecker_Env.failhard);
        FStarC_TypeChecker_Env.flychecking =
          (uu___.FStarC_TypeChecker_Env.flychecking);
        FStarC_TypeChecker_Env.uvar_subtyping =
          (uu___.FStarC_TypeChecker_Env.uvar_subtyping);
        FStarC_TypeChecker_Env.intactics =
          (uu___.FStarC_TypeChecker_Env.intactics);
        FStarC_TypeChecker_Env.nocoerce =
          (uu___.FStarC_TypeChecker_Env.nocoerce);
        FStarC_TypeChecker_Env.tc_term =
          (uu___.FStarC_TypeChecker_Env.tc_term);
        FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
          (uu___.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
        FStarC_TypeChecker_Env.universe_of =
          (uu___.FStarC_TypeChecker_Env.universe_of);
        FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
          (uu___.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
        FStarC_TypeChecker_Env.teq_nosmt_force =
          (uu___.FStarC_TypeChecker_Env.teq_nosmt_force);
        FStarC_TypeChecker_Env.subtype_nosmt_force =
          (uu___.FStarC_TypeChecker_Env.subtype_nosmt_force);
        FStarC_TypeChecker_Env.qtbl_name_and_index =
          (uu___.FStarC_TypeChecker_Env.qtbl_name_and_index);
        FStarC_TypeChecker_Env.normalized_eff_names =
          (uu___.FStarC_TypeChecker_Env.normalized_eff_names);
        FStarC_TypeChecker_Env.fv_delta_depths =
          (uu___.FStarC_TypeChecker_Env.fv_delta_depths);
        FStarC_TypeChecker_Env.proof_ns =
          (uu___.FStarC_TypeChecker_Env.proof_ns);
        FStarC_TypeChecker_Env.synth_hook =
          (uu___.FStarC_TypeChecker_Env.synth_hook);
        FStarC_TypeChecker_Env.try_solve_implicits_hook =
          (uu___.FStarC_TypeChecker_Env.try_solve_implicits_hook);
        FStarC_TypeChecker_Env.splice = (uu___.FStarC_TypeChecker_Env.splice);
        FStarC_TypeChecker_Env.mpreprocess =
          (uu___.FStarC_TypeChecker_Env.mpreprocess);
        FStarC_TypeChecker_Env.postprocess =
          (uu___.FStarC_TypeChecker_Env.postprocess);
        FStarC_TypeChecker_Env.identifier_info =
          (uu___.FStarC_TypeChecker_Env.identifier_info);
        FStarC_TypeChecker_Env.tc_hooks =
          (uu___.FStarC_TypeChecker_Env.tc_hooks);
        FStarC_TypeChecker_Env.dsenv = (uu___.FStarC_TypeChecker_Env.dsenv);
        FStarC_TypeChecker_Env.nbe = (uu___.FStarC_TypeChecker_Env.nbe);
        FStarC_TypeChecker_Env.strict_args_tab =
          (uu___.FStarC_TypeChecker_Env.strict_args_tab);
        FStarC_TypeChecker_Env.erasable_types_tab =
          (uu___.FStarC_TypeChecker_Env.erasable_types_tab);
        FStarC_TypeChecker_Env.enable_defer_to_tac =
          (uu___.FStarC_TypeChecker_Env.enable_defer_to_tac);
        FStarC_TypeChecker_Env.unif_allow_ref_guards =
          (uu___.FStarC_TypeChecker_Env.unif_allow_ref_guards);
        FStarC_TypeChecker_Env.erase_erasable_args =
          (uu___.FStarC_TypeChecker_Env.erase_erasable_args);
        FStarC_TypeChecker_Env.core_check =
          (uu___.FStarC_TypeChecker_Env.core_check);
        FStarC_TypeChecker_Env.missing_decl =
          (uu___.FStarC_TypeChecker_Env.missing_decl)
      }
let (def_scope_wf :
  Prims.string ->
    FStarC_Compiler_Range_Type.range ->
      FStarC_Syntax_Syntax.binder Prims.list -> unit)
  =
  fun msg ->
    fun rng ->
      fun r ->
        let uu___ =
          let uu___1 = FStarC_Options.defensive () in
          Prims.op_Negation uu___1 in
        if uu___
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | { FStarC_Syntax_Syntax.binder_bv = bv;
                 FStarC_Syntax_Syntax.binder_qual = uu___2;
                 FStarC_Syntax_Syntax.binder_positivity = uu___3;
                 FStarC_Syntax_Syntax.binder_attrs = uu___4;_}::bs ->
                 (FStarC_Defensive.def_check_scoped
                    FStarC_Class_Binders.hasBinders_list_bv
                    FStarC_Class_Binders.hasNames_term
                    FStarC_Syntax_Print.pretty_term rng msg prev
                    bv.FStarC_Syntax_Syntax.sort;
                  aux (FStarC_Compiler_List.op_At prev [bv]) bs) in
           aux [] r)
let (hasBinders_prob :
  FStarC_TypeChecker_Common.prob FStarC_Class_Binders.hasBinders) =
  {
    FStarC_Class_Binders.boundNames =
      (fun uu___ ->
         (fun prob ->
            let uu___ =
              let uu___1 = p_scope prob in
              FStarC_Compiler_List.map
                (fun b -> b.FStarC_Syntax_Syntax.binder_bv) uu___1 in
            Obj.magic
              (FStarC_Class_Setlike.from_list ()
                 (Obj.magic
                    (FStarC_Compiler_FlatSet.setlike_flat_set
                       FStarC_Syntax_Syntax.ord_bv)) uu___)) uu___)
  }
let (def_check_term_scoped_in_prob :
  Prims.string ->
    FStarC_TypeChecker_Common.prob -> FStarC_Syntax_Syntax.term -> unit)
  =
  fun msg ->
    fun prob ->
      fun phi ->
        FStarC_Defensive.def_check_scoped hasBinders_prob
          FStarC_Class_Binders.hasNames_term FStarC_Syntax_Print.pretty_term
          (p_loc prob) msg prob phi
let (def_check_comp_scoped_in_prob :
  Prims.string ->
    FStarC_TypeChecker_Common.prob -> FStarC_Syntax_Syntax.comp -> unit)
  =
  fun msg ->
    fun prob ->
      fun phi ->
        FStarC_Defensive.def_check_scoped hasBinders_prob
          FStarC_Class_Binders.hasNames_comp FStarC_Syntax_Print.pretty_comp
          (p_loc prob) msg prob phi
let (def_check_prob : Prims.string -> FStarC_TypeChecker_Common.prob -> unit)
  =
  fun msg ->
    fun prob ->
      let uu___ =
        let uu___1 = FStarC_Options.defensive () in Prims.op_Negation uu___1 in
      if uu___
      then ()
      else
        (let msgf m =
           let uu___2 =
             let uu___3 =
               let uu___4 = FStarC_Compiler_Util.string_of_int (p_pid prob) in
               Prims.strcat uu___4 (Prims.strcat "." m) in
             Prims.strcat "." uu___3 in
           Prims.strcat msg uu___2 in
         (let uu___3 = msgf "scope" in
          let uu___4 = p_scope prob in
          def_scope_wf uu___3 (p_loc prob) uu___4);
         (let uu___4 = msgf "guard" in
          def_check_term_scoped_in_prob uu___4 prob (p_guard prob));
         (match prob with
          | FStarC_TypeChecker_Common.TProb p ->
              ((let uu___5 = msgf "lhs" in
                def_check_term_scoped_in_prob uu___5 prob
                  p.FStarC_TypeChecker_Common.lhs);
               (let uu___5 = msgf "rhs" in
                def_check_term_scoped_in_prob uu___5 prob
                  p.FStarC_TypeChecker_Common.rhs))
          | FStarC_TypeChecker_Common.CProb p ->
              ((let uu___5 = msgf "lhs" in
                def_check_comp_scoped_in_prob uu___5 prob
                  p.FStarC_TypeChecker_Common.lhs);
               (let uu___5 = msgf "rhs" in
                def_check_comp_scoped_in_prob uu___5 prob
                  p.FStarC_TypeChecker_Common.rhs))))
let (rel_to_string : FStarC_TypeChecker_Common.rel -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | FStarC_TypeChecker_Common.EQ -> "="
    | FStarC_TypeChecker_Common.SUB -> "<:"
    | FStarC_TypeChecker_Common.SUBINV -> ":>"
let (term_to_string : FStarC_Syntax_Syntax.term -> Prims.string) =
  fun t ->
    let uu___ = FStarC_Syntax_Util.head_and_args t in
    match uu___ with
    | (head, args) ->
        (match head.FStarC_Syntax_Syntax.n with
         | FStarC_Syntax_Syntax.Tm_uvar (u, s) ->
             let uu___1 =
               FStarC_Class_Show.show FStarC_Syntax_Print.showable_ctxu u in
             let uu___2 =
               let uu___3 =
                 FStarC_Class_Show.show
                   (FStarC_Class_Show.show_list
                      (FStarC_Class_Show.show_list
                         FStarC_Syntax_Print.showable_subst_elt))
                   (FStar_Pervasives_Native.fst s) in
               Prims.strcat "@" uu___3 in
             let uu___3 =
               FStarC_Class_Show.show
                 (FStarC_Class_Show.show_list
                    (FStarC_Class_Show.show_tuple2
                       FStarC_Syntax_Print.showable_term
                       FStarC_Syntax_Print.showable_aqual)) args in
             FStarC_Compiler_Util.format3 "%s%s %s" uu___1 uu___2 uu___3
         | uu___1 ->
             FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t)
let (prob_to_string :
  FStarC_TypeChecker_Env.env ->
    FStarC_TypeChecker_Common.prob -> Prims.string)
  =
  fun env ->
    fun prob ->
      match prob with
      | FStarC_TypeChecker_Common.TProb p ->
          let uu___ =
            let uu___1 =
              FStarC_Compiler_Util.string_of_int
                p.FStarC_TypeChecker_Common.pid in
            let uu___2 =
              let uu___3 = term_to_string p.FStarC_TypeChecker_Common.lhs in
              let uu___4 =
                let uu___5 =
                  let uu___6 = term_to_string p.FStarC_TypeChecker_Common.rhs in
                  let uu___7 =
                    let uu___8 =
                      let uu___9 =
                        FStarC_Class_Show.show
                          FStarC_Class_Show.showable_bool
                          p.FStarC_TypeChecker_Common.logical in
                      [uu___9] in
                    (match p.FStarC_TypeChecker_Common.reason with
                     | [] -> ""
                     | r::uu___9 -> r) :: uu___8 in
                  uu___6 :: uu___7 in
                (rel_to_string p.FStarC_TypeChecker_Common.relation) ::
                  uu___5 in
              uu___3 :: uu___4 in
            uu___1 :: uu___2 in
          FStarC_Compiler_Util.format
            "\n%s:\t%s \n\t\t%s\n\t%s\n\t(reason:%s) (logical:%s)\n" uu___
      | FStarC_TypeChecker_Common.CProb p ->
          let uu___ =
            FStarC_Compiler_Util.string_of_int
              p.FStarC_TypeChecker_Common.pid in
          let uu___1 =
            FStarC_TypeChecker_Normalize.comp_to_string env
              p.FStarC_TypeChecker_Common.lhs in
          let uu___2 =
            FStarC_TypeChecker_Normalize.comp_to_string env
              p.FStarC_TypeChecker_Common.rhs in
          FStarC_Compiler_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu___
            uu___1 (rel_to_string p.FStarC_TypeChecker_Common.relation)
            uu___2
let (prob_to_string' :
  worklist -> FStarC_TypeChecker_Common.prob -> Prims.string) =
  fun wl -> fun prob -> let env = p_env wl prob in prob_to_string env prob
let (uvi_to_string : FStarC_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env ->
    fun uu___ ->
      match uu___ with
      | UNIV (u, t) ->
          let x =
            let uu___1 = FStarC_Options.hide_uvar_nums () in
            if uu___1
            then "?"
            else
              (let uu___3 = FStarC_Syntax_Unionfind.univ_uvar_id u in
               FStarC_Compiler_Util.string_of_int uu___3) in
          let uu___1 =
            FStarC_Class_Show.show FStarC_Syntax_Print.showable_univ t in
          FStarC_Compiler_Util.format2 "UNIV %s <- %s" x uu___1
      | TERM (u, t) ->
          let x =
            let uu___1 = FStarC_Options.hide_uvar_nums () in
            if uu___1
            then "?"
            else
              (let uu___3 =
                 FStarC_Syntax_Unionfind.uvar_id
                   u.FStarC_Syntax_Syntax.ctx_uvar_head in
               FStarC_Compiler_Util.string_of_int uu___3) in
          let uu___1 = FStarC_TypeChecker_Normalize.term_to_string env t in
          FStarC_Compiler_Util.format2 "TERM %s <- %s" x uu___1
let (uvis_to_string :
  FStarC_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env ->
    fun uvis -> (FStarC_Common.string_of_list ()) (uvi_to_string env) uvis
let (empty_worklist : FStarC_TypeChecker_Env.env -> worklist) =
  fun env ->
    let uu___ =
      Obj.magic
        (FStarC_Class_Setlike.empty ()
           (Obj.magic
              (FStarC_Compiler_RBSet.setlike_rbset
                 FStarC_Syntax_Free.ord_ctx_uvar)) ()) in
    {
      attempting = [];
      wl_deferred =
        (Obj.magic
           (FStarC_Class_Listlike.empty ()
              (Obj.magic (FStarC_Compiler_CList.listlike_clist ()))));
      wl_deferred_to_tac =
        (Obj.magic
           (FStarC_Class_Listlike.empty ()
              (Obj.magic (FStarC_Compiler_CList.listlike_clist ()))));
      ctr = Prims.int_zero;
      defer_ok = DeferAny;
      smt_ok = true;
      umax_heuristic_ok = true;
      tcenv = env;
      wl_implicits =
        (Obj.magic
           (FStarC_Class_Listlike.empty ()
              (Obj.magic (FStarC_Compiler_CList.listlike_clist ()))));
      repr_subcomp_allowed = false;
      typeclass_variables = uu___
    }
let (giveup :
  worklist -> lstring -> FStarC_TypeChecker_Common.prob -> solution) =
  fun wl ->
    fun reason ->
      fun prob ->
        (let uu___1 = FStarC_Compiler_Effect.op_Bang dbg_Rel in
         if uu___1
         then
           let uu___2 = FStarC_Thunk.force reason in
           let uu___3 = prob_to_string' wl prob in
           FStarC_Compiler_Util.print2 "Failed %s:\n%s\n" uu___2 uu___3
         else ());
        Failed (prob, reason)
let (giveup_lit :
  worklist -> Prims.string -> FStarC_TypeChecker_Common.prob -> solution) =
  fun wl ->
    fun reason ->
      fun prob ->
        let uu___ = mklstr (fun uu___1 -> reason) in giveup wl uu___ prob
let (singleton :
  worklist -> FStarC_TypeChecker_Common.prob -> Prims.bool -> worklist) =
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
          repr_subcomp_allowed = (wl.repr_subcomp_allowed);
          typeclass_variables = (wl.typeclass_variables)
        }
let wl_of_guard :
  'uuuuu 'uuuuu1 .
    FStarC_TypeChecker_Env.env ->
      ('uuuuu * 'uuuuu1 * FStarC_TypeChecker_Common.prob) Prims.list ->
        worklist
  =
  fun env ->
    fun g ->
      let uu___ = empty_worklist env in
      let uu___1 =
        FStarC_Compiler_List.map
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
        repr_subcomp_allowed = (uu___.repr_subcomp_allowed);
        typeclass_variables = (uu___.typeclass_variables)
      }
let (defer :
  FStarC_TypeChecker_Common.deferred_reason ->
    lstring -> FStarC_TypeChecker_Common.prob -> worklist -> worklist)
  =
  fun reason ->
    fun msg ->
      fun prob ->
        fun wl ->
          let uu___ =
            Obj.magic
              (FStarC_Class_Listlike.cons ()
                 (Obj.magic (FStarC_Compiler_CList.listlike_clist ()))
                 ((wl.ctr), reason, msg, prob) (Obj.magic wl.wl_deferred)) in
          {
            attempting = (wl.attempting);
            wl_deferred = uu___;
            wl_deferred_to_tac = (wl.wl_deferred_to_tac);
            ctr = (wl.ctr);
            defer_ok = (wl.defer_ok);
            smt_ok = (wl.smt_ok);
            umax_heuristic_ok = (wl.umax_heuristic_ok);
            tcenv = (wl.tcenv);
            wl_implicits = (wl.wl_implicits);
            repr_subcomp_allowed = (wl.repr_subcomp_allowed);
            typeclass_variables = (wl.typeclass_variables)
          }
let (defer_lit :
  FStarC_TypeChecker_Common.deferred_reason ->
    Prims.string -> FStarC_TypeChecker_Common.prob -> worklist -> worklist)
  =
  fun reason ->
    fun msg ->
      fun prob ->
        fun wl ->
          let uu___ = FStarC_Thunk.mkv msg in defer reason uu___ prob wl
let (attempt :
  FStarC_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs ->
    fun wl ->
      FStarC_Compiler_List.iter (def_check_prob "attempt") probs;
      {
        attempting = (FStarC_Compiler_List.op_At probs wl.attempting);
        wl_deferred = (wl.wl_deferred);
        wl_deferred_to_tac = (wl.wl_deferred_to_tac);
        ctr = (wl.ctr);
        defer_ok = (wl.defer_ok);
        smt_ok = (wl.smt_ok);
        umax_heuristic_ok = (wl.umax_heuristic_ok);
        tcenv = (wl.tcenv);
        wl_implicits = (wl.wl_implicits);
        repr_subcomp_allowed = (wl.repr_subcomp_allowed);
        typeclass_variables = (wl.typeclass_variables)
      }
let (mk_eq2 :
  worklist ->
    FStarC_TypeChecker_Common.prob ->
      FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
        FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
          (FStarC_Syntax_Syntax.term * worklist))
  =
  fun wl ->
    fun prob ->
      fun t1 ->
        fun t2 ->
          let env = p_env wl prob in
          FStarC_Defensive.def_check_scoped
            FStarC_TypeChecker_Env.hasBinders_env
            FStarC_Class_Binders.hasNames_term
            FStarC_Syntax_Print.pretty_term t1.FStarC_Syntax_Syntax.pos
            "mk_eq2.t1" env t1;
          FStarC_Defensive.def_check_scoped
            FStarC_TypeChecker_Env.hasBinders_env
            FStarC_Class_Binders.hasNames_term
            FStarC_Syntax_Print.pretty_term t2.FStarC_Syntax_Syntax.pos
            "mk_eq2.t2" env t2;
          (let uu___2 =
             env.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
               env t1 false in
           match uu___2 with
           | (tt, uu___3) ->
               let u = env.FStarC_TypeChecker_Env.universe_of env tt in
               let uu___4 = FStarC_Syntax_Util.mk_eq2 u tt t1 t2 in
               (uu___4, wl))
let (p_invert :
  FStarC_TypeChecker_Common.prob -> FStarC_TypeChecker_Common.prob) =
  fun uu___ ->
    match uu___ with
    | FStarC_TypeChecker_Common.TProb p ->
        FStarC_TypeChecker_Common.TProb (invert p)
    | FStarC_TypeChecker_Common.CProb p ->
        FStarC_TypeChecker_Common.CProb (invert p)
let (p_logical : FStarC_TypeChecker_Common.prob -> Prims.bool) =
  fun uu___ ->
    match uu___ with
    | FStarC_TypeChecker_Common.TProb p ->
        p.FStarC_TypeChecker_Common.logical
    | FStarC_TypeChecker_Common.CProb p ->
        p.FStarC_TypeChecker_Common.logical
let (set_logical :
  Prims.bool ->
    FStarC_TypeChecker_Common.prob -> FStarC_TypeChecker_Common.prob)
  =
  fun b ->
    fun uu___ ->
      match uu___ with
      | FStarC_TypeChecker_Common.TProb p ->
          FStarC_TypeChecker_Common.TProb
            {
              FStarC_TypeChecker_Common.pid =
                (p.FStarC_TypeChecker_Common.pid);
              FStarC_TypeChecker_Common.lhs =
                (p.FStarC_TypeChecker_Common.lhs);
              FStarC_TypeChecker_Common.relation =
                (p.FStarC_TypeChecker_Common.relation);
              FStarC_TypeChecker_Common.rhs =
                (p.FStarC_TypeChecker_Common.rhs);
              FStarC_TypeChecker_Common.element =
                (p.FStarC_TypeChecker_Common.element);
              FStarC_TypeChecker_Common.logical_guard =
                (p.FStarC_TypeChecker_Common.logical_guard);
              FStarC_TypeChecker_Common.logical_guard_uvar =
                (p.FStarC_TypeChecker_Common.logical_guard_uvar);
              FStarC_TypeChecker_Common.reason =
                (p.FStarC_TypeChecker_Common.reason);
              FStarC_TypeChecker_Common.loc =
                (p.FStarC_TypeChecker_Common.loc);
              FStarC_TypeChecker_Common.rank =
                (p.FStarC_TypeChecker_Common.rank);
              FStarC_TypeChecker_Common.logical = b
            }
      | FStarC_TypeChecker_Common.CProb p ->
          FStarC_TypeChecker_Common.CProb
            {
              FStarC_TypeChecker_Common.pid =
                (p.FStarC_TypeChecker_Common.pid);
              FStarC_TypeChecker_Common.lhs =
                (p.FStarC_TypeChecker_Common.lhs);
              FStarC_TypeChecker_Common.relation =
                (p.FStarC_TypeChecker_Common.relation);
              FStarC_TypeChecker_Common.rhs =
                (p.FStarC_TypeChecker_Common.rhs);
              FStarC_TypeChecker_Common.element =
                (p.FStarC_TypeChecker_Common.element);
              FStarC_TypeChecker_Common.logical_guard =
                (p.FStarC_TypeChecker_Common.logical_guard);
              FStarC_TypeChecker_Common.logical_guard_uvar =
                (p.FStarC_TypeChecker_Common.logical_guard_uvar);
              FStarC_TypeChecker_Common.reason =
                (p.FStarC_TypeChecker_Common.reason);
              FStarC_TypeChecker_Common.loc =
                (p.FStarC_TypeChecker_Common.loc);
              FStarC_TypeChecker_Common.rank =
                (p.FStarC_TypeChecker_Common.rank);
              FStarC_TypeChecker_Common.logical = b
            }
let (is_top_level_prob : FStarC_TypeChecker_Common.prob -> Prims.bool) =
  fun p -> (FStarC_Compiler_List.length (p_reason p)) = Prims.int_one
let (next_pid : unit -> Prims.int) =
  let ctr = FStarC_Compiler_Util.mk_ref Prims.int_zero in
  fun uu___ ->
    FStarC_Compiler_Util.incr ctr; FStarC_Compiler_Effect.op_Bang ctr
let mk_problem :
  'uuuuu .
    worklist ->
      FStarC_Syntax_Syntax.binder Prims.list ->
        FStarC_TypeChecker_Common.prob ->
          'uuuuu ->
            FStarC_TypeChecker_Common.rel ->
              'uuuuu ->
                FStarC_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('uuuuu FStarC_TypeChecker_Common.problem * worklist)
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
                          let uu___1 = FStarC_Syntax_Syntax.mk_binder x in
                          [uu___1] in
                        FStarC_Compiler_List.op_At scope uu___ in
                  let bs =
                    FStarC_Compiler_List.op_At
                      (p_guard_uvar orig).FStarC_Syntax_Syntax.ctx_uvar_binders
                      scope1 in
                  let gamma =
                    let uu___ =
                      let uu___1 =
                        FStarC_Compiler_List.map
                          (fun b ->
                             FStarC_Syntax_Syntax.Binding_var
                               (b.FStarC_Syntax_Syntax.binder_bv)) scope1 in
                      FStarC_Compiler_List.rev uu___1 in
                    FStarC_Compiler_List.op_At uu___
                      (p_guard_uvar orig).FStarC_Syntax_Syntax.ctx_uvar_gamma in
                  let uu___ =
                    new_uvar
                      (Prims.strcat "mk_problem: logical guard for " reason)
                      wl FStarC_Compiler_Range_Type.dummyRange gamma bs
                      FStarC_Syntax_Util.ktype0
                      (FStarC_Syntax_Syntax.Allow_untyped "logical guard")
                      FStar_Pervasives_Native.None in
                  match uu___ with
                  | (ctx_uvar, lg, wl1) ->
                      let prob =
                        let uu___1 = next_pid () in
                        {
                          FStarC_TypeChecker_Common.pid = uu___1;
                          FStarC_TypeChecker_Common.lhs = lhs;
                          FStarC_TypeChecker_Common.relation = rel;
                          FStarC_TypeChecker_Common.rhs = rhs;
                          FStarC_TypeChecker_Common.element = elt;
                          FStarC_TypeChecker_Common.logical_guard = lg;
                          FStarC_TypeChecker_Common.logical_guard_uvar =
                            ctx_uvar;
                          FStarC_TypeChecker_Common.reason = (reason ::
                            (p_reason orig));
                          FStarC_TypeChecker_Common.loc = (p_loc orig);
                          FStarC_TypeChecker_Common.rank =
                            FStar_Pervasives_Native.None;
                          FStarC_TypeChecker_Common.logical =
                            (p_logical orig)
                        } in
                      (prob, wl1)
let (mk_t_problem :
  worklist ->
    FStarC_Syntax_Syntax.binder Prims.list ->
      FStarC_TypeChecker_Common.prob ->
        FStarC_Syntax_Syntax.typ ->
          FStarC_TypeChecker_Common.rel ->
            FStarC_Syntax_Syntax.typ ->
              FStarC_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                Prims.string -> (FStarC_TypeChecker_Common.prob * worklist))
  =
  fun wl ->
    fun scope ->
      fun orig ->
        fun lhs ->
          fun rel ->
            fun rhs ->
              fun elt ->
                fun reason ->
                  def_check_prob (Prims.strcat reason ".mk_t.arg") orig;
                  (let uu___1 =
                     mk_problem wl scope orig lhs rel rhs elt reason in
                   match uu___1 with
                   | (p, wl1) ->
                       (def_check_prob (Prims.strcat reason ".mk_t")
                          (FStarC_TypeChecker_Common.TProb p);
                        ((FStarC_TypeChecker_Common.TProb p), wl1)))
let (mk_c_problem :
  worklist ->
    FStarC_Syntax_Syntax.binder Prims.list ->
      FStarC_TypeChecker_Common.prob ->
        FStarC_Syntax_Syntax.comp ->
          FStarC_TypeChecker_Common.rel ->
            FStarC_Syntax_Syntax.comp ->
              FStarC_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                Prims.string -> (FStarC_TypeChecker_Common.prob * worklist))
  =
  fun wl ->
    fun scope ->
      fun orig ->
        fun lhs ->
          fun rel ->
            fun rhs ->
              fun elt ->
                fun reason ->
                  def_check_prob (Prims.strcat reason ".mk_c.arg") orig;
                  (let uu___1 =
                     mk_problem wl scope orig lhs rel rhs elt reason in
                   match uu___1 with
                   | (p, wl1) ->
                       (def_check_prob (Prims.strcat reason ".mk_c")
                          (FStarC_TypeChecker_Common.CProb p);
                        ((FStarC_TypeChecker_Common.CProb p), wl1)))
let new_problem :
  'uuuuu .
    worklist ->
      FStarC_TypeChecker_Env.env ->
        'uuuuu ->
          FStarC_TypeChecker_Common.rel ->
            'uuuuu ->
              FStarC_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStarC_Compiler_Range_Type.range ->
                  Prims.string ->
                    ('uuuuu FStarC_TypeChecker_Common.problem * worklist)
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
                        FStarC_Syntax_Util.ktype0
                    | FStar_Pervasives_Native.Some x ->
                        let bs =
                          let uu___ = FStarC_Syntax_Syntax.mk_binder x in
                          [uu___] in
                        let uu___ =
                          FStarC_Syntax_Syntax.mk_Total
                            FStarC_Syntax_Util.ktype0 in
                        FStarC_Syntax_Util.arrow bs uu___ in
                  let uu___ =
                    let uu___1 = FStarC_TypeChecker_Env.all_binders env in
                    new_uvar
                      (Prims.strcat "new_problem: logical guard for " reason)
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
                        repr_subcomp_allowed = (wl.repr_subcomp_allowed);
                        typeclass_variables = (wl.typeclass_variables)
                      } loc env.FStarC_TypeChecker_Env.gamma uu___1 lg_ty
                      (FStarC_Syntax_Syntax.Allow_untyped "logical guard")
                      FStar_Pervasives_Native.None in
                  match uu___ with
                  | (ctx_uvar, lg, wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu___1 =
                              let uu___2 =
                                let uu___3 =
                                  FStarC_Syntax_Syntax.bv_to_name x in
                                FStarC_Syntax_Syntax.as_arg uu___3 in
                              [uu___2] in
                            FStarC_Syntax_Syntax.mk_Tm_app lg uu___1 loc in
                      let prob =
                        let uu___1 = next_pid () in
                        {
                          FStarC_TypeChecker_Common.pid = uu___1;
                          FStarC_TypeChecker_Common.lhs = lhs;
                          FStarC_TypeChecker_Common.relation = rel;
                          FStarC_TypeChecker_Common.rhs = rhs;
                          FStarC_TypeChecker_Common.element = subject;
                          FStarC_TypeChecker_Common.logical_guard = lg1;
                          FStarC_TypeChecker_Common.logical_guard_uvar =
                            ctx_uvar;
                          FStarC_TypeChecker_Common.reason = [reason];
                          FStarC_TypeChecker_Common.loc = loc;
                          FStarC_TypeChecker_Common.rank =
                            FStar_Pervasives_Native.None;
                          FStarC_TypeChecker_Common.logical = false
                        } in
                      (prob, wl1)
let (problem_using_guard :
  FStarC_TypeChecker_Common.prob ->
    FStarC_Syntax_Syntax.typ ->
      FStarC_TypeChecker_Common.rel ->
        FStarC_Syntax_Syntax.typ ->
          FStarC_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
            Prims.string ->
              FStarC_Syntax_Syntax.typ FStarC_TypeChecker_Common.problem)
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
                  FStarC_TypeChecker_Common.pid = uu___;
                  FStarC_TypeChecker_Common.lhs = lhs;
                  FStarC_TypeChecker_Common.relation = rel;
                  FStarC_TypeChecker_Common.rhs = rhs;
                  FStarC_TypeChecker_Common.element = elt;
                  FStarC_TypeChecker_Common.logical_guard = (p_guard orig);
                  FStarC_TypeChecker_Common.logical_guard_uvar =
                    (p_guard_uvar orig);
                  FStarC_TypeChecker_Common.reason = (reason ::
                    (p_reason orig));
                  FStarC_TypeChecker_Common.loc = (p_loc orig);
                  FStarC_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None;
                  FStarC_TypeChecker_Common.logical = (p_logical orig)
                } in
              def_check_prob reason (FStarC_TypeChecker_Common.TProb p); p
let (guard_on_element :
  worklist ->
    FStarC_Syntax_Syntax.typ FStarC_TypeChecker_Common.problem ->
      FStarC_Syntax_Syntax.bv ->
        FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
          FStarC_Syntax_Syntax.term)
  =
  fun wl ->
    fun problem ->
      fun x ->
        fun phi ->
          match problem.FStarC_TypeChecker_Common.element with
          | FStar_Pervasives_Native.None ->
              let tcenv = p_env wl (FStarC_TypeChecker_Common.TProb problem) in
              let u =
                tcenv.FStarC_TypeChecker_Env.universe_of tcenv
                  x.FStarC_Syntax_Syntax.sort in
              FStarC_Syntax_Util.mk_forall u x phi
          | FStar_Pervasives_Native.Some e ->
              let uu___ =
                let uu___1 =
                  let uu___2 =
                    let uu___3 = FStarC_Syntax_Syntax.bv_to_name e in
                    (x, uu___3) in
                  FStarC_Syntax_Syntax.NT uu___2 in
                [uu___1] in
              FStarC_Syntax_Subst.subst uu___ phi
let (explain :
  worklist -> FStarC_TypeChecker_Common.prob -> lstring -> Prims.string) =
  fun wl ->
    fun d ->
      fun s ->
        let uu___ =
          (FStarC_Compiler_Effect.op_Bang dbg_ExplainRel) ||
            (FStarC_Compiler_Effect.op_Bang dbg_Rel) in
        if uu___
        then
          let uu___1 = FStarC_Compiler_Range_Ops.string_of_range (p_loc d) in
          let uu___2 = prob_to_string' wl d in
          let uu___3 = FStarC_Thunk.force s in
          FStarC_Compiler_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu___1 uu___2
            (FStarC_Compiler_String.concat "\n\t>" (p_reason d)) uu___3
        else
          (let d1 = maybe_invert_p d in
           let rel =
             match p_rel d1 with
             | FStarC_TypeChecker_Common.EQ -> "equal to"
             | FStarC_TypeChecker_Common.SUB -> "a subtype of"
             | uu___2 -> failwith "impossible" in
           let uu___2 =
             match d1 with
             | FStarC_TypeChecker_Common.TProb tp ->
                 FStarC_TypeChecker_Err.print_discrepancy
                   (FStarC_TypeChecker_Normalize.term_to_string (p_env wl d1))
                   tp.FStarC_TypeChecker_Common.lhs
                   tp.FStarC_TypeChecker_Common.rhs
             | FStarC_TypeChecker_Common.CProb cp ->
                 FStarC_TypeChecker_Err.print_discrepancy
                   (FStarC_TypeChecker_Normalize.comp_to_string (p_env wl d1))
                   cp.FStarC_TypeChecker_Common.lhs
                   cp.FStarC_TypeChecker_Common.rhs in
           match uu___2 with
           | (lhs, rhs) ->
               FStarC_Compiler_Util.format3
                 "%s is not %s the expected type %s" lhs rel rhs)
let (occurs :
  FStarC_Syntax_Syntax.ctx_uvar ->
    FStarC_Syntax_Syntax.term ->
      (FStarC_Syntax_Syntax.ctx_uvar Prims.list * Prims.bool))
  =
  fun uk ->
    fun t ->
      let uvars =
        let uu___ = FStarC_Syntax_Free.uvars t in
        FStarC_Class_Setlike.elems ()
          (Obj.magic
             (FStarC_Compiler_FlatSet.setlike_flat_set
                FStarC_Syntax_Free.ord_ctx_uvar)) (Obj.magic uu___) in
      let occurs1 =
        FStarC_Compiler_Util.for_some
          (fun uv ->
             FStarC_Syntax_Unionfind.equiv
               uv.FStarC_Syntax_Syntax.ctx_uvar_head
               uk.FStarC_Syntax_Syntax.ctx_uvar_head) uvars in
      (uvars, occurs1)
let (occurs_check :
  FStarC_Syntax_Syntax.ctx_uvar ->
    FStarC_Syntax_Syntax.term ->
      (FStarC_Syntax_Syntax.ctx_uvar Prims.list * Prims.bool * Prims.string
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
                   FStarC_Class_Show.show FStarC_Syntax_Print.showable_uvar
                     uk.FStarC_Syntax_Syntax.ctx_uvar_head in
                 let uu___4 =
                   FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
                 FStarC_Compiler_Util.format2
                   "occurs-check failed (%s occurs in %s)" uu___3 uu___4 in
               FStar_Pervasives_Native.Some uu___2) in
          (uvars, (Prims.op_Negation occurs1), msg)
let (occurs_full :
  FStarC_Syntax_Syntax.ctx_uvar -> FStarC_Syntax_Syntax.term -> Prims.bool) =
  fun uk ->
    fun t ->
      let uvars =
        let uu___ = FStarC_Syntax_Free.uvars_full t in
        FStarC_Class_Setlike.elems ()
          (Obj.magic
             (FStarC_Compiler_FlatSet.setlike_flat_set
                FStarC_Syntax_Free.ord_ctx_uvar)) (Obj.magic uu___) in
      let occurs1 =
        FStarC_Compiler_Util.for_some
          (fun uv ->
             FStarC_Syntax_Unionfind.equiv
               uv.FStarC_Syntax_Syntax.ctx_uvar_head
               uk.FStarC_Syntax_Syntax.ctx_uvar_head) uvars in
      occurs1
let set_uvar :
  'uuuuu .
    'uuuuu ->
      FStarC_Syntax_Syntax.ctx_uvar ->
        FStarC_Syntax_Syntax.should_check_uvar FStar_Pervasives_Native.option
          -> FStarC_Syntax_Syntax.term -> unit
  =
  fun env ->
    fun u ->
      fun should_check_opt ->
        fun t ->
          (match should_check_opt with
           | FStar_Pervasives_Native.None -> ()
           | FStar_Pervasives_Native.Some should_check ->
               let uu___1 =
                 let uu___2 =
                   FStarC_Syntax_Unionfind.find_decoration
                     u.FStarC_Syntax_Syntax.ctx_uvar_head in
                 {
                   FStarC_Syntax_Syntax.uvar_decoration_typ =
                     (uu___2.FStarC_Syntax_Syntax.uvar_decoration_typ);
                   FStarC_Syntax_Syntax.uvar_decoration_typedness_depends_on
                     =
                     (uu___2.FStarC_Syntax_Syntax.uvar_decoration_typedness_depends_on);
                   FStarC_Syntax_Syntax.uvar_decoration_should_check =
                     should_check;
                   FStarC_Syntax_Syntax.uvar_decoration_should_unrefine =
                     (uu___2.FStarC_Syntax_Syntax.uvar_decoration_should_unrefine)
                 } in
               FStarC_Syntax_Unionfind.change_decoration
                 u.FStarC_Syntax_Syntax.ctx_uvar_head uu___1);
          (let uu___2 = FStarC_Options.defensive () in
           if uu___2
           then
             let uu___3 =
               let uu___4 = occurs u t in FStar_Pervasives_Native.snd uu___4 in
             (if uu___3 then failwith "OCCURS BUG!" else ())
           else ());
          FStarC_Syntax_Util.set_uvar u.FStarC_Syntax_Syntax.ctx_uvar_head t
let (commit : FStarC_TypeChecker_Env.env_t -> uvi Prims.list -> unit) =
  fun env ->
    fun uvis ->
      FStarC_Compiler_List.iter
        (fun uu___ ->
           match uu___ with
           | UNIV (u, t) ->
               (match t with
                | FStarC_Syntax_Syntax.U_unif u' ->
                    FStarC_Syntax_Unionfind.univ_union u u'
                | uu___1 -> FStarC_Syntax_Unionfind.univ_change u t)
           | TERM (u, t) ->
               ((let uu___2 =
                   FStarC_Compiler_List.map
                     (fun b -> b.FStarC_Syntax_Syntax.binder_bv)
                     u.FStarC_Syntax_Syntax.ctx_uvar_binders in
                 FStarC_Defensive.def_check_scoped
                   FStarC_Class_Binders.hasBinders_list_bv
                   FStarC_Class_Binders.hasNames_term
                   FStarC_Syntax_Print.pretty_term t.FStarC_Syntax_Syntax.pos
                   "commit" uu___2 t);
                set_uvar env u FStar_Pervasives_Native.None t)) uvis
let (find_term_uvar :
  FStarC_Syntax_Syntax.uvar ->
    uvi Prims.list ->
      FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv ->
    fun s ->
      FStarC_Compiler_Util.find_map s
        (fun uu___ ->
           match uu___ with
           | UNIV uu___1 -> FStar_Pervasives_Native.None
           | TERM (u, t) ->
               let uu___1 =
                 FStarC_Syntax_Unionfind.equiv uv
                   u.FStarC_Syntax_Syntax.ctx_uvar_head in
               if uu___1
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None)
let (find_univ_uvar :
  FStarC_Syntax_Syntax.universe_uvar ->
    uvi Prims.list ->
      FStarC_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun u ->
    fun s ->
      FStarC_Compiler_Util.find_map s
        (fun uu___ ->
           match uu___ with
           | UNIV (u', t) ->
               let uu___1 = FStarC_Syntax_Unionfind.univ_equiv u u' in
               if uu___1
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu___1 -> FStar_Pervasives_Native.None)
let (sn' :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  =
  fun env ->
    fun t ->
      let uu___ =
        let uu___1 =
          FStarC_TypeChecker_Normalize.normalize
            [FStarC_TypeChecker_Env.Beta; FStarC_TypeChecker_Env.Reify] env t in
        FStarC_Syntax_Subst.compress uu___1 in
      FStarC_Syntax_Util.unlazy_emb uu___
let (sn :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  =
  fun env ->
    fun t ->
      let uu___ =
        let uu___1 =
          let uu___2 = FStarC_TypeChecker_Env.current_module env in
          FStarC_Ident.string_of_lid uu___2 in
        FStar_Pervasives_Native.Some uu___1 in
      FStarC_Profiling.profile (fun uu___1 -> sn' env t) uu___
        "FStarC.TypeChecker.Rel.sn"
let (norm_with_steps :
  Prims.string ->
    FStarC_TypeChecker_Env.steps ->
      FStarC_TypeChecker_Env.env ->
        FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  =
  fun profiling_tag ->
    fun steps ->
      fun env ->
        fun t ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStarC_TypeChecker_Env.current_module env in
              FStarC_Ident.string_of_lid uu___2 in
            FStar_Pervasives_Native.Some uu___1 in
          FStarC_Profiling.profile
            (fun uu___1 -> FStarC_TypeChecker_Normalize.normalize steps env t)
            uu___ profiling_tag
let (should_strongly_reduce : FStarC_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu___ =
      let uu___1 = FStarC_Syntax_Util.unascribe t in
      FStarC_Syntax_Util.head_and_args uu___1 in
    match uu___ with
    | (h, uu___1) ->
        let uu___2 =
          let uu___3 = FStarC_Syntax_Subst.compress h in
          uu___3.FStarC_Syntax_Syntax.n in
        (match uu___2 with
         | FStarC_Syntax_Syntax.Tm_constant (FStarC_Const.Const_reify uu___3)
             -> true
         | uu___3 -> false)
let (whnf :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  =
  fun env ->
    fun t ->
      let norm steps t1 =
        let uu___ =
          let uu___1 =
            let uu___2 = FStarC_Syntax_Util.unmeta t1 in
            FStarC_TypeChecker_Normalize.normalize steps env uu___2 in
          FStarC_Syntax_Subst.compress uu___1 in
        FStarC_Syntax_Util.unlazy_emb uu___ in
      let uu___ =
        let uu___1 =
          let uu___2 = FStarC_TypeChecker_Env.current_module env in
          FStarC_Ident.string_of_lid uu___2 in
        FStar_Pervasives_Native.Some uu___1 in
      FStarC_Profiling.profile
        (fun uu___1 ->
           let steps =
             let uu___2 =
               let uu___3 = should_strongly_reduce t in
               if uu___3
               then
                 [FStarC_TypeChecker_Env.Exclude FStarC_TypeChecker_Env.Zeta;
                 FStarC_TypeChecker_Env.UnfoldUntil
                   FStarC_Syntax_Syntax.delta_constant]
               else [FStarC_TypeChecker_Env.Weak; FStarC_TypeChecker_Env.HNF] in
             FStarC_Compiler_List.op_At uu___2
               [FStarC_TypeChecker_Env.Beta;
               FStarC_TypeChecker_Env.Reify;
               FStarC_TypeChecker_Env.Primops] in
           norm steps t) uu___ "FStarC.TypeChecker.Rel.whnf"
let norm_arg :
  'uuuuu .
    FStarC_TypeChecker_Env.env ->
      (FStarC_Syntax_Syntax.term * 'uuuuu) ->
        (FStarC_Syntax_Syntax.term * 'uuuuu)
  =
  fun env ->
    fun t ->
      let uu___ = sn env (FStar_Pervasives_Native.fst t) in
      (uu___, (FStar_Pervasives_Native.snd t))
let (sn_binders :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.binders -> FStarC_Syntax_Syntax.binder Prims.list)
  =
  fun env ->
    fun binders ->
      FStarC_Compiler_List.map
        (fun b ->
           let uu___ =
             let uu___1 = b.FStarC_Syntax_Syntax.binder_bv in
             let uu___2 =
               sn env
                 (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
             {
               FStarC_Syntax_Syntax.ppname =
                 (uu___1.FStarC_Syntax_Syntax.ppname);
               FStarC_Syntax_Syntax.index =
                 (uu___1.FStarC_Syntax_Syntax.index);
               FStarC_Syntax_Syntax.sort = uu___2
             } in
           {
             FStarC_Syntax_Syntax.binder_bv = uu___;
             FStarC_Syntax_Syntax.binder_qual =
               (b.FStarC_Syntax_Syntax.binder_qual);
             FStarC_Syntax_Syntax.binder_positivity =
               (b.FStarC_Syntax_Syntax.binder_positivity);
             FStarC_Syntax_Syntax.binder_attrs =
               (b.FStarC_Syntax_Syntax.binder_attrs)
           }) binders
let (norm_univ :
  worklist -> FStarC_Syntax_Syntax.universe -> FStarC_Syntax_Syntax.universe)
  =
  fun wl ->
    fun u ->
      let rec aux u1 =
        let u2 = FStarC_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStarC_Syntax_Syntax.U_succ u3 ->
            let uu___ = aux u3 in FStarC_Syntax_Syntax.U_succ uu___
        | FStarC_Syntax_Syntax.U_max us ->
            let uu___ = FStarC_Compiler_List.map aux us in
            FStarC_Syntax_Syntax.U_max uu___
        | uu___ -> u2 in
      let uu___ = aux u in
      FStarC_TypeChecker_Normalize.normalize_universe wl.tcenv uu___
let (normalize_refinement :
  FStarC_TypeChecker_Env.steps ->
    FStarC_TypeChecker_Env.env ->
      FStarC_Syntax_Syntax.typ -> FStarC_Syntax_Syntax.term)
  =
  fun steps ->
    fun env ->
      fun t0 ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStarC_TypeChecker_Env.current_module env in
            FStarC_Ident.string_of_lid uu___2 in
          FStar_Pervasives_Native.Some uu___1 in
        FStarC_Profiling.profile
          (fun uu___1 ->
             FStarC_TypeChecker_Normalize.normalize_refinement steps env t0)
          uu___ "FStarC.TypeChecker.Rel.normalize_refinement"
let (base_and_refinement_maybe_delta :
  Prims.bool ->
    FStarC_TypeChecker_Env.env ->
      FStarC_Syntax_Syntax.term ->
        (FStarC_Syntax_Syntax.term * (FStarC_Syntax_Syntax.bv *
          FStarC_Syntax_Syntax.term) FStar_Pervasives_Native.option))
  =
  fun should_delta ->
    fun env ->
      fun t1 ->
        let norm_refinement env1 t =
          let steps =
            if should_delta
            then
              [FStarC_TypeChecker_Env.Weak;
              FStarC_TypeChecker_Env.HNF;
              FStarC_TypeChecker_Env.UnfoldUntil
                FStarC_Syntax_Syntax.delta_constant]
            else [FStarC_TypeChecker_Env.Weak; FStarC_TypeChecker_Env.HNF] in
          normalize_refinement steps env1 t in
        let rec aux norm t11 =
          let t12 = FStarC_Syntax_Util.unmeta t11 in
          match t12.FStarC_Syntax_Syntax.n with
          | FStarC_Syntax_Syntax.Tm_refine
              { FStarC_Syntax_Syntax.b = x; FStarC_Syntax_Syntax.phi = phi;_}
              ->
              if norm
              then
                ((x.FStarC_Syntax_Syntax.sort),
                  (FStar_Pervasives_Native.Some (x, phi)))
              else
                (let uu___1 = norm_refinement env t12 in
                 match uu___1 with
                 | {
                     FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_refine
                       { FStarC_Syntax_Syntax.b = x1;
                         FStarC_Syntax_Syntax.phi = phi1;_};
                     FStarC_Syntax_Syntax.pos = uu___2;
                     FStarC_Syntax_Syntax.vars = uu___3;
                     FStarC_Syntax_Syntax.hash_code = uu___4;_} ->
                     ((x1.FStarC_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu___2 =
                       let uu___3 =
                         FStarC_Class_Show.show
                           FStarC_Syntax_Print.showable_term tt in
                       let uu___4 =
                         FStarC_Class_Tagged.tag_of
                           FStarC_Syntax_Syntax.tagged_term tt in
                       FStarC_Compiler_Util.format2
                         "impossible: Got %s ... %s\n" uu___3 uu___4 in
                     failwith uu___2)
          | FStarC_Syntax_Syntax.Tm_lazy i ->
              let uu___ = FStarC_Syntax_Util.unfold_lazy i in aux norm uu___
          | FStarC_Syntax_Syntax.Tm_uinst uu___ ->
              if norm
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12 in
                 let uu___2 =
                   let uu___3 = FStarC_Syntax_Subst.compress t1' in
                   uu___3.FStarC_Syntax_Syntax.n in
                 match uu___2 with
                 | FStarC_Syntax_Syntax.Tm_refine uu___3 -> aux true t1'
                 | uu___3 -> (t12, FStar_Pervasives_Native.None))
          | FStarC_Syntax_Syntax.Tm_fvar uu___ ->
              if norm
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12 in
                 let uu___2 =
                   let uu___3 = FStarC_Syntax_Subst.compress t1' in
                   uu___3.FStarC_Syntax_Syntax.n in
                 match uu___2 with
                 | FStarC_Syntax_Syntax.Tm_refine uu___3 -> aux true t1'
                 | uu___3 -> (t12, FStar_Pervasives_Native.None))
          | FStarC_Syntax_Syntax.Tm_app uu___ ->
              if norm
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12 in
                 let uu___2 =
                   let uu___3 = FStarC_Syntax_Subst.compress t1' in
                   uu___3.FStarC_Syntax_Syntax.n in
                 match uu___2 with
                 | FStarC_Syntax_Syntax.Tm_refine uu___3 -> aux true t1'
                 | uu___3 -> (t12, FStar_Pervasives_Native.None))
          | FStarC_Syntax_Syntax.Tm_type uu___ ->
              (t12, FStar_Pervasives_Native.None)
          | FStarC_Syntax_Syntax.Tm_constant uu___ ->
              (t12, FStar_Pervasives_Native.None)
          | FStarC_Syntax_Syntax.Tm_name uu___ ->
              (t12, FStar_Pervasives_Native.None)
          | FStarC_Syntax_Syntax.Tm_bvar uu___ ->
              (t12, FStar_Pervasives_Native.None)
          | FStarC_Syntax_Syntax.Tm_arrow uu___ ->
              (t12, FStar_Pervasives_Native.None)
          | FStarC_Syntax_Syntax.Tm_abs uu___ ->
              (t12, FStar_Pervasives_Native.None)
          | FStarC_Syntax_Syntax.Tm_quoted uu___ ->
              (t12, FStar_Pervasives_Native.None)
          | FStarC_Syntax_Syntax.Tm_uvar uu___ ->
              (t12, FStar_Pervasives_Native.None)
          | FStarC_Syntax_Syntax.Tm_let uu___ ->
              (t12, FStar_Pervasives_Native.None)
          | FStarC_Syntax_Syntax.Tm_match uu___ ->
              (t12, FStar_Pervasives_Native.None)
          | FStarC_Syntax_Syntax.Tm_meta uu___ ->
              let uu___1 =
                let uu___2 =
                  FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                    t12 in
                let uu___3 =
                  FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term
                    t12 in
                FStarC_Compiler_Util.format2
                  "impossible (outer): Got %s ... %s\n" uu___2 uu___3 in
              failwith uu___1
          | FStarC_Syntax_Syntax.Tm_ascribed uu___ ->
              let uu___1 =
                let uu___2 =
                  FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                    t12 in
                let uu___3 =
                  FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term
                    t12 in
                FStarC_Compiler_Util.format2
                  "impossible (outer): Got %s ... %s\n" uu___2 uu___3 in
              failwith uu___1
          | FStarC_Syntax_Syntax.Tm_delayed uu___ ->
              let uu___1 =
                let uu___2 =
                  FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                    t12 in
                let uu___3 =
                  FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term
                    t12 in
                FStarC_Compiler_Util.format2
                  "impossible (outer): Got %s ... %s\n" uu___2 uu___3 in
              failwith uu___1
          | FStarC_Syntax_Syntax.Tm_unknown ->
              let uu___ =
                let uu___1 =
                  FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                    t12 in
                let uu___2 =
                  FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term
                    t12 in
                FStarC_Compiler_Util.format2
                  "impossible (outer): Got %s ... %s\n" uu___1 uu___2 in
              failwith uu___ in
        let uu___ = whnf env t1 in aux false uu___
let (base_and_refinement :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.term ->
      (FStarC_Syntax_Syntax.term * (FStarC_Syntax_Syntax.bv *
        FStarC_Syntax_Syntax.term) FStar_Pervasives_Native.option))
  = fun env -> fun t -> base_and_refinement_maybe_delta false env t
let (unrefine :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.typ -> FStarC_Syntax_Syntax.typ)
  =
  fun env ->
    fun t ->
      let uu___ = base_and_refinement env t in
      FStar_Pervasives_Native.fst uu___
let (trivial_refinement :
  FStarC_Syntax_Syntax.term ->
    (FStarC_Syntax_Syntax.bv * FStarC_Syntax_Syntax.term))
  =
  fun t ->
    let uu___ = FStarC_Syntax_Syntax.null_bv t in
    (uu___, FStarC_Syntax_Util.t_true)
let (as_refinement :
  Prims.bool ->
    FStarC_TypeChecker_Env.env ->
      FStarC_Syntax_Syntax.term ->
        (FStarC_Syntax_Syntax.bv * FStarC_Syntax_Syntax.term))
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
  (FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax *
    (FStarC_Syntax_Syntax.bv * FStarC_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStarC_Syntax_Syntax.term)
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
             FStarC_Syntax_Syntax.mk
               (FStarC_Syntax_Syntax.Tm_refine
                  {
                    FStarC_Syntax_Syntax.b = y;
                    FStarC_Syntax_Syntax.phi = phi
                  }) t_base.FStarC_Syntax_Syntax.pos)
let (wl_to_string : worklist -> Prims.string) =
  fun wl ->
    let probs_to_string ps =
      let uu___ = FStarC_Compiler_List.map (prob_to_string' wl) ps in
      FStarC_Compiler_String.concat "\n\t" uu___ in
    let cprobs_to_string ps =
      let uu___ =
        let uu___1 = FStarC_Compiler_CList.map (prob_to_string' wl) ps in
        FStarC_Class_Listlike.to_list
          (FStarC_Compiler_CList.listlike_clist ()) uu___1 in
      FStarC_Compiler_String.concat "\n\t" uu___ in
    let uu___ = probs_to_string wl.attempting in
    let uu___1 =
      let uu___2 =
        FStarC_Compiler_CList.map
          (fun uu___3 -> match uu___3 with | (uu___4, uu___5, uu___6, x) -> x)
          wl.wl_deferred in
      cprobs_to_string uu___2 in
    FStarC_Compiler_Util.format2
      "{ attempting = [ %s ];\ndeferred = [ %s ] }\n" uu___ uu___1
let (showable_wl : worklist FStarC_Class_Show.showable) =
  { FStarC_Class_Show.show = wl_to_string }
type flex_t =
  | Flex of (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.ctx_uvar *
  FStarC_Syntax_Syntax.args) 
let (uu___is_Flex : flex_t -> Prims.bool) = fun projectee -> true
let (__proj__Flex__item___0 :
  flex_t ->
    (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.ctx_uvar *
      FStarC_Syntax_Syntax.args))
  = fun projectee -> match projectee with | Flex _0 -> _0
let (flex_reason : flex_t -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | Flex (uu___1, u, uu___2) -> u.FStarC_Syntax_Syntax.ctx_uvar_reason
let (flex_uvar : flex_t -> FStarC_Syntax_Syntax.ctx_uvar) =
  fun uu___ -> match uu___ with | Flex (uu___1, u, uu___2) -> u
let (flex_uvar_has_meta_tac : FStarC_Syntax_Syntax.ctx_uvar -> Prims.bool) =
  fun u ->
    match u.FStarC_Syntax_Syntax.ctx_uvar_meta with
    | FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Ctx_uvar_meta_tac
        uu___) -> true
    | uu___ -> false
let (flex_t_to_string : flex_t -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | Flex (uu___1, c, args) ->
        let uu___2 =
          FStarC_Class_Show.show FStarC_Syntax_Print.showable_ctxu c in
        let uu___3 =
          FStarC_Class_Show.show
            (FStarC_Class_Show.show_list
               (FStarC_Class_Show.show_tuple2
                  FStarC_Syntax_Print.showable_term
                  FStarC_Syntax_Print.showable_aqual)) args in
        FStarC_Compiler_Util.format2 "%s [%s]" uu___2 uu___3
let (is_flex : FStarC_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu___ = FStarC_Syntax_Util.head_and_args t in
    match uu___ with
    | (head, _args) ->
        let uu___1 =
          let uu___2 = FStarC_Syntax_Subst.compress head in
          uu___2.FStarC_Syntax_Syntax.n in
        (match uu___1 with
         | FStarC_Syntax_Syntax.Tm_uvar uu___2 -> true
         | uu___2 -> false)
let (flex_uvar_head :
  FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.ctx_uvar) =
  fun t ->
    let uu___ = FStarC_Syntax_Util.head_and_args t in
    match uu___ with
    | (head, _args) ->
        let uu___1 =
          let uu___2 = FStarC_Syntax_Subst.compress head in
          uu___2.FStarC_Syntax_Syntax.n in
        (match uu___1 with
         | FStarC_Syntax_Syntax.Tm_uvar (u, uu___2) -> u
         | uu___2 -> failwith "Not a flex-uvar")
let ensure_no_uvar_subst :
  'uuuuu .
    'uuuuu ->
      FStarC_Syntax_Syntax.term ->
        worklist -> (FStarC_Syntax_Syntax.term * worklist)
  =
  fun env ->
    fun t0 ->
      fun wl ->
        let bv_not_affected_by s x =
          let t_x = FStarC_Syntax_Syntax.bv_to_name x in
          let t_x' = FStarC_Syntax_Subst.subst' s t_x in
          let uu___ =
            let uu___1 = FStarC_Syntax_Subst.compress t_x' in
            uu___1.FStarC_Syntax_Syntax.n in
          match uu___ with
          | FStarC_Syntax_Syntax.Tm_name y -> FStarC_Syntax_Syntax.bv_eq x y
          | uu___1 -> false in
        let binding_not_affected_by s b =
          match b with
          | FStarC_Syntax_Syntax.Binding_var x -> bv_not_affected_by s x
          | uu___ -> true in
        let uu___ = FStarC_Syntax_Util.head_and_args t0 in
        match uu___ with
        | (head, args) ->
            let uu___1 =
              let uu___2 = FStarC_Syntax_Subst.compress head in
              uu___2.FStarC_Syntax_Syntax.n in
            (match uu___1 with
             | FStarC_Syntax_Syntax.Tm_uvar (uv, ([], uu___2)) -> (t0, wl)
             | FStarC_Syntax_Syntax.Tm_uvar (uv, uu___2) when
                 FStarC_Compiler_List.isEmpty
                   uv.FStarC_Syntax_Syntax.ctx_uvar_binders
                 -> (t0, wl)
             | FStarC_Syntax_Syntax.Tm_uvar (uv, s) ->
                 let uu___2 =
                   FStarC_Common.max_suffix (binding_not_affected_by s)
                     uv.FStarC_Syntax_Syntax.ctx_uvar_gamma in
                 (match uu___2 with
                  | (gamma_aff, new_gamma) ->
                      (match gamma_aff with
                       | [] -> (t0, wl)
                       | uu___3 ->
                           let dom_binders =
                             FStarC_TypeChecker_Env.binders_of_bindings
                               gamma_aff in
                           let uu___4 =
                             let uu___5 =
                               FStarC_TypeChecker_Env.binders_of_bindings
                                 new_gamma in
                             let uu___6 =
                               let uu___7 =
                                 let uu___8 =
                                   FStarC_Syntax_Util.ctx_uvar_typ uv in
                                 FStarC_Syntax_Syntax.mk_Total uu___8 in
                               FStarC_Syntax_Util.arrow dom_binders uu___7 in
                             let uu___7 =
                               FStarC_Syntax_Util.ctx_uvar_should_check uv in
                             new_uvar
                               (Prims.strcat
                                  uv.FStarC_Syntax_Syntax.ctx_uvar_reason
                                  "; force delayed") wl
                               t0.FStarC_Syntax_Syntax.pos new_gamma uu___5
                               uu___6 uu___7
                               uv.FStarC_Syntax_Syntax.ctx_uvar_meta in
                           (match uu___4 with
                            | (v, t_v, wl1) ->
                                let args_sol =
                                  FStarC_Compiler_List.map
                                    FStarC_Syntax_Util.arg_of_non_null_binder
                                    dom_binders in
                                let sol =
                                  FStarC_Syntax_Syntax.mk_Tm_app t_v args_sol
                                    t0.FStarC_Syntax_Syntax.pos in
                                ((let uu___6 =
                                    FStarC_Compiler_Effect.op_Bang dbg_Rel in
                                  if uu___6
                                  then
                                    let uu___7 =
                                      FStarC_Class_Show.show
                                        FStarC_Syntax_Print.showable_ctxu uv in
                                    let uu___8 =
                                      FStarC_Class_Show.show
                                        FStarC_Syntax_Print.showable_term sol in
                                    FStarC_Compiler_Util.print2
                                      "ensure_no_uvar_subst solving %s with %s\n"
                                      uu___7 uu___8
                                  else ());
                                 set_uvar env uv
                                   (FStar_Pervasives_Native.Some
                                      FStarC_Syntax_Syntax.Already_checked)
                                   sol;
                                 (let args_sol_s =
                                    FStarC_Compiler_List.map
                                      (fun uu___7 ->
                                         match uu___7 with
                                         | (a, i) ->
                                             let uu___8 =
                                               FStarC_Syntax_Subst.subst' s a in
                                             (uu___8, i)) args_sol in
                                  let t =
                                    FStarC_Syntax_Syntax.mk_Tm_app t_v
                                      (FStarC_Compiler_List.op_At args_sol_s
                                         args) t0.FStarC_Syntax_Syntax.pos in
                                  (t, wl1))))))
             | uu___2 ->
                 let uu___3 =
                   let uu___4 =
                     FStarC_Class_Tagged.tag_of
                       FStarC_Syntax_Syntax.tagged_term t0 in
                   let uu___5 =
                     FStarC_Class_Tagged.tag_of
                       FStarC_Syntax_Syntax.tagged_term head in
                   let uu___6 =
                     let uu___7 = FStarC_Syntax_Subst.compress head in
                     FStarC_Class_Tagged.tag_of
                       FStarC_Syntax_Syntax.tagged_term uu___7 in
                   FStarC_Compiler_Util.format3
                     "ensure_no_uvar_subst: expected a uvar at the head (%s-%s-%s)"
                     uu___4 uu___5 uu___6 in
                 failwith uu___3)
let (no_free_uvars : FStarC_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    (let uu___ = FStarC_Syntax_Free.uvars t in
     FStarC_Class_Setlike.is_empty ()
       (Obj.magic
          (FStarC_Compiler_FlatSet.setlike_flat_set
             FStarC_Syntax_Free.ord_ctx_uvar)) (Obj.magic uu___))
      &&
      (let uu___ = FStarC_Syntax_Free.univs t in
       FStarC_Class_Setlike.is_empty ()
         (Obj.magic
            (FStarC_Compiler_FlatSet.setlike_flat_set
               FStarC_Syntax_Free.ord_univ_uvar)) (Obj.magic uu___))
let rec (may_relate_with_logical_guard :
  FStarC_TypeChecker_Env.env ->
    Prims.bool -> FStarC_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env ->
    fun is_eq ->
      fun head ->
        let uu___ =
          let uu___1 = FStarC_Syntax_Subst.compress head in
          uu___1.FStarC_Syntax_Syntax.n in
        match uu___ with
        | FStarC_Syntax_Syntax.Tm_name uu___1 -> true
        | FStarC_Syntax_Syntax.Tm_match uu___1 -> true
        | FStarC_Syntax_Syntax.Tm_fvar fv ->
            let uu___1 = FStarC_TypeChecker_Env.delta_depth_of_fv env fv in
            (match uu___1 with
             | FStarC_Syntax_Syntax.Delta_equational_at_level uu___2 -> true
             | FStarC_Syntax_Syntax.Delta_abstract uu___2 -> is_eq
             | uu___2 -> false)
        | FStarC_Syntax_Syntax.Tm_ascribed
            { FStarC_Syntax_Syntax.tm = t; FStarC_Syntax_Syntax.asc = uu___1;
              FStarC_Syntax_Syntax.eff_opt = uu___2;_}
            -> may_relate_with_logical_guard env is_eq t
        | FStarC_Syntax_Syntax.Tm_uinst (t, uu___1) ->
            may_relate_with_logical_guard env is_eq t
        | FStarC_Syntax_Syntax.Tm_meta
            { FStarC_Syntax_Syntax.tm2 = t;
              FStarC_Syntax_Syntax.meta = uu___1;_}
            -> may_relate_with_logical_guard env is_eq t
        | uu___1 -> false
let (may_relate :
  FStarC_TypeChecker_Env.env ->
    FStarC_TypeChecker_Common.rel -> FStarC_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env ->
    fun prel ->
      fun head ->
        may_relate_with_logical_guard env
          (FStarC_TypeChecker_Common.uu___is_EQ prel) head
let (destruct_flex_t' : FStarC_Syntax_Syntax.term -> flex_t) =
  fun t ->
    let uu___ = FStarC_Syntax_Util.head_and_args t in
    match uu___ with
    | (head, args) ->
        let uu___1 =
          let uu___2 = FStarC_Syntax_Subst.compress head in
          uu___2.FStarC_Syntax_Syntax.n in
        (match uu___1 with
         | FStarC_Syntax_Syntax.Tm_uvar (uv, s) -> Flex (t, uv, args)
         | uu___2 -> failwith "Not a flex-uvar")
let (destruct_flex_t :
  FStarC_Syntax_Syntax.term -> worklist -> (flex_t * worklist)) =
  fun t ->
    fun wl ->
      let uu___ = ensure_no_uvar_subst wl.tcenv t wl in
      match uu___ with
      | (t1, wl1) -> let uu___1 = destruct_flex_t' t1 in (uu___1, wl1)
let (u_abs :
  FStarC_Syntax_Syntax.typ ->
    FStarC_Syntax_Syntax.binders ->
      FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  =
  fun k ->
    fun ys ->
      fun t ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStarC_Syntax_Subst.compress k in
            uu___2.FStarC_Syntax_Syntax.n in
          match uu___1 with
          | FStarC_Syntax_Syntax.Tm_arrow
              { FStarC_Syntax_Syntax.bs1 = bs;
                FStarC_Syntax_Syntax.comp = c;_}
              ->
              if
                (FStarC_Compiler_List.length bs) =
                  (FStarC_Compiler_List.length ys)
              then
                let uu___2 = FStarC_Syntax_Subst.open_comp bs c in
                ((ys, t), uu___2)
              else
                (let uu___3 = FStarC_Syntax_Util.abs_formals t in
                 match uu___3 with
                 | (ys', t1, uu___4) ->
                     let uu___5 = FStarC_Syntax_Util.arrow_formals_comp k in
                     (((FStarC_Compiler_List.op_At ys ys'), t1), uu___5))
          | uu___2 ->
              let uu___3 =
                let uu___4 = FStarC_Syntax_Syntax.mk_Total k in ([], uu___4) in
              ((ys, t), uu___3) in
        match uu___ with
        | ((ys1, t1), (xs, c)) ->
            if
              (FStarC_Compiler_List.length xs) <>
                (FStarC_Compiler_List.length ys1)
            then
              FStarC_Syntax_Util.abs ys1 t1
                (FStar_Pervasives_Native.Some
                   (FStarC_Syntax_Util.mk_residual_comp
                      FStarC_Parser_Const.effect_Tot_lid
                      FStar_Pervasives_Native.None []))
            else
              (let c1 =
                 let uu___2 = FStarC_Syntax_Util.rename_binders xs ys1 in
                 FStarC_Syntax_Subst.subst_comp uu___2 c in
               let uu___2 =
                 let uu___3 = FStarC_Syntax_Util.residual_comp_of_comp c1 in
                 FStar_Pervasives_Native.Some uu___3 in
               FStarC_Syntax_Util.abs ys1 t1 uu___2)
let (solve_prob' :
  Prims.bool ->
    FStarC_TypeChecker_Common.prob ->
      FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax
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
               | FStar_Pervasives_Native.None -> FStarC_Syntax_Util.t_true
               | FStar_Pervasives_Native.Some phi1 -> phi1 in
             let assign_solution xs uv phi1 =
               (let uu___2 = FStarC_Compiler_Effect.op_Bang dbg_Rel in
                if uu___2
                then
                  let uu___3 =
                    FStarC_Compiler_Util.string_of_int (p_pid prob) in
                  let uu___4 =
                    FStarC_Class_Show.show FStarC_Syntax_Print.showable_ctxu
                      uv in
                  let uu___5 =
                    FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                      phi1 in
                  FStarC_Compiler_Util.print3
                    "Solving %s (%s) with formula %s\n" uu___3 uu___4 uu___5
                else ());
               (let phi2 =
                  FStarC_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStarC_Syntax_Util.residual_tot
                          FStarC_Syntax_Util.ktype0)) in
                (let uu___3 =
                   let uu___4 =
                     FStarC_Compiler_Util.string_of_int (p_pid prob) in
                   Prims.strcat "solve_prob'.sol." uu___4 in
                 let uu___4 =
                   let uu___5 = p_scope prob in
                   FStarC_Compiler_List.map
                     (fun b -> b.FStarC_Syntax_Syntax.binder_bv) uu___5 in
                 FStarC_Defensive.def_check_scoped
                   FStarC_Class_Binders.hasBinders_list_bv
                   FStarC_Class_Binders.hasNames_term
                   FStarC_Syntax_Print.pretty_term (p_loc prob) uu___3 uu___4
                   phi2);
                set_uvar wl.tcenv uv FStar_Pervasives_Native.None phi2) in
             let uv = p_guard_uvar prob in
             let fail uu___1 =
               let uu___2 =
                 let uu___3 =
                   FStarC_Class_Show.show FStarC_Syntax_Print.showable_ctxu
                     uv in
                 let uu___4 =
                   FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                     (p_guard prob) in
                 FStarC_Compiler_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu___3 uu___4 in
               failwith uu___2 in
             let args_as_binders args =
               FStarC_Compiler_List.collect
                 (fun uu___1 ->
                    match uu___1 with
                    | (a, i) ->
                        let uu___2 =
                          let uu___3 = FStarC_Syntax_Subst.compress a in
                          uu___3.FStarC_Syntax_Syntax.n in
                        (match uu___2 with
                         | FStarC_Syntax_Syntax.Tm_name x ->
                             let uu___3 =
                               FStarC_Syntax_Util.bqual_and_attrs_of_aqual i in
                             (match uu___3 with
                              | (q, attrs) ->
                                  let uu___4 =
                                    FStarC_Syntax_Util.parse_positivity_attributes
                                      attrs in
                                  (match uu___4 with
                                   | (pq, attrs1) ->
                                       let uu___5 =
                                         FStarC_Syntax_Syntax.mk_binder_with_attrs
                                           x q pq attrs1 in
                                       [uu___5]))
                         | uu___3 -> (fail (); []))) args in
             let wl1 =
               let g = whnf (p_guard_env wl prob) (p_guard prob) in
               let uu___1 =
                 let uu___2 = is_flex g in Prims.op_Negation uu___2 in
               if uu___1
               then (if resolve_ok then wl else (fail (); wl))
               else
                 (let uu___3 = destruct_flex_t g wl in
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
               repr_subcomp_allowed = (wl1.repr_subcomp_allowed);
               typeclass_variables = (wl1.typeclass_variables)
             })
let (extend_universe_solution :
  Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid ->
    fun sol ->
      fun wl ->
        (let uu___1 = FStarC_Compiler_Effect.op_Bang dbg_Rel in
         if uu___1
         then
           let uu___2 = FStarC_Compiler_Util.string_of_int pid in
           let uu___3 = uvis_to_string wl.tcenv sol in
           FStarC_Compiler_Util.print2 "Solving %s: with [%s]\n" uu___2
             uu___3
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
          repr_subcomp_allowed = (wl.repr_subcomp_allowed);
          typeclass_variables = (wl.typeclass_variables)
        }
let (solve_prob :
  FStarC_TypeChecker_Common.prob ->
    FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      uvi Prims.list -> worklist -> worklist)
  =
  fun prob ->
    fun logical_guard ->
      fun uvis ->
        fun wl ->
          def_check_prob "solve_prob.prob" prob;
          FStarC_Compiler_Util.iter_opt logical_guard
            (def_check_term_scoped_in_prob "solve_prob.guard" prob);
          (let uu___3 = FStarC_Compiler_Effect.op_Bang dbg_Rel in
           if uu___3
           then
             let uu___4 = FStarC_Compiler_Util.string_of_int (p_pid prob) in
             let uu___5 = uvis_to_string wl.tcenv uvis in
             FStarC_Compiler_Util.print2 "Solving %s: with %s\n" uu___4
               uu___5
           else ());
          solve_prob' false prob logical_guard uvis wl
let rec (maximal_prefix :
  FStarC_Syntax_Syntax.binders ->
    FStarC_Syntax_Syntax.binders ->
      (FStarC_Syntax_Syntax.binders * (FStarC_Syntax_Syntax.binders *
        FStarC_Syntax_Syntax.binders)))
  =
  fun bs ->
    fun bs' ->
      match (bs, bs') with
      | (binder1::bs_tail,
         { FStarC_Syntax_Syntax.binder_bv = b';
           FStarC_Syntax_Syntax.binder_qual = i';
           FStarC_Syntax_Syntax.binder_positivity = uu___;
           FStarC_Syntax_Syntax.binder_attrs = uu___1;_}::bs'_tail)
          ->
          let uu___2 =
            FStarC_Syntax_Syntax.bv_eq binder1.FStarC_Syntax_Syntax.binder_bv
              b' in
          if uu___2
          then
            let uu___3 = maximal_prefix bs_tail bs'_tail in
            (match uu___3 with | (pfx, rest) -> ((binder1 :: pfx), rest))
          else ([], (bs, bs'))
      | uu___ -> ([], (bs, bs'))
let (extend_gamma :
  FStarC_Syntax_Syntax.gamma ->
    FStarC_Syntax_Syntax.binders -> FStarC_Syntax_Syntax.binding Prims.list)
  =
  fun g ->
    fun bs ->
      FStarC_Compiler_List.fold_left
        (fun g1 ->
           fun uu___ ->
             match uu___ with
             | { FStarC_Syntax_Syntax.binder_bv = x;
                 FStarC_Syntax_Syntax.binder_qual = uu___1;
                 FStarC_Syntax_Syntax.binder_positivity = uu___2;
                 FStarC_Syntax_Syntax.binder_attrs = uu___3;_} ->
                 (FStarC_Syntax_Syntax.Binding_var x) :: g1) g bs
let (gamma_until :
  FStarC_Syntax_Syntax.gamma ->
    FStarC_Syntax_Syntax.binders -> FStarC_Syntax_Syntax.binding Prims.list)
  =
  fun g ->
    fun bs ->
      let uu___ = FStarC_Compiler_List.last_opt bs in
      match uu___ with
      | FStar_Pervasives_Native.None -> []
      | FStar_Pervasives_Native.Some
          { FStarC_Syntax_Syntax.binder_bv = x;
            FStarC_Syntax_Syntax.binder_qual = uu___1;
            FStarC_Syntax_Syntax.binder_positivity = uu___2;
            FStarC_Syntax_Syntax.binder_attrs = uu___3;_}
          ->
          let uu___4 =
            FStarC_Compiler_Util.prefix_until
              (fun uu___5 ->
                 match uu___5 with
                 | FStarC_Syntax_Syntax.Binding_var x' ->
                     FStarC_Syntax_Syntax.bv_eq x x'
                 | uu___6 -> false) g in
          (match uu___4 with
           | FStar_Pervasives_Native.None -> []
           | FStar_Pervasives_Native.Some (uu___5, bx, rest) -> bx :: rest)
let restrict_ctx :
  'uuuuu .
    'uuuuu ->
      FStarC_Syntax_Syntax.ctx_uvar ->
        FStarC_Syntax_Syntax.binders ->
          FStarC_Syntax_Syntax.ctx_uvar -> worklist -> worklist
  =
  fun env ->
    fun tgt ->
      fun bs ->
        fun src ->
          fun wl ->
            let uu___ =
              maximal_prefix tgt.FStarC_Syntax_Syntax.ctx_uvar_binders
                src.FStarC_Syntax_Syntax.ctx_uvar_binders in
            match uu___ with
            | (pfx, uu___1) ->
                let g =
                  gamma_until src.FStarC_Syntax_Syntax.ctx_uvar_gamma pfx in
                let aux t f =
                  let uu___2 =
                    let uu___3 =
                      let uu___4 =
                        FStarC_Class_Show.show
                          FStarC_Syntax_Print.showable_uvar
                          src.FStarC_Syntax_Syntax.ctx_uvar_head in
                      Prims.strcat "restricted " uu___4 in
                    let uu___4 = FStarC_Syntax_Util.ctx_uvar_should_check src in
                    new_uvar uu___3 wl
                      src.FStarC_Syntax_Syntax.ctx_uvar_range g pfx t uu___4
                      src.FStarC_Syntax_Syntax.ctx_uvar_meta in
                  match uu___2 with
                  | (uu___3, src', wl1) ->
                      ((let uu___5 = f src' in
                        set_uvar env src
                          (FStar_Pervasives_Native.Some
                             FStarC_Syntax_Syntax.Already_checked) uu___5);
                       wl1) in
                let bs1 =
                  FStarC_Compiler_List.filter
                    (fun uu___2 ->
                       match uu___2 with
                       | { FStarC_Syntax_Syntax.binder_bv = bv1;
                           FStarC_Syntax_Syntax.binder_qual = uu___3;
                           FStarC_Syntax_Syntax.binder_positivity = uu___4;
                           FStarC_Syntax_Syntax.binder_attrs = uu___5;_} ->
                           (FStarC_Compiler_List.existsb
                              (fun uu___6 ->
                                 match uu___6 with
                                 | { FStarC_Syntax_Syntax.binder_bv = bv2;
                                     FStarC_Syntax_Syntax.binder_qual =
                                       uu___7;
                                     FStarC_Syntax_Syntax.binder_positivity =
                                       uu___8;
                                     FStarC_Syntax_Syntax.binder_attrs =
                                       uu___9;_}
                                     -> FStarC_Syntax_Syntax.bv_eq bv1 bv2)
                              src.FStarC_Syntax_Syntax.ctx_uvar_binders)
                             &&
                             (let uu___6 =
                                FStarC_Compiler_List.existsb
                                  (fun uu___7 ->
                                     match uu___7 with
                                     | {
                                         FStarC_Syntax_Syntax.binder_bv = bv2;
                                         FStarC_Syntax_Syntax.binder_qual =
                                           uu___8;
                                         FStarC_Syntax_Syntax.binder_positivity
                                           = uu___9;
                                         FStarC_Syntax_Syntax.binder_attrs =
                                           uu___10;_}
                                         ->
                                         FStarC_Syntax_Syntax.bv_eq bv1 bv2)
                                  pfx in
                              Prims.op_Negation uu___6)) bs in
                if (FStarC_Compiler_List.length bs1) = Prims.int_zero
                then
                  let uu___2 = FStarC_Syntax_Util.ctx_uvar_typ src in
                  aux uu___2 (fun src' -> src')
                else
                  (let uu___3 =
                     let t = FStarC_Syntax_Util.ctx_uvar_typ src in
                     let uu___4 = FStarC_Syntax_Syntax.mk_Total t in
                     FStarC_Syntax_Util.arrow bs1 uu___4 in
                   aux uu___3
                     (fun src' ->
                        let uu___4 =
                          let uu___5 =
                            FStarC_Syntax_Syntax.binders_to_names bs1 in
                          FStarC_Compiler_List.map
                            FStarC_Syntax_Syntax.as_arg uu___5 in
                        FStarC_Syntax_Syntax.mk_Tm_app src' uu___4
                          src.FStarC_Syntax_Syntax.ctx_uvar_range))
let restrict_all_uvars :
  'uuuuu .
    'uuuuu ->
      FStarC_Syntax_Syntax.ctx_uvar ->
        FStarC_Syntax_Syntax.binders ->
          FStarC_Syntax_Syntax.ctx_uvar Prims.list -> worklist -> worklist
  =
  fun env ->
    fun tgt ->
      fun bs ->
        fun sources ->
          fun wl ->
            match bs with
            | [] ->
                let ctx_tgt =
                  binders_as_bv_set tgt.FStarC_Syntax_Syntax.ctx_uvar_binders in
                FStarC_Compiler_List.fold_right
                  (fun src ->
                     fun wl1 ->
                       let ctx_src =
                         binders_as_bv_set
                           src.FStarC_Syntax_Syntax.ctx_uvar_binders in
                       let uu___ =
                         FStarC_Class_Setlike.subset ()
                           (Obj.magic
                              (FStarC_Compiler_FlatSet.setlike_flat_set
                                 FStarC_Syntax_Syntax.ord_bv))
                           (Obj.magic ctx_src) (Obj.magic ctx_tgt) in
                       if uu___ then wl1 else restrict_ctx env tgt [] src wl1)
                  sources wl
            | uu___ ->
                FStarC_Compiler_List.fold_right (restrict_ctx env tgt bs)
                  sources wl
let (intersect_binders :
  FStarC_Syntax_Syntax.gamma ->
    FStarC_Syntax_Syntax.binders ->
      FStarC_Syntax_Syntax.binders -> FStarC_Syntax_Syntax.binders)
  =
  fun g ->
    fun v1 ->
      fun v2 ->
        let as_set v =
          let uu___ =
            Obj.magic
              (FStarC_Class_Setlike.empty ()
                 (Obj.magic
                    (FStarC_Compiler_RBSet.setlike_rbset
                       FStarC_Syntax_Syntax.ord_bv)) ()) in
          FStarC_Compiler_List.fold_left
            (fun uu___2 ->
               fun uu___1 ->
                 (fun out ->
                    fun x ->
                      Obj.magic
                        (FStarC_Class_Setlike.add ()
                           (Obj.magic
                              (FStarC_Compiler_RBSet.setlike_rbset
                                 FStarC_Syntax_Syntax.ord_bv))
                           x.FStarC_Syntax_Syntax.binder_bv (Obj.magic out)))
                   uu___2 uu___1) uu___ v in
        let v1_set = as_set v1 in
        let ctx_binders =
          let uu___ =
            Obj.magic
              (FStarC_Class_Setlike.empty ()
                 (Obj.magic
                    (FStarC_Compiler_FlatSet.setlike_flat_set
                       FStarC_Syntax_Syntax.ord_bv)) ()) in
          FStarC_Compiler_List.fold_left
            (fun uu___2 ->
               fun uu___1 ->
                 (fun out ->
                    fun b ->
                      match b with
                      | FStarC_Syntax_Syntax.Binding_var x ->
                          Obj.magic
                            (Obj.repr
                               (FStarC_Class_Setlike.add ()
                                  (Obj.magic
                                     (FStarC_Compiler_FlatSet.setlike_flat_set
                                        FStarC_Syntax_Syntax.ord_bv)) x
                                  (Obj.magic out)))
                      | uu___1 -> Obj.magic (Obj.repr out)) uu___2 uu___1)
            uu___ g in
        let uu___ =
          FStarC_Compiler_List.fold_left
            (fun uu___1 ->
               fun b ->
                 match uu___1 with
                 | (isect, isect_set) ->
                     let uu___2 =
                       ((b.FStarC_Syntax_Syntax.binder_bv),
                         (b.FStarC_Syntax_Syntax.binder_qual)) in
                     (match uu___2 with
                      | (x, imp) ->
                          let uu___3 =
                            let uu___4 =
                              FStarC_Class_Setlike.mem ()
                                (Obj.magic
                                   (FStarC_Compiler_RBSet.setlike_rbset
                                      FStarC_Syntax_Syntax.ord_bv)) x
                                (Obj.magic v1_set) in
                            Prims.op_Negation uu___4 in
                          if uu___3
                          then (isect, isect_set)
                          else
                            (let fvs =
                               FStarC_Syntax_Free.names
                                 x.FStarC_Syntax_Syntax.sort in
                             let uu___5 =
                               FStarC_Class_Setlike.subset ()
                                 (Obj.magic
                                    (FStarC_Compiler_FlatSet.setlike_flat_set
                                       FStarC_Syntax_Syntax.ord_bv))
                                 (Obj.magic fvs) (Obj.magic isect_set) in
                             if uu___5
                             then
                               let uu___6 =
                                 Obj.magic
                                   (FStarC_Class_Setlike.add ()
                                      (Obj.magic
                                         (FStarC_Compiler_FlatSet.setlike_flat_set
                                            FStarC_Syntax_Syntax.ord_bv)) x
                                      (Obj.magic isect_set)) in
                               ((b :: isect), uu___6)
                             else (isect, isect_set)))) ([], ctx_binders) v2 in
        match uu___ with | (isect, uu___1) -> FStarC_Compiler_List.rev isect
let (binders_eq :
  FStarC_Syntax_Syntax.binder Prims.list ->
    FStarC_Syntax_Syntax.binder Prims.list -> Prims.bool)
  =
  fun v1 ->
    fun v2 ->
      ((FStarC_Compiler_List.length v1) = (FStarC_Compiler_List.length v2))
        &&
        (FStarC_Compiler_List.forall2
           (fun uu___ ->
              fun uu___1 ->
                match (uu___, uu___1) with
                | ({ FStarC_Syntax_Syntax.binder_bv = a;
                     FStarC_Syntax_Syntax.binder_qual = uu___2;
                     FStarC_Syntax_Syntax.binder_positivity = uu___3;
                     FStarC_Syntax_Syntax.binder_attrs = uu___4;_},
                   { FStarC_Syntax_Syntax.binder_bv = b;
                     FStarC_Syntax_Syntax.binder_qual = uu___5;
                     FStarC_Syntax_Syntax.binder_positivity = uu___6;
                     FStarC_Syntax_Syntax.binder_attrs = uu___7;_})
                    -> FStarC_Syntax_Syntax.bv_eq a b) v1 v2)
let (name_exists_in_binders :
  FStarC_Syntax_Syntax.bv ->
    FStarC_Syntax_Syntax.binder Prims.list -> Prims.bool)
  =
  fun x ->
    fun bs ->
      FStarC_Compiler_Util.for_some
        (fun uu___ ->
           match uu___ with
           | { FStarC_Syntax_Syntax.binder_bv = y;
               FStarC_Syntax_Syntax.binder_qual = uu___1;
               FStarC_Syntax_Syntax.binder_positivity = uu___2;
               FStarC_Syntax_Syntax.binder_attrs = uu___3;_} ->
               FStarC_Syntax_Syntax.bv_eq x y) bs
let (pat_vars :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.binder Prims.list ->
      (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.aqual) Prims.list ->
        FStarC_Syntax_Syntax.binders FStar_Pervasives_Native.option)
  =
  fun env ->
    fun ctx ->
      fun args ->
        let rec aux seen args1 =
          match args1 with
          | [] ->
              FStar_Pervasives_Native.Some (FStarC_Compiler_List.rev seen)
          | (arg, i)::args2 ->
              let hd = sn env arg in
              (match hd.FStarC_Syntax_Syntax.n with
               | FStarC_Syntax_Syntax.Tm_name a ->
                   let uu___ =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx) in
                   if uu___
                   then FStar_Pervasives_Native.None
                   else
                     (let uu___2 =
                        FStarC_Syntax_Util.bqual_and_attrs_of_aqual i in
                      match uu___2 with
                      | (bq, attrs) ->
                          let uu___3 =
                            FStarC_Syntax_Util.parse_positivity_attributes
                              attrs in
                          (match uu___3 with
                           | (pq, attrs1) ->
                               let uu___4 =
                                 let uu___5 =
                                   FStarC_Syntax_Syntax.mk_binder_with_attrs
                                     a bq pq attrs1 in
                                 uu___5 :: seen in
                               aux uu___4 args2))
               | uu___ -> FStar_Pervasives_Native.None) in
        aux [] args
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | MisMatch (d1, d2) ->
        let uu___1 =
          FStarC_Class_Show.show
            (FStarC_Class_Show.show_tuple2
               (FStarC_Class_Show.show_option
                  FStarC_Syntax_Syntax.showable_delta_depth)
               (FStarC_Class_Show.show_option
                  FStarC_Syntax_Syntax.showable_delta_depth)) (d1, d2) in
        Prims.strcat "MisMatch " uu___1
    | HeadMatch u ->
        let uu___1 = FStarC_Compiler_Util.string_of_bool u in
        Prims.strcat "HeadMatch " uu___1
    | FullMatch -> "FullMatch"
let (showable_match_result : match_result FStarC_Class_Show.showable) =
  { FStarC_Class_Show.show = string_of_match_result }
let (head_match : match_result -> match_result) =
  fun uu___ ->
    match uu___ with
    | MisMatch (i, j) -> MisMatch (i, j)
    | HeadMatch (true) -> HeadMatch true
    | uu___1 -> HeadMatch false
let (universe_has_max :
  FStarC_TypeChecker_Env.env -> FStarC_Syntax_Syntax.universe -> Prims.bool)
  =
  fun env ->
    fun u ->
      let u1 = FStarC_TypeChecker_Normalize.normalize_universe env u in
      match u1 with
      | FStarC_Syntax_Syntax.U_max uu___ -> true
      | uu___ -> false
let rec (head_matches :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term -> match_result)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let t11 = FStarC_Syntax_Util.unmeta t1 in
        let t21 = FStarC_Syntax_Util.unmeta t2 in
        (let uu___1 = FStarC_Compiler_Effect.op_Bang dbg_RelDelta in
         if uu___1
         then
           ((let uu___3 =
               FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t11 in
             let uu___4 =
               FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t21 in
             FStarC_Compiler_Util.print2 "head_matches %s %s\n" uu___3 uu___4);
            (let uu___4 =
               FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term
                 t11 in
             let uu___5 =
               FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term
                 t21 in
             FStarC_Compiler_Util.print2 "             %s  -- %s\n" uu___4
               uu___5))
         else ());
        (match ((t11.FStarC_Syntax_Syntax.n), (t21.FStarC_Syntax_Syntax.n))
         with
         | (FStarC_Syntax_Syntax.Tm_lazy
            { FStarC_Syntax_Syntax.blob = uu___1;
              FStarC_Syntax_Syntax.lkind =
                FStarC_Syntax_Syntax.Lazy_embedding uu___2;
              FStarC_Syntax_Syntax.ltyp = uu___3;
              FStarC_Syntax_Syntax.rng = uu___4;_},
            uu___5) ->
             let uu___6 = FStarC_Syntax_Util.unlazy t11 in
             head_matches env uu___6 t21
         | (uu___1, FStarC_Syntax_Syntax.Tm_lazy
            { FStarC_Syntax_Syntax.blob = uu___2;
              FStarC_Syntax_Syntax.lkind =
                FStarC_Syntax_Syntax.Lazy_embedding uu___3;
              FStarC_Syntax_Syntax.ltyp = uu___4;
              FStarC_Syntax_Syntax.rng = uu___5;_})
             ->
             let uu___6 = FStarC_Syntax_Util.unlazy t21 in
             head_matches env t11 uu___6
         | (FStarC_Syntax_Syntax.Tm_lazy li1, FStarC_Syntax_Syntax.Tm_lazy
            li2) ->
             let uu___1 =
               FStarC_Class_Deq.op_Equals_Question
                 FStarC_Syntax_Syntax.deq_lazy_kind
                 li1.FStarC_Syntax_Syntax.lkind
                 li2.FStarC_Syntax_Syntax.lkind in
             if uu___1
             then HeadMatch false
             else
               MisMatch
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
         | (FStarC_Syntax_Syntax.Tm_name x, FStarC_Syntax_Syntax.Tm_name y)
             ->
             let uu___1 = FStarC_Syntax_Syntax.bv_eq x y in
             if uu___1
             then FullMatch
             else
               MisMatch
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
         | (FStarC_Syntax_Syntax.Tm_fvar f, FStarC_Syntax_Syntax.Tm_fvar g)
             ->
             let uu___1 = FStarC_Syntax_Syntax.fv_eq f g in
             if uu___1
             then FullMatch
             else
               (let uu___3 =
                  let uu___4 =
                    let uu___5 = FStarC_TypeChecker_Env.fv_delta_depth env f in
                    FStar_Pervasives_Native.Some uu___5 in
                  let uu___5 =
                    let uu___6 = FStarC_TypeChecker_Env.fv_delta_depth env g in
                    FStar_Pervasives_Native.Some uu___6 in
                  (uu___4, uu___5) in
                MisMatch uu___3)
         | (FStarC_Syntax_Syntax.Tm_uinst (f, uu___1),
            FStarC_Syntax_Syntax.Tm_uinst (g, uu___2)) ->
             let uu___3 = head_matches env f g in head_match uu___3
         | (FStarC_Syntax_Syntax.Tm_constant (FStarC_Const.Const_reify
            uu___1), FStarC_Syntax_Syntax.Tm_constant
            (FStarC_Const.Const_reify uu___2)) -> FullMatch
         | (FStarC_Syntax_Syntax.Tm_constant (FStarC_Const.Const_reify
            uu___1), uu___2) -> HeadMatch true
         | (uu___1, FStarC_Syntax_Syntax.Tm_constant
            (FStarC_Const.Const_reify uu___2)) -> HeadMatch true
         | (FStarC_Syntax_Syntax.Tm_constant c,
            FStarC_Syntax_Syntax.Tm_constant d) ->
             let uu___1 = FStarC_Const.eq_const c d in
             if uu___1
             then FullMatch
             else
               MisMatch
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
         | (FStarC_Syntax_Syntax.Tm_uvar (uv, uu___1),
            FStarC_Syntax_Syntax.Tm_uvar (uv', uu___2)) ->
             let uu___3 =
               FStarC_Syntax_Unionfind.equiv
                 uv.FStarC_Syntax_Syntax.ctx_uvar_head
                 uv'.FStarC_Syntax_Syntax.ctx_uvar_head in
             if uu___3
             then FullMatch
             else
               MisMatch
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
         | (FStarC_Syntax_Syntax.Tm_refine
            { FStarC_Syntax_Syntax.b = x;
              FStarC_Syntax_Syntax.phi = uu___1;_},
            FStarC_Syntax_Syntax.Tm_refine
            { FStarC_Syntax_Syntax.b = y;
              FStarC_Syntax_Syntax.phi = uu___2;_})
             ->
             let uu___3 =
               head_matches env x.FStarC_Syntax_Syntax.sort
                 y.FStarC_Syntax_Syntax.sort in
             head_match uu___3
         | (FStarC_Syntax_Syntax.Tm_refine
            { FStarC_Syntax_Syntax.b = x;
              FStarC_Syntax_Syntax.phi = uu___1;_},
            uu___2) ->
             let uu___3 = head_matches env x.FStarC_Syntax_Syntax.sort t21 in
             head_match uu___3
         | (uu___1, FStarC_Syntax_Syntax.Tm_refine
            { FStarC_Syntax_Syntax.b = x;
              FStarC_Syntax_Syntax.phi = uu___2;_})
             ->
             let uu___3 = head_matches env t11 x.FStarC_Syntax_Syntax.sort in
             head_match uu___3
         | (FStarC_Syntax_Syntax.Tm_type uu___1, FStarC_Syntax_Syntax.Tm_type
            uu___2) -> HeadMatch false
         | (FStarC_Syntax_Syntax.Tm_arrow uu___1,
            FStarC_Syntax_Syntax.Tm_arrow uu___2) -> HeadMatch false
         | (FStarC_Syntax_Syntax.Tm_app
            { FStarC_Syntax_Syntax.hd = head;
              FStarC_Syntax_Syntax.args = uu___1;_},
            FStarC_Syntax_Syntax.Tm_app
            { FStarC_Syntax_Syntax.hd = head';
              FStarC_Syntax_Syntax.args = uu___2;_})
             -> let uu___3 = head_matches env head head' in head_match uu___3
         | (FStarC_Syntax_Syntax.Tm_app
            { FStarC_Syntax_Syntax.hd = head;
              FStarC_Syntax_Syntax.args = uu___1;_},
            uu___2) ->
             let uu___3 = head_matches env head t21 in head_match uu___3
         | (uu___1, FStarC_Syntax_Syntax.Tm_app
            { FStarC_Syntax_Syntax.hd = head;
              FStarC_Syntax_Syntax.args = uu___2;_})
             -> let uu___3 = head_matches env t11 head in head_match uu___3
         | (FStarC_Syntax_Syntax.Tm_let uu___1, FStarC_Syntax_Syntax.Tm_let
            uu___2) -> HeadMatch true
         | (FStarC_Syntax_Syntax.Tm_match uu___1,
            FStarC_Syntax_Syntax.Tm_match uu___2) -> HeadMatch true
         | (FStarC_Syntax_Syntax.Tm_quoted uu___1,
            FStarC_Syntax_Syntax.Tm_quoted uu___2) -> HeadMatch true
         | (FStarC_Syntax_Syntax.Tm_abs uu___1, FStarC_Syntax_Syntax.Tm_abs
            uu___2) -> HeadMatch true
         | uu___1 ->
             let maybe_dd t =
               let uu___2 =
                 let uu___3 = FStarC_Syntax_Subst.compress t in
                 uu___3.FStarC_Syntax_Syntax.n in
               match uu___2 with
               | FStarC_Syntax_Syntax.Tm_unknown ->
                   FStar_Pervasives_Native.None
               | FStarC_Syntax_Syntax.Tm_bvar uu___3 ->
                   FStar_Pervasives_Native.None
               | FStarC_Syntax_Syntax.Tm_name uu___3 ->
                   FStar_Pervasives_Native.None
               | FStarC_Syntax_Syntax.Tm_uvar uu___3 ->
                   FStar_Pervasives_Native.None
               | FStarC_Syntax_Syntax.Tm_let uu___3 ->
                   FStar_Pervasives_Native.None
               | FStarC_Syntax_Syntax.Tm_match uu___3 ->
                   FStar_Pervasives_Native.None
               | uu___3 ->
                   let uu___4 =
                     FStarC_TypeChecker_Env.delta_depth_of_term env t in
                   FStar_Pervasives_Native.Some uu___4 in
             let uu___2 =
               let uu___3 = maybe_dd t11 in
               let uu___4 = maybe_dd t21 in (uu___3, uu___4) in
             MisMatch uu___2)
let (head_matches_delta :
  FStarC_TypeChecker_Env.env ->
    Prims.bool ->
      Prims.bool ->
        FStarC_Syntax_Syntax.typ ->
          FStarC_Syntax_Syntax.typ ->
            (match_result * (FStarC_Syntax_Syntax.typ *
              FStarC_Syntax_Syntax.typ) FStar_Pervasives_Native.option))
  =
  fun env ->
    fun logical ->
      fun smt_ok ->
        fun t1 ->
          fun t2 ->
            let base_steps =
              FStarC_Compiler_List.op_At
                (if logical
                 then
                   [FStarC_TypeChecker_Env.DontUnfoldAttr
                      [FStarC_Parser_Const.tac_opaque_attr]]
                 else [])
                [FStarC_TypeChecker_Env.Primops;
                FStarC_TypeChecker_Env.Weak;
                FStarC_TypeChecker_Env.HNF] in
            let maybe_inline t =
              let head =
                let uu___ = unrefine env t in
                FStarC_Syntax_Util.head_of uu___ in
              (let uu___1 = FStarC_Compiler_Effect.op_Bang dbg_RelDelta in
               if uu___1
               then
                 let uu___2 =
                   FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
                 let uu___3 =
                   FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                     head in
                 FStarC_Compiler_Util.print2 "Head of %s is %s\n" uu___2
                   uu___3
               else ());
              (let uu___1 =
                 let uu___2 = FStarC_Syntax_Util.un_uinst head in
                 uu___2.FStarC_Syntax_Syntax.n in
               match uu___1 with
               | FStarC_Syntax_Syntax.Tm_fvar fv ->
                   let uu___2 =
                     FStarC_TypeChecker_Env.lookup_definition
                       [FStarC_TypeChecker_Env.Unfold
                          FStarC_Syntax_Syntax.delta_constant;
                       FStarC_TypeChecker_Env.Eager_unfolding_only] env
                       (fv.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v in
                   (match uu___2 with
                    | FStar_Pervasives_Native.None ->
                        ((let uu___4 =
                            FStarC_Compiler_Effect.op_Bang dbg_RelDelta in
                          if uu___4
                          then
                            let uu___5 =
                              FStarC_Class_Show.show
                                FStarC_Syntax_Print.showable_term head in
                            FStarC_Compiler_Util.print1
                              "No definition found for %s\n" uu___5
                          else ());
                         FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some uu___3 ->
                        let basic_steps =
                          FStarC_Compiler_List.op_At
                            (if logical
                             then
                               [FStarC_TypeChecker_Env.DontUnfoldAttr
                                  [FStarC_Parser_Const.tac_opaque_attr]]
                             else [])
                            [FStarC_TypeChecker_Env.UnfoldUntil
                               FStarC_Syntax_Syntax.delta_constant;
                            FStarC_TypeChecker_Env.Weak;
                            FStarC_TypeChecker_Env.HNF;
                            FStarC_TypeChecker_Env.Primops;
                            FStarC_TypeChecker_Env.Beta;
                            FStarC_TypeChecker_Env.Eager_unfolding;
                            FStarC_TypeChecker_Env.Iota] in
                        let steps =
                          if smt_ok
                          then basic_steps
                          else
                            (FStarC_TypeChecker_Env.Exclude
                               FStarC_TypeChecker_Env.Zeta)
                            :: basic_steps in
                        let t' =
                          norm_with_steps
                            "FStarC.TypeChecker.Rel.norm_with_steps.1" steps
                            env t in
                        let uu___4 =
                          let uu___5 =
                            FStarC_TypeChecker_TermEqAndSimplify.eq_tm env t
                              t' in
                          uu___5 = FStarC_TypeChecker_TermEqAndSimplify.Equal in
                        if uu___4
                        then FStar_Pervasives_Native.None
                        else
                          ((let uu___7 =
                              FStarC_Compiler_Effect.op_Bang dbg_RelDelta in
                            if uu___7
                            then
                              let uu___8 =
                                FStarC_Class_Show.show
                                  FStarC_Syntax_Print.showable_term t in
                              let uu___9 =
                                FStarC_Class_Show.show
                                  FStarC_Syntax_Print.showable_term t' in
                              FStarC_Compiler_Util.print2
                                "Inlined %s to %s\n" uu___8 uu___9
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
              let head =
                let uu___ = FStarC_Syntax_Util.head_and_args t in
                FStar_Pervasives_Native.fst uu___ in
              let head' =
                let uu___ = FStarC_Syntax_Util.head_and_args t' in
                FStar_Pervasives_Native.fst uu___ in
              let uu___ = FStarC_Syntax_Util.term_eq head head' in
              Prims.op_Negation uu___ in
            let rec aux retry n_delta t11 t21 =
              let r = head_matches env t11 t21 in
              (let uu___1 = FStarC_Compiler_Effect.op_Bang dbg_RelDelta in
               if uu___1
               then
                 let uu___2 =
                   FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                     t11 in
                 let uu___3 =
                   FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                     t21 in
                 let uu___4 = string_of_match_result r in
                 FStarC_Compiler_Util.print3 "head_matches (%s, %s) = %s\n"
                   uu___2 uu___3 uu___4
               else ());
              (let reduce_one_and_try_again d1 d2 =
                 let d1_greater_than_d2 =
                   FStarC_TypeChecker_Common.delta_depth_greater_than d1 d2 in
                 let uu___1 =
                   if d1_greater_than_d2
                   then
                     let t1' =
                       normalize_refinement
                         ((FStarC_TypeChecker_Env.UnfoldUntil d2) ::
                         base_steps) env t11 in
                     let uu___2 = made_progress t11 t1' in (t1', t21, uu___2)
                   else
                     (let t2' =
                        normalize_refinement
                          ((FStarC_TypeChecker_Env.UnfoldUntil d1) ::
                          base_steps) env t21 in
                      let uu___3 = made_progress t21 t2' in
                      (t11, t2', uu___3)) in
                 match uu___1 with
                 | (t12, t22, made_progress1) ->
                     if made_progress1
                     then aux retry (n_delta + Prims.int_one) t12 t22
                     else fail n_delta r t12 t22 in
               let reduce_both_and_try_again d r1 =
                 let uu___1 = FStarC_TypeChecker_Common.decr_delta_depth d in
                 match uu___1 with
                 | FStar_Pervasives_Native.None -> fail n_delta r1 t11 t21
                 | FStar_Pervasives_Native.Some d1 ->
                     let t1' =
                       normalize_refinement
                         ((FStarC_TypeChecker_Env.UnfoldUntil d1) ::
                         base_steps) env t11 in
                     let t2' =
                       normalize_refinement
                         ((FStarC_TypeChecker_Env.UnfoldUntil d1) ::
                         base_steps) env t21 in
                     let uu___2 =
                       (made_progress t11 t1') && (made_progress t21 t2') in
                     if uu___2
                     then aux retry (n_delta + Prims.int_one) t1' t2'
                     else fail n_delta r1 t11 t21 in
               match r with
               | MisMatch
                   (FStar_Pervasives_Native.Some
                    (FStarC_Syntax_Syntax.Delta_equational_at_level i),
                    FStar_Pervasives_Native.Some
                    (FStarC_Syntax_Syntax.Delta_equational_at_level j))
                   when
                   ((i > Prims.int_zero) || (j > Prims.int_zero)) && (i <> j)
                   ->
                   reduce_one_and_try_again
                     (FStarC_Syntax_Syntax.Delta_equational_at_level i)
                     (FStarC_Syntax_Syntax.Delta_equational_at_level j)
               | MisMatch
                   (FStar_Pervasives_Native.Some
                    (FStarC_Syntax_Syntax.Delta_equational_at_level uu___1),
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
                    (FStarC_Syntax_Syntax.Delta_equational_at_level uu___2))
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
            (let uu___1 = FStarC_Compiler_Effect.op_Bang dbg_RelDelta in
             if uu___1
             then
               let uu___2 =
                 FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t1 in
               let uu___3 =
                 FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t2 in
               let uu___4 =
                 FStarC_Class_Show.show
                   (FStarC_Class_Show.show_tuple2 showable_match_result
                      (FStarC_Class_Show.show_option
                         (FStarC_Class_Show.show_tuple2
                            FStarC_Syntax_Print.showable_term
                            FStarC_Syntax_Print.showable_term))) r in
               FStarC_Compiler_Util.print3
                 "head_matches_delta (%s, %s) = %s\n" uu___2 uu___3 uu___4
             else ());
            r
let (kind_type :
  FStarC_Syntax_Syntax.binders ->
    FStarC_Compiler_Range_Type.range -> FStarC_Syntax_Syntax.typ)
  =
  fun binders ->
    fun r ->
      let uu___ = FStarC_Syntax_Util.type_u () in
      FStar_Pervasives_Native.fst uu___
let (rank_t_num : FStarC_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___ ->
    match uu___ with
    | FStarC_TypeChecker_Common.Rigid_rigid -> Prims.int_zero
    | FStarC_TypeChecker_Common.Flex_rigid_eq -> Prims.int_one
    | FStarC_TypeChecker_Common.Flex_flex_pattern_eq -> (Prims.of_int (2))
    | FStarC_TypeChecker_Common.Flex_rigid -> (Prims.of_int (3))
    | FStarC_TypeChecker_Common.Rigid_flex -> (Prims.of_int (4))
    | FStarC_TypeChecker_Common.Flex_flex -> (Prims.of_int (5))
let (rank_leq :
  FStarC_TypeChecker_Common.rank_t ->
    FStarC_TypeChecker_Common.rank_t -> Prims.bool)
  = fun r1 -> fun r2 -> (rank_t_num r1) <= (rank_t_num r2)
let (rank_less_than :
  FStarC_TypeChecker_Common.rank_t ->
    FStarC_TypeChecker_Common.rank_t -> Prims.bool)
  = fun r1 -> fun r2 -> (r1 <> r2) && ((rank_t_num r1) <= (rank_t_num r2))
let (compress_tprob :
  worklist ->
    FStarC_Syntax_Syntax.typ FStarC_TypeChecker_Common.problem ->
      FStarC_Syntax_Syntax.term FStarC_TypeChecker_Common.problem)
  =
  fun wl ->
    fun p ->
      let env = p_env wl (FStarC_TypeChecker_Common.TProb p) in
      let uu___ = whnf env p.FStarC_TypeChecker_Common.lhs in
      let uu___1 = whnf env p.FStarC_TypeChecker_Common.rhs in
      {
        FStarC_TypeChecker_Common.pid = (p.FStarC_TypeChecker_Common.pid);
        FStarC_TypeChecker_Common.lhs = uu___;
        FStarC_TypeChecker_Common.relation =
          (p.FStarC_TypeChecker_Common.relation);
        FStarC_TypeChecker_Common.rhs = uu___1;
        FStarC_TypeChecker_Common.element =
          (p.FStarC_TypeChecker_Common.element);
        FStarC_TypeChecker_Common.logical_guard =
          (p.FStarC_TypeChecker_Common.logical_guard);
        FStarC_TypeChecker_Common.logical_guard_uvar =
          (p.FStarC_TypeChecker_Common.logical_guard_uvar);
        FStarC_TypeChecker_Common.reason =
          (p.FStarC_TypeChecker_Common.reason);
        FStarC_TypeChecker_Common.loc = (p.FStarC_TypeChecker_Common.loc);
        FStarC_TypeChecker_Common.rank = (p.FStarC_TypeChecker_Common.rank);
        FStarC_TypeChecker_Common.logical =
          (p.FStarC_TypeChecker_Common.logical)
      }
let (compress_cprob :
  worklist ->
    FStarC_Syntax_Syntax.comp FStarC_TypeChecker_Common.problem ->
      FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax
        FStarC_TypeChecker_Common.problem)
  =
  fun wl ->
    fun p ->
      let whnf_c env c =
        match c.FStarC_Syntax_Syntax.n with
        | FStarC_Syntax_Syntax.Total ty ->
            let uu___ = whnf env ty in FStarC_Syntax_Syntax.mk_Total uu___
        | uu___ -> c in
      let env = p_env wl (FStarC_TypeChecker_Common.CProb p) in
      let uu___ = whnf_c env p.FStarC_TypeChecker_Common.lhs in
      let uu___1 = whnf_c env p.FStarC_TypeChecker_Common.rhs in
      {
        FStarC_TypeChecker_Common.pid = (p.FStarC_TypeChecker_Common.pid);
        FStarC_TypeChecker_Common.lhs = uu___;
        FStarC_TypeChecker_Common.relation =
          (p.FStarC_TypeChecker_Common.relation);
        FStarC_TypeChecker_Common.rhs = uu___1;
        FStarC_TypeChecker_Common.element =
          (p.FStarC_TypeChecker_Common.element);
        FStarC_TypeChecker_Common.logical_guard =
          (p.FStarC_TypeChecker_Common.logical_guard);
        FStarC_TypeChecker_Common.logical_guard_uvar =
          (p.FStarC_TypeChecker_Common.logical_guard_uvar);
        FStarC_TypeChecker_Common.reason =
          (p.FStarC_TypeChecker_Common.reason);
        FStarC_TypeChecker_Common.loc = (p.FStarC_TypeChecker_Common.loc);
        FStarC_TypeChecker_Common.rank = (p.FStarC_TypeChecker_Common.rank);
        FStarC_TypeChecker_Common.logical =
          (p.FStarC_TypeChecker_Common.logical)
      }
let (compress_prob :
  worklist ->
    FStarC_TypeChecker_Common.prob -> FStarC_TypeChecker_Common.prob)
  =
  fun wl ->
    fun p ->
      match p with
      | FStarC_TypeChecker_Common.TProb p1 ->
          let uu___ = compress_tprob wl p1 in
          FStarC_TypeChecker_Common.TProb uu___
      | FStarC_TypeChecker_Common.CProb p1 ->
          let uu___ = compress_cprob wl p1 in
          FStarC_TypeChecker_Common.CProb uu___
let (rank :
  worklist ->
    FStarC_TypeChecker_Common.prob ->
      (FStarC_TypeChecker_Common.rank_t * FStarC_TypeChecker_Common.prob))
  =
  fun wl ->
    fun pr ->
      let prob = let uu___ = compress_prob wl pr in maybe_invert_p uu___ in
      match prob with
      | FStarC_TypeChecker_Common.TProb tp ->
          let uu___ =
            FStarC_Syntax_Util.head_and_args tp.FStarC_TypeChecker_Common.lhs in
          (match uu___ with
           | (lh, lhs_args) ->
               let uu___1 =
                 FStarC_Syntax_Util.head_and_args
                   tp.FStarC_TypeChecker_Common.rhs in
               (match uu___1 with
                | (rh, rhs_args) ->
                    let uu___2 =
                      match ((lh.FStarC_Syntax_Syntax.n),
                              (rh.FStarC_Syntax_Syntax.n))
                      with
                      | (FStarC_Syntax_Syntax.Tm_uvar uu___3,
                         FStarC_Syntax_Syntax.Tm_uvar uu___4) ->
                          (match (lhs_args, rhs_args) with
                           | ([], []) when
                               tp.FStarC_TypeChecker_Common.relation =
                                 FStarC_TypeChecker_Common.EQ
                               ->
                               (FStarC_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu___5 ->
                               (FStarC_TypeChecker_Common.Flex_flex, tp))
                      | (FStarC_Syntax_Syntax.Tm_uvar uu___3, uu___4) when
                          tp.FStarC_TypeChecker_Common.relation =
                            FStarC_TypeChecker_Common.EQ
                          -> (FStarC_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu___3, FStarC_Syntax_Syntax.Tm_uvar uu___4) when
                          tp.FStarC_TypeChecker_Common.relation =
                            FStarC_TypeChecker_Common.EQ
                          -> (FStarC_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStarC_Syntax_Syntax.Tm_uvar uu___3,
                         FStarC_Syntax_Syntax.Tm_arrow uu___4) ->
                          (FStarC_TypeChecker_Common.Flex_rigid_eq,
                            {
                              FStarC_TypeChecker_Common.pid =
                                (tp.FStarC_TypeChecker_Common.pid);
                              FStarC_TypeChecker_Common.lhs =
                                (tp.FStarC_TypeChecker_Common.lhs);
                              FStarC_TypeChecker_Common.relation =
                                FStarC_TypeChecker_Common.EQ;
                              FStarC_TypeChecker_Common.rhs =
                                (tp.FStarC_TypeChecker_Common.rhs);
                              FStarC_TypeChecker_Common.element =
                                (tp.FStarC_TypeChecker_Common.element);
                              FStarC_TypeChecker_Common.logical_guard =
                                (tp.FStarC_TypeChecker_Common.logical_guard);
                              FStarC_TypeChecker_Common.logical_guard_uvar =
                                (tp.FStarC_TypeChecker_Common.logical_guard_uvar);
                              FStarC_TypeChecker_Common.reason =
                                (tp.FStarC_TypeChecker_Common.reason);
                              FStarC_TypeChecker_Common.loc =
                                (tp.FStarC_TypeChecker_Common.loc);
                              FStarC_TypeChecker_Common.rank =
                                (tp.FStarC_TypeChecker_Common.rank);
                              FStarC_TypeChecker_Common.logical =
                                (tp.FStarC_TypeChecker_Common.logical)
                            })
                      | (FStarC_Syntax_Syntax.Tm_uvar uu___3,
                         FStarC_Syntax_Syntax.Tm_type uu___4) ->
                          (FStarC_TypeChecker_Common.Flex_rigid_eq,
                            {
                              FStarC_TypeChecker_Common.pid =
                                (tp.FStarC_TypeChecker_Common.pid);
                              FStarC_TypeChecker_Common.lhs =
                                (tp.FStarC_TypeChecker_Common.lhs);
                              FStarC_TypeChecker_Common.relation =
                                FStarC_TypeChecker_Common.EQ;
                              FStarC_TypeChecker_Common.rhs =
                                (tp.FStarC_TypeChecker_Common.rhs);
                              FStarC_TypeChecker_Common.element =
                                (tp.FStarC_TypeChecker_Common.element);
                              FStarC_TypeChecker_Common.logical_guard =
                                (tp.FStarC_TypeChecker_Common.logical_guard);
                              FStarC_TypeChecker_Common.logical_guard_uvar =
                                (tp.FStarC_TypeChecker_Common.logical_guard_uvar);
                              FStarC_TypeChecker_Common.reason =
                                (tp.FStarC_TypeChecker_Common.reason);
                              FStarC_TypeChecker_Common.loc =
                                (tp.FStarC_TypeChecker_Common.loc);
                              FStarC_TypeChecker_Common.rank =
                                (tp.FStarC_TypeChecker_Common.rank);
                              FStarC_TypeChecker_Common.logical =
                                (tp.FStarC_TypeChecker_Common.logical)
                            })
                      | (FStarC_Syntax_Syntax.Tm_type uu___3,
                         FStarC_Syntax_Syntax.Tm_uvar uu___4) ->
                          (FStarC_TypeChecker_Common.Flex_rigid_eq,
                            {
                              FStarC_TypeChecker_Common.pid =
                                (tp.FStarC_TypeChecker_Common.pid);
                              FStarC_TypeChecker_Common.lhs =
                                (tp.FStarC_TypeChecker_Common.lhs);
                              FStarC_TypeChecker_Common.relation =
                                FStarC_TypeChecker_Common.EQ;
                              FStarC_TypeChecker_Common.rhs =
                                (tp.FStarC_TypeChecker_Common.rhs);
                              FStarC_TypeChecker_Common.element =
                                (tp.FStarC_TypeChecker_Common.element);
                              FStarC_TypeChecker_Common.logical_guard =
                                (tp.FStarC_TypeChecker_Common.logical_guard);
                              FStarC_TypeChecker_Common.logical_guard_uvar =
                                (tp.FStarC_TypeChecker_Common.logical_guard_uvar);
                              FStarC_TypeChecker_Common.reason =
                                (tp.FStarC_TypeChecker_Common.reason);
                              FStarC_TypeChecker_Common.loc =
                                (tp.FStarC_TypeChecker_Common.loc);
                              FStarC_TypeChecker_Common.rank =
                                (tp.FStarC_TypeChecker_Common.rank);
                              FStarC_TypeChecker_Common.logical =
                                (tp.FStarC_TypeChecker_Common.logical)
                            })
                      | (uu___3, FStarC_Syntax_Syntax.Tm_uvar uu___4) ->
                          (FStarC_TypeChecker_Common.Rigid_flex, tp)
                      | (FStarC_Syntax_Syntax.Tm_uvar uu___3, uu___4) ->
                          (FStarC_TypeChecker_Common.Flex_rigid, tp)
                      | (uu___3, FStarC_Syntax_Syntax.Tm_uvar uu___4) ->
                          (FStarC_TypeChecker_Common.Rigid_flex, tp)
                      | (uu___3, uu___4) ->
                          (FStarC_TypeChecker_Common.Rigid_rigid, tp) in
                    (match uu___2 with
                     | (rank1, tp1) ->
                         (rank1,
                           (FStarC_TypeChecker_Common.TProb
                              {
                                FStarC_TypeChecker_Common.pid =
                                  (tp1.FStarC_TypeChecker_Common.pid);
                                FStarC_TypeChecker_Common.lhs =
                                  (tp1.FStarC_TypeChecker_Common.lhs);
                                FStarC_TypeChecker_Common.relation =
                                  (tp1.FStarC_TypeChecker_Common.relation);
                                FStarC_TypeChecker_Common.rhs =
                                  (tp1.FStarC_TypeChecker_Common.rhs);
                                FStarC_TypeChecker_Common.element =
                                  (tp1.FStarC_TypeChecker_Common.element);
                                FStarC_TypeChecker_Common.logical_guard =
                                  (tp1.FStarC_TypeChecker_Common.logical_guard);
                                FStarC_TypeChecker_Common.logical_guard_uvar
                                  =
                                  (tp1.FStarC_TypeChecker_Common.logical_guard_uvar);
                                FStarC_TypeChecker_Common.reason =
                                  (tp1.FStarC_TypeChecker_Common.reason);
                                FStarC_TypeChecker_Common.loc =
                                  (tp1.FStarC_TypeChecker_Common.loc);
                                FStarC_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank1);
                                FStarC_TypeChecker_Common.logical =
                                  (tp1.FStarC_TypeChecker_Common.logical)
                              })))))
      | FStarC_TypeChecker_Common.CProb cp ->
          (FStarC_TypeChecker_Common.Rigid_rigid,
            (FStarC_TypeChecker_Common.CProb
               {
                 FStarC_TypeChecker_Common.pid =
                   (cp.FStarC_TypeChecker_Common.pid);
                 FStarC_TypeChecker_Common.lhs =
                   (cp.FStarC_TypeChecker_Common.lhs);
                 FStarC_TypeChecker_Common.relation =
                   (cp.FStarC_TypeChecker_Common.relation);
                 FStarC_TypeChecker_Common.rhs =
                   (cp.FStarC_TypeChecker_Common.rhs);
                 FStarC_TypeChecker_Common.element =
                   (cp.FStarC_TypeChecker_Common.element);
                 FStarC_TypeChecker_Common.logical_guard =
                   (cp.FStarC_TypeChecker_Common.logical_guard);
                 FStarC_TypeChecker_Common.logical_guard_uvar =
                   (cp.FStarC_TypeChecker_Common.logical_guard_uvar);
                 FStarC_TypeChecker_Common.reason =
                   (cp.FStarC_TypeChecker_Common.reason);
                 FStarC_TypeChecker_Common.loc =
                   (cp.FStarC_TypeChecker_Common.loc);
                 FStarC_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStarC_TypeChecker_Common.Rigid_rigid);
                 FStarC_TypeChecker_Common.logical =
                   (cp.FStarC_TypeChecker_Common.logical)
               }))
let (next_prob :
  worklist ->
    (FStarC_TypeChecker_Common.prob * FStarC_TypeChecker_Common.prob
      Prims.list * FStarC_TypeChecker_Common.rank_t)
      FStar_Pervasives_Native.option)
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
               let uu___1 = rank wl hd in
               (match uu___1 with
                | (rank1, hd1) ->
                    if rank_leq rank1 FStarC_TypeChecker_Common.Flex_rigid_eq
                    then
                      (match min with
                       | FStar_Pervasives_Native.None ->
                           FStar_Pervasives_Native.Some
                             (hd1, (FStarC_Compiler_List.op_At out tl),
                               rank1)
                       | FStar_Pervasives_Native.Some m ->
                           FStar_Pervasives_Native.Some
                             (hd1,
                               (FStarC_Compiler_List.op_At out (m :: tl)),
                               rank1))
                    else
                      (let uu___3 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu___4 = FStarC_Compiler_Option.get min_rank in
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
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.binders ->
      FStarC_TypeChecker_Common.prob -> Prims.bool)
  =
  fun tcenv ->
    fun bs ->
      fun p ->
        let flex_will_be_closed t =
          let uu___ = FStarC_Syntax_Util.head_and_args t in
          match uu___ with
          | (hd, uu___1) ->
              let uu___2 =
                let uu___3 = FStarC_Syntax_Subst.compress hd in
                uu___3.FStarC_Syntax_Syntax.n in
              (match uu___2 with
               | FStarC_Syntax_Syntax.Tm_uvar (u, uu___3) ->
                   FStarC_Compiler_Util.for_some
                     (fun uu___4 ->
                        match uu___4 with
                        | { FStarC_Syntax_Syntax.binder_bv = y;
                            FStarC_Syntax_Syntax.binder_qual = uu___5;
                            FStarC_Syntax_Syntax.binder_positivity = uu___6;
                            FStarC_Syntax_Syntax.binder_attrs = uu___7;_} ->
                            FStarC_Compiler_Util.for_some
                              (fun uu___8 ->
                                 match uu___8 with
                                 | { FStarC_Syntax_Syntax.binder_bv = x;
                                     FStarC_Syntax_Syntax.binder_qual =
                                       uu___9;
                                     FStarC_Syntax_Syntax.binder_positivity =
                                       uu___10;
                                     FStarC_Syntax_Syntax.binder_attrs =
                                       uu___11;_}
                                     -> FStarC_Syntax_Syntax.bv_eq x y) bs)
                     u.FStarC_Syntax_Syntax.ctx_uvar_binders
               | uu___3 -> false) in
        let wl = empty_worklist tcenv in
        let uu___ = rank wl p in
        match uu___ with
        | (r, p1) ->
            (match p1 with
             | FStarC_TypeChecker_Common.CProb uu___1 -> true
             | FStarC_TypeChecker_Common.TProb p2 ->
                 (match r with
                  | FStarC_TypeChecker_Common.Rigid_rigid -> true
                  | FStarC_TypeChecker_Common.Flex_rigid_eq -> true
                  | FStarC_TypeChecker_Common.Flex_flex_pattern_eq -> true
                  | FStarC_TypeChecker_Common.Flex_rigid ->
                      flex_will_be_closed p2.FStarC_TypeChecker_Common.lhs
                  | FStarC_TypeChecker_Common.Rigid_flex ->
                      flex_will_be_closed p2.FStarC_TypeChecker_Common.rhs
                  | FStarC_TypeChecker_Common.Flex_flex ->
                      (p2.FStarC_TypeChecker_Common.relation =
                         FStarC_TypeChecker_Common.EQ)
                        &&
                        ((flex_will_be_closed
                            p2.FStarC_TypeChecker_Common.lhs)
                           ||
                           (flex_will_be_closed
                              p2.FStarC_TypeChecker_Common.rhs))))
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
  fun s -> let uu___ = FStarC_Thunk.mkv s in UFailed uu___
let (ufailed_thunk : (unit -> Prims.string) -> univ_eq_sol) =
  fun s -> let uu___ = mklstr s in UFailed uu___
let rec (really_solve_universe_eq :
  Prims.int ->
    worklist ->
      FStarC_Syntax_Syntax.universe ->
        FStarC_Syntax_Syntax.universe -> univ_eq_sol)
  =
  fun pid_orig ->
    fun wl ->
      fun u1 ->
        fun u2 ->
          let u11 =
            FStarC_TypeChecker_Normalize.normalize_universe wl.tcenv u1 in
          let u21 =
            FStarC_TypeChecker_Normalize.normalize_universe wl.tcenv u2 in
          let rec occurs_univ v1 u =
            match u with
            | FStarC_Syntax_Syntax.U_max us ->
                FStarC_Compiler_Util.for_some
                  (fun u3 ->
                     let uu___ = FStarC_Syntax_Util.univ_kernel u3 in
                     match uu___ with
                     | (k, uu___1) ->
                         (match k with
                          | FStarC_Syntax_Syntax.U_unif v2 ->
                              FStarC_Syntax_Unionfind.univ_equiv v1 v2
                          | uu___2 -> false)) us
            | uu___ -> occurs_univ v1 (FStarC_Syntax_Syntax.U_max [u]) in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStarC_Compiler_List.fold_left
                (fun uvs ->
                   fun uv1 ->
                     let uu___ =
                       FStarC_Compiler_List.existsML
                         (fun uv2 -> FStarC_Syntax_Util.eq_univs uv1 uv2) u22 in
                     if uu___ then uv1 :: uvs else uvs) [] u12 in
            let filter =
              FStarC_Compiler_List.filter
                (fun u ->
                   let uu___ =
                     FStarC_Compiler_List.existsML
                       (fun u' -> FStarC_Syntax_Util.eq_univs u u')
                       common_elts in
                   Prims.op_Negation uu___) in
            let uu___ = filter u12 in
            let uu___1 = filter u22 in (uu___, uu___1) in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then ufailed_simple "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStarC_Syntax_Syntax.U_max us1, FStarC_Syntax_Syntax.U_max
                  us2) ->
                   let uu___1 = filter_out_common_univs us1 us2 in
                   (match uu___1 with
                    | (us11, us21) ->
                        if
                          (FStarC_Compiler_List.length us11) =
                            (FStarC_Compiler_List.length us21)
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
                                 FStarC_Class_Show.show
                                   FStarC_Syntax_Print.showable_univ u12 in
                               let uu___5 =
                                 FStarC_Class_Show.show
                                   FStarC_Syntax_Print.showable_univ u22 in
                               FStarC_Compiler_Util.format2
                                 "Unable to unify universes: %s and %s"
                                 uu___4 uu___5))
               | (FStarC_Syntax_Syntax.U_max us, u') ->
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
               | (u', FStarC_Syntax_Syntax.U_max us) ->
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
                        let uu___3 =
                          FStarC_Class_Show.show
                            FStarC_Syntax_Print.showable_univ u12 in
                        let uu___4 =
                          FStarC_Class_Show.show
                            FStarC_Syntax_Print.showable_univ u22 in
                        FStarC_Compiler_Util.format3
                          "Unable to unify universes: %s and %s (%s)" uu___3
                          uu___4 msg)) in
          match (u11, u21) with
          | (FStarC_Syntax_Syntax.U_bvar uu___, uu___1) ->
              let uu___2 =
                let uu___3 =
                  FStarC_Class_Show.show FStarC_Syntax_Print.showable_univ
                    u11 in
                let uu___4 =
                  FStarC_Class_Show.show FStarC_Syntax_Print.showable_univ
                    u21 in
                FStarC_Compiler_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu___3 uu___4 in
              failwith uu___2
          | (FStarC_Syntax_Syntax.U_unknown, uu___) ->
              let uu___1 =
                let uu___2 =
                  FStarC_Class_Show.show FStarC_Syntax_Print.showable_univ
                    u11 in
                let uu___3 =
                  FStarC_Class_Show.show FStarC_Syntax_Print.showable_univ
                    u21 in
                FStarC_Compiler_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu___2 uu___3 in
              failwith uu___1
          | (uu___, FStarC_Syntax_Syntax.U_bvar uu___1) ->
              let uu___2 =
                let uu___3 =
                  FStarC_Class_Show.show FStarC_Syntax_Print.showable_univ
                    u11 in
                let uu___4 =
                  FStarC_Class_Show.show FStarC_Syntax_Print.showable_univ
                    u21 in
                FStarC_Compiler_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu___3 uu___4 in
              failwith uu___2
          | (uu___, FStarC_Syntax_Syntax.U_unknown) ->
              let uu___1 =
                let uu___2 =
                  FStarC_Class_Show.show FStarC_Syntax_Print.showable_univ
                    u11 in
                let uu___3 =
                  FStarC_Class_Show.show FStarC_Syntax_Print.showable_univ
                    u21 in
                FStarC_Compiler_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu___2 uu___3 in
              failwith uu___1
          | (FStarC_Syntax_Syntax.U_name x, FStarC_Syntax_Syntax.U_name y) ->
              let uu___ =
                let uu___1 = FStarC_Ident.string_of_id x in
                let uu___2 = FStarC_Ident.string_of_id y in uu___1 = uu___2 in
              if uu___
              then USolved wl
              else ufailed_simple "Incompatible universes"
          | (FStarC_Syntax_Syntax.U_zero, FStarC_Syntax_Syntax.U_zero) ->
              USolved wl
          | (FStarC_Syntax_Syntax.U_succ u12, FStarC_Syntax_Syntax.U_succ
             u22) -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStarC_Syntax_Syntax.U_unif v1, FStarC_Syntax_Syntax.U_unif v2)
              ->
              let uu___ = FStarC_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu___
              then USolved wl
              else
                (let wl1 =
                   extend_universe_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStarC_Syntax_Syntax.U_unif v1, u) ->
              let u3 = norm_univ wl u in
              let uu___ = occurs_univ v1 u3 in
              if uu___
              then
                let uu___1 =
                  let uu___2 =
                    FStarC_Class_Show.show FStarC_Syntax_Print.showable_univ
                      (FStarC_Syntax_Syntax.U_unif v1) in
                  let uu___3 =
                    FStarC_Class_Show.show FStarC_Syntax_Print.showable_univ
                      u3 in
                  FStarC_Compiler_Util.format2
                    "Failed occurs check: %s occurs in %s" uu___2 uu___3 in
                try_umax_components u11 u21 uu___1
              else
                (let uu___2 =
                   extend_universe_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu___2)
          | (u, FStarC_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu___ = occurs_univ v1 u3 in
              if uu___
              then
                let uu___1 =
                  let uu___2 =
                    FStarC_Class_Show.show FStarC_Syntax_Print.showable_univ
                      (FStarC_Syntax_Syntax.U_unif v1) in
                  let uu___3 =
                    FStarC_Class_Show.show FStarC_Syntax_Print.showable_univ
                      u3 in
                  FStarC_Compiler_Util.format2
                    "Failed occurs check: %s occurs in %s" uu___2 uu___3 in
                try_umax_components u11 u21 uu___1
              else
                (let uu___2 =
                   extend_universe_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu___2)
          | (FStarC_Syntax_Syntax.U_max uu___, uu___1) ->
              if wl.defer_ok = DeferAny
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu___3 = FStarC_Syntax_Util.eq_univs u12 u22 in
                 if uu___3
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu___, FStarC_Syntax_Syntax.U_max uu___1) ->
              if wl.defer_ok = DeferAny
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu___3 = FStarC_Syntax_Util.eq_univs u12 u22 in
                 if uu___3
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStarC_Syntax_Syntax.U_succ uu___, FStarC_Syntax_Syntax.U_zero)
              -> ufailed_simple "Incompatible universes"
          | (FStarC_Syntax_Syntax.U_succ uu___, FStarC_Syntax_Syntax.U_name
             uu___1) -> ufailed_simple "Incompatible universes"
          | (FStarC_Syntax_Syntax.U_zero, FStarC_Syntax_Syntax.U_succ uu___)
              -> ufailed_simple "Incompatible universes"
          | (FStarC_Syntax_Syntax.U_zero, FStarC_Syntax_Syntax.U_name uu___)
              -> ufailed_simple "Incompatible universes"
          | (FStarC_Syntax_Syntax.U_name uu___, FStarC_Syntax_Syntax.U_succ
             uu___1) -> ufailed_simple "Incompatible universes"
          | (FStarC_Syntax_Syntax.U_name uu___, FStarC_Syntax_Syntax.U_zero)
              -> ufailed_simple "Incompatible universes"
let (solve_universe_eq :
  Prims.int ->
    worklist ->
      FStarC_Syntax_Syntax.universe ->
        FStarC_Syntax_Syntax.universe -> univ_eq_sol)
  =
  fun orig ->
    fun wl ->
      fun u1 ->
        fun u2 ->
          if (wl.tcenv).FStarC_TypeChecker_Env.lax_universes
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
  worklist ->
    tprob ->
      FStarC_Syntax_Syntax.term ->
        FStarC_Syntax_Syntax.term -> (FStarC_Syntax_Syntax.term * worklist))
  =
  fun wl ->
    fun problem ->
      fun t1 ->
        fun t2 ->
          def_check_prob "guard_of_prob"
            (FStarC_TypeChecker_Common.TProb problem);
          (let env = p_env wl (FStarC_TypeChecker_Common.TProb problem) in
           let has_type_guard t11 t21 =
             match problem.FStarC_TypeChecker_Common.element with
             | FStar_Pervasives_Native.Some t ->
                 let uu___1 = FStarC_Syntax_Syntax.bv_to_name t in
                 FStarC_Syntax_Util.mk_has_type t11 uu___1 t21
             | FStar_Pervasives_Native.None ->
                 let x =
                   FStarC_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                     t11 in
                 (FStarC_Defensive.def_check_scoped
                    FStarC_TypeChecker_Env.hasBinders_env
                    FStarC_Class_Binders.hasNames_term
                    FStarC_Syntax_Print.pretty_term
                    t11.FStarC_Syntax_Syntax.pos "guard_of_prob.universe_of"
                    env t11;
                  (let u_x = env.FStarC_TypeChecker_Env.universe_of env t11 in
                   let uu___2 =
                     let uu___3 = FStarC_Syntax_Syntax.bv_to_name x in
                     FStarC_Syntax_Util.mk_has_type t11 uu___3 t21 in
                   FStarC_Syntax_Util.mk_forall u_x x uu___2)) in
           match problem.FStarC_TypeChecker_Common.relation with
           | FStarC_TypeChecker_Common.EQ ->
               mk_eq2 wl (FStarC_TypeChecker_Common.TProb problem) t1 t2
           | FStarC_TypeChecker_Common.SUB ->
               let uu___1 = has_type_guard t1 t2 in (uu___1, wl)
           | FStarC_TypeChecker_Common.SUBINV ->
               let uu___1 = has_type_guard t2 t1 in (uu___1, wl))
let (is_flex_pat : flex_t -> Prims.bool) =
  fun uu___ ->
    match uu___ with | Flex (uu___1, uu___2, []) -> true | uu___1 -> false
let (should_defer_flex_to_user_tac : worklist -> flex_t -> Prims.bool) =
  fun wl ->
    fun f ->
      let uu___ = f in
      match uu___ with
      | Flex (uu___1, u, uu___2) ->
          let b =
            FStarC_TypeChecker_DeferredImplicits.should_defer_uvar_to_user_tac
              wl.tcenv u in
          ((let uu___4 =
              FStarC_Compiler_Effect.op_Bang dbg_ResolveImplicitsHook in
            if uu___4
            then
              let uu___5 =
                FStarC_Class_Show.show FStarC_Syntax_Print.showable_ctxu u in
              let uu___6 =
                FStarC_Class_Show.show FStarC_Class_Show.showable_bool b in
              let uu___7 =
                FStarC_Class_Show.show FStarC_Class_Show.showable_bool
                  (wl.tcenv).FStarC_TypeChecker_Env.enable_defer_to_tac in
              FStarC_Compiler_Util.print3
                "Rel.should_defer_flex_to_user_tac for %s returning %s (env.enable_defer_to_tac: %s)\n"
                uu___5 uu___6 uu___7
            else ());
           b)
let (quasi_pattern :
  FStarC_TypeChecker_Env.env ->
    flex_t ->
      (FStarC_Syntax_Syntax.binders * FStarC_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env ->
    fun f ->
      let uu___ = f in
      match uu___ with
      | Flex (uu___1, ctx_uvar, args) ->
          let t_hd = FStarC_Syntax_Util.ctx_uvar_typ ctx_uvar in
          let ctx = ctx_uvar.FStarC_Syntax_Syntax.ctx_uvar_binders in
          let name_exists_in x bs =
            FStarC_Compiler_Util.for_some
              (fun uu___2 ->
                 match uu___2 with
                 | { FStarC_Syntax_Syntax.binder_bv = y;
                     FStarC_Syntax_Syntax.binder_qual = uu___3;
                     FStarC_Syntax_Syntax.binder_positivity = uu___4;
                     FStarC_Syntax_Syntax.binder_attrs = uu___5;_} ->
                     FStarC_Syntax_Syntax.bv_eq x y) bs in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([], []) ->
                let uu___2 =
                  let uu___3 =
                    let uu___4 = FStarC_Syntax_Syntax.mk_Total t_res in
                    FStarC_Syntax_Util.arrow formals uu___4 in
                  ((FStarC_Compiler_List.rev pat_binders), uu___3) in
                FStar_Pervasives_Native.Some uu___2
            | (uu___2, []) ->
                let uu___3 =
                  let uu___4 =
                    let uu___5 = FStarC_Syntax_Syntax.mk_Total t_res in
                    FStarC_Syntax_Util.arrow formals uu___5 in
                  ((FStarC_Compiler_List.rev pat_binders), uu___4) in
                FStar_Pervasives_Native.Some uu___3
            | (fml::formals1, (a, a_imp)::args2) ->
                let uu___2 =
                  ((fml.FStarC_Syntax_Syntax.binder_bv),
                    (fml.FStarC_Syntax_Syntax.binder_qual)) in
                (match uu___2 with
                 | (formal, formal_imp) ->
                     let uu___3 =
                       let uu___4 = FStarC_Syntax_Subst.compress a in
                       uu___4.FStarC_Syntax_Syntax.n in
                     (match uu___3 with
                      | FStarC_Syntax_Syntax.Tm_name x ->
                          let uu___4 =
                            (name_exists_in x ctx) ||
                              (name_exists_in x pat_binders) in
                          if uu___4
                          then aux (fml :: pat_binders) formals1 t_res args2
                          else
                            (let x1 =
                               {
                                 FStarC_Syntax_Syntax.ppname =
                                   (x.FStarC_Syntax_Syntax.ppname);
                                 FStarC_Syntax_Syntax.index =
                                   (x.FStarC_Syntax_Syntax.index);
                                 FStarC_Syntax_Syntax.sort =
                                   (formal.FStarC_Syntax_Syntax.sort)
                               } in
                             let subst =
                               let uu___6 =
                                 let uu___7 =
                                   let uu___8 =
                                     FStarC_Syntax_Syntax.bv_to_name x1 in
                                   (formal, uu___8) in
                                 FStarC_Syntax_Syntax.NT uu___7 in
                               [uu___6] in
                             let formals2 =
                               FStarC_Syntax_Subst.subst_binders subst
                                 formals1 in
                             let t_res1 =
                               FStarC_Syntax_Subst.subst subst t_res in
                             let uu___6 =
                               FStarC_Syntax_Util.bqual_and_attrs_of_aqual
                                 a_imp in
                             match uu___6 with
                             | (q, uu___7) ->
                                 let uu___8 =
                                   let uu___9 =
                                     FStarC_Syntax_Syntax.mk_binder_with_attrs
                                       {
                                         FStarC_Syntax_Syntax.ppname =
                                           (x1.FStarC_Syntax_Syntax.ppname);
                                         FStarC_Syntax_Syntax.index =
                                           (x1.FStarC_Syntax_Syntax.index);
                                         FStarC_Syntax_Syntax.sort =
                                           (formal.FStarC_Syntax_Syntax.sort)
                                       } q
                                       fml.FStarC_Syntax_Syntax.binder_positivity
                                       fml.FStarC_Syntax_Syntax.binder_attrs in
                                   uu___9 :: pat_binders in
                                 aux uu___8 formals2 t_res1 args2)
                      | uu___4 ->
                          aux (fml :: pat_binders) formals1 t_res args2))
            | ([], args2) ->
                let uu___2 =
                  let uu___3 =
                    FStarC_TypeChecker_Normalize.unfold_whnf env t_res in
                  FStarC_Syntax_Util.arrow_formals uu___3 in
                (match uu___2 with
                 | (more_formals, t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu___3 -> aux pat_binders more_formals t_res1 args2)) in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu___2 ->
               let uu___3 = FStarC_Syntax_Util.arrow_formals t_hd in
               (match uu___3 with
                | (formals, t_res) -> aux [] formals t_res args))
let (run_meta_arg_tac :
  FStarC_TypeChecker_Env.env_t ->
    FStarC_Syntax_Syntax.ctx_uvar -> FStarC_Syntax_Syntax.term)
  =
  fun env ->
    fun ctx_u ->
      match ctx_u.FStarC_Syntax_Syntax.ctx_uvar_meta with
      | FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Ctx_uvar_meta_tac
          tau) ->
          let env1 =
            {
              FStarC_TypeChecker_Env.solver =
                (env.FStarC_TypeChecker_Env.solver);
              FStarC_TypeChecker_Env.range =
                (env.FStarC_TypeChecker_Env.range);
              FStarC_TypeChecker_Env.curmodule =
                (env.FStarC_TypeChecker_Env.curmodule);
              FStarC_TypeChecker_Env.gamma =
                (ctx_u.FStarC_Syntax_Syntax.ctx_uvar_gamma);
              FStarC_TypeChecker_Env.gamma_sig =
                (env.FStarC_TypeChecker_Env.gamma_sig);
              FStarC_TypeChecker_Env.gamma_cache =
                (env.FStarC_TypeChecker_Env.gamma_cache);
              FStarC_TypeChecker_Env.modules =
                (env.FStarC_TypeChecker_Env.modules);
              FStarC_TypeChecker_Env.expected_typ =
                (env.FStarC_TypeChecker_Env.expected_typ);
              FStarC_TypeChecker_Env.sigtab =
                (env.FStarC_TypeChecker_Env.sigtab);
              FStarC_TypeChecker_Env.attrtab =
                (env.FStarC_TypeChecker_Env.attrtab);
              FStarC_TypeChecker_Env.instantiate_imp =
                (env.FStarC_TypeChecker_Env.instantiate_imp);
              FStarC_TypeChecker_Env.effects =
                (env.FStarC_TypeChecker_Env.effects);
              FStarC_TypeChecker_Env.generalize =
                (env.FStarC_TypeChecker_Env.generalize);
              FStarC_TypeChecker_Env.letrecs =
                (env.FStarC_TypeChecker_Env.letrecs);
              FStarC_TypeChecker_Env.top_level =
                (env.FStarC_TypeChecker_Env.top_level);
              FStarC_TypeChecker_Env.check_uvars =
                (env.FStarC_TypeChecker_Env.check_uvars);
              FStarC_TypeChecker_Env.use_eq_strict =
                (env.FStarC_TypeChecker_Env.use_eq_strict);
              FStarC_TypeChecker_Env.is_iface =
                (env.FStarC_TypeChecker_Env.is_iface);
              FStarC_TypeChecker_Env.admit =
                (env.FStarC_TypeChecker_Env.admit);
              FStarC_TypeChecker_Env.lax_universes =
                (env.FStarC_TypeChecker_Env.lax_universes);
              FStarC_TypeChecker_Env.phase1 =
                (env.FStarC_TypeChecker_Env.phase1);
              FStarC_TypeChecker_Env.failhard =
                (env.FStarC_TypeChecker_Env.failhard);
              FStarC_TypeChecker_Env.flychecking =
                (env.FStarC_TypeChecker_Env.flychecking);
              FStarC_TypeChecker_Env.uvar_subtyping =
                (env.FStarC_TypeChecker_Env.uvar_subtyping);
              FStarC_TypeChecker_Env.intactics =
                (env.FStarC_TypeChecker_Env.intactics);
              FStarC_TypeChecker_Env.nocoerce =
                (env.FStarC_TypeChecker_Env.nocoerce);
              FStarC_TypeChecker_Env.tc_term =
                (env.FStarC_TypeChecker_Env.tc_term);
              FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
                (env.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
              FStarC_TypeChecker_Env.universe_of =
                (env.FStarC_TypeChecker_Env.universe_of);
              FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
                (env.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
              FStarC_TypeChecker_Env.teq_nosmt_force =
                (env.FStarC_TypeChecker_Env.teq_nosmt_force);
              FStarC_TypeChecker_Env.subtype_nosmt_force =
                (env.FStarC_TypeChecker_Env.subtype_nosmt_force);
              FStarC_TypeChecker_Env.qtbl_name_and_index =
                (env.FStarC_TypeChecker_Env.qtbl_name_and_index);
              FStarC_TypeChecker_Env.normalized_eff_names =
                (env.FStarC_TypeChecker_Env.normalized_eff_names);
              FStarC_TypeChecker_Env.fv_delta_depths =
                (env.FStarC_TypeChecker_Env.fv_delta_depths);
              FStarC_TypeChecker_Env.proof_ns =
                (env.FStarC_TypeChecker_Env.proof_ns);
              FStarC_TypeChecker_Env.synth_hook =
                (env.FStarC_TypeChecker_Env.synth_hook);
              FStarC_TypeChecker_Env.try_solve_implicits_hook =
                (env.FStarC_TypeChecker_Env.try_solve_implicits_hook);
              FStarC_TypeChecker_Env.splice =
                (env.FStarC_TypeChecker_Env.splice);
              FStarC_TypeChecker_Env.mpreprocess =
                (env.FStarC_TypeChecker_Env.mpreprocess);
              FStarC_TypeChecker_Env.postprocess =
                (env.FStarC_TypeChecker_Env.postprocess);
              FStarC_TypeChecker_Env.identifier_info =
                (env.FStarC_TypeChecker_Env.identifier_info);
              FStarC_TypeChecker_Env.tc_hooks =
                (env.FStarC_TypeChecker_Env.tc_hooks);
              FStarC_TypeChecker_Env.dsenv =
                (env.FStarC_TypeChecker_Env.dsenv);
              FStarC_TypeChecker_Env.nbe = (env.FStarC_TypeChecker_Env.nbe);
              FStarC_TypeChecker_Env.strict_args_tab =
                (env.FStarC_TypeChecker_Env.strict_args_tab);
              FStarC_TypeChecker_Env.erasable_types_tab =
                (env.FStarC_TypeChecker_Env.erasable_types_tab);
              FStarC_TypeChecker_Env.enable_defer_to_tac =
                (env.FStarC_TypeChecker_Env.enable_defer_to_tac);
              FStarC_TypeChecker_Env.unif_allow_ref_guards =
                (env.FStarC_TypeChecker_Env.unif_allow_ref_guards);
              FStarC_TypeChecker_Env.erase_erasable_args =
                (env.FStarC_TypeChecker_Env.erase_erasable_args);
              FStarC_TypeChecker_Env.core_check =
                (env.FStarC_TypeChecker_Env.core_check);
              FStarC_TypeChecker_Env.missing_decl =
                (env.FStarC_TypeChecker_Env.missing_decl)
            } in
          ((let uu___1 = FStarC_Compiler_Effect.op_Bang dbg_Tac in
            if uu___1
            then
              let uu___2 =
                FStarC_Class_Show.show FStarC_Syntax_Print.showable_ctxu
                  ctx_u in
              FStarC_Compiler_Util.print1 "Running tactic for meta-arg %s\n"
                uu___2
            else ());
           FStarC_Errors.with_ctx "Running tactic for meta-arg"
             (fun uu___1 ->
                let uu___2 = FStarC_Syntax_Util.ctx_uvar_typ ctx_u in
                env1.FStarC_TypeChecker_Env.synth_hook env1 uu___2 tau))
      | uu___ ->
          failwith
            "run_meta_arg_tac must have been called with a uvar that has a meta tac"
let (simplify_vc :
  Prims.bool ->
    FStarC_TypeChecker_Env.env ->
      FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  =
  fun full_norm_allowed ->
    fun env ->
      fun t ->
        (let uu___1 = FStarC_Compiler_Effect.op_Bang dbg_Simplification in
         if uu___1
         then
           let uu___2 =
             FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
           FStarC_Compiler_Util.print1 "Simplifying guard %s\n" uu___2
         else ());
        (let steps =
           [FStarC_TypeChecker_Env.Beta;
           FStarC_TypeChecker_Env.Eager_unfolding;
           FStarC_TypeChecker_Env.Simplify;
           FStarC_TypeChecker_Env.Primops;
           FStarC_TypeChecker_Env.Exclude FStarC_TypeChecker_Env.Zeta] in
         let steps1 =
           if full_norm_allowed
           then steps
           else FStarC_TypeChecker_Env.NoFullNorm :: steps in
         let t' =
           norm_with_steps "FStarC.TypeChecker.Rel.simplify_vc" steps1 env t in
         (let uu___2 = FStarC_Compiler_Effect.op_Bang dbg_Simplification in
          if uu___2
          then
            let uu___3 =
              FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t' in
            FStarC_Compiler_Util.print1 "Simplified guard to %s\n" uu___3
          else ());
         t')
let (__simplify_guard :
  Prims.bool ->
    FStarC_TypeChecker_Env.env ->
      FStarC_TypeChecker_Common.guard_t -> FStarC_TypeChecker_Common.guard_t)
  =
  fun full_norm_allowed ->
    fun env ->
      fun g ->
        match g.FStarC_TypeChecker_Common.guard_f with
        | FStarC_TypeChecker_Common.Trivial -> g
        | FStarC_TypeChecker_Common.NonTrivial f ->
            let f1 = simplify_vc full_norm_allowed env f in
            let f2 = FStarC_TypeChecker_Common.check_trivial f1 in
            {
              FStarC_TypeChecker_Common.guard_f = f2;
              FStarC_TypeChecker_Common.deferred_to_tac =
                (g.FStarC_TypeChecker_Common.deferred_to_tac);
              FStarC_TypeChecker_Common.deferred =
                (g.FStarC_TypeChecker_Common.deferred);
              FStarC_TypeChecker_Common.univ_ineqs =
                (g.FStarC_TypeChecker_Common.univ_ineqs);
              FStarC_TypeChecker_Common.implicits =
                (g.FStarC_TypeChecker_Common.implicits)
            }
let (simplify_guard :
  FStarC_TypeChecker_Env.env ->
    FStarC_TypeChecker_Common.guard_t -> FStarC_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun g ->
      match g.FStarC_TypeChecker_Common.guard_f with
      | FStarC_TypeChecker_Common.Trivial -> g
      | FStarC_TypeChecker_Common.NonTrivial f ->
          let f1 = simplify_vc false env f in
          let f2 = FStarC_TypeChecker_Common.check_trivial f1 in
          {
            FStarC_TypeChecker_Common.guard_f = f2;
            FStarC_TypeChecker_Common.deferred_to_tac =
              (g.FStarC_TypeChecker_Common.deferred_to_tac);
            FStarC_TypeChecker_Common.deferred =
              (g.FStarC_TypeChecker_Common.deferred);
            FStarC_TypeChecker_Common.univ_ineqs =
              (g.FStarC_TypeChecker_Common.univ_ineqs);
            FStarC_TypeChecker_Common.implicits =
              (g.FStarC_TypeChecker_Common.implicits)
          }
let (simplify_guard_full_norm :
  FStarC_TypeChecker_Env.env ->
    FStarC_TypeChecker_Common.guard_t -> FStarC_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun g ->
      match g.FStarC_TypeChecker_Common.guard_f with
      | FStarC_TypeChecker_Common.Trivial -> g
      | FStarC_TypeChecker_Common.NonTrivial f ->
          let f1 = simplify_vc true env f in
          let f2 = FStarC_TypeChecker_Common.check_trivial f1 in
          {
            FStarC_TypeChecker_Common.guard_f = f2;
            FStarC_TypeChecker_Common.deferred_to_tac =
              (g.FStarC_TypeChecker_Common.deferred_to_tac);
            FStarC_TypeChecker_Common.deferred =
              (g.FStarC_TypeChecker_Common.deferred);
            FStarC_TypeChecker_Common.univ_ineqs =
              (g.FStarC_TypeChecker_Common.univ_ineqs);
            FStarC_TypeChecker_Common.implicits =
              (g.FStarC_TypeChecker_Common.implicits)
          }
let (apply_substitutive_indexed_subcomp :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.indexed_effect_combinator_kind ->
      FStarC_Syntax_Syntax.binders ->
        FStarC_Syntax_Syntax.comp ->
          FStarC_Syntax_Syntax.comp_typ ->
            FStarC_Syntax_Syntax.comp_typ ->
              (worklist ->
                 FStarC_Syntax_Syntax.term ->
                   FStarC_TypeChecker_Common.rel ->
                     FStarC_Syntax_Syntax.term ->
                       Prims.string ->
                         (FStarC_TypeChecker_Common.prob * worklist))
                ->
                Prims.int ->
                  worklist ->
                    Prims.string ->
                      FStarC_Compiler_Range_Type.range ->
                        (FStarC_Syntax_Syntax.typ *
                          FStarC_TypeChecker_Common.prob Prims.list *
                          worklist))
  =
  fun env ->
    fun k ->
      fun bs ->
        fun subcomp_c ->
          fun ct1 ->
            fun ct2 ->
              fun sub_prob ->
                fun num_effect_params ->
                  fun wl ->
                    fun subcomp_name ->
                      fun r1 ->
                        let uu___ =
                          let uu___1 = bs in
                          match uu___1 with
                          | a_b::bs1 ->
                              (bs1,
                                [FStarC_Syntax_Syntax.NT
                                   ((a_b.FStarC_Syntax_Syntax.binder_bv),
                                     (ct2.FStarC_Syntax_Syntax.result_typ))]) in
                        match uu___ with
                        | (bs1, subst) ->
                            let uu___1 =
                              if num_effect_params = Prims.int_zero
                              then
                                (bs1, subst,
                                  (ct1.FStarC_Syntax_Syntax.effect_args),
                                  (ct2.FStarC_Syntax_Syntax.effect_args), [],
                                  wl)
                              else
                                (let split l =
                                   FStarC_Compiler_List.splitAt
                                     num_effect_params l in
                                 let uu___3 = split bs1 in
                                 match uu___3 with
                                 | (eff_params_bs, bs2) ->
                                     let uu___4 =
                                       split
                                         ct1.FStarC_Syntax_Syntax.effect_args in
                                     (match uu___4 with
                                      | (param_args1, args1) ->
                                          let uu___5 =
                                            split
                                              ct2.FStarC_Syntax_Syntax.effect_args in
                                          (match uu___5 with
                                           | (param_args2, args2) ->
                                               let uu___6 =
                                                 FStarC_Compiler_List.fold_left2
                                                   (fun uu___7 ->
                                                      fun uu___8 ->
                                                        fun uu___9 ->
                                                          match (uu___7,
                                                                  uu___8,
                                                                  uu___9)
                                                          with
                                                          | ((ps, wl1),
                                                             (t1, uu___10),
                                                             (t2, uu___11))
                                                              ->
                                                              let uu___12 =
                                                                sub_prob wl1
                                                                  t1
                                                                  FStarC_TypeChecker_Common.EQ
                                                                  t2
                                                                  "effect params subcomp" in
                                                              (match uu___12
                                                               with
                                                               | (p, wl2) ->
                                                                   ((FStarC_Compiler_List.op_At
                                                                    ps [p]),
                                                                    wl2)))
                                                   ([], wl) param_args1
                                                   param_args2 in
                                               (match uu___6 with
                                                | (probs, wl1) ->
                                                    let param_subst =
                                                      FStarC_Compiler_List.map2
                                                        (fun b ->
                                                           fun uu___7 ->
                                                             match uu___7
                                                             with
                                                             | (arg, uu___8)
                                                                 ->
                                                                 FStarC_Syntax_Syntax.NT
                                                                   ((b.FStarC_Syntax_Syntax.binder_bv),
                                                                    arg))
                                                        eff_params_bs
                                                        param_args1 in
                                                    (bs2,
                                                      (FStarC_Compiler_List.op_At
                                                         subst param_subst),
                                                      args1, args2, probs,
                                                      wl1))))) in
                            (match uu___1 with
                             | (bs2, subst1, args1, args2,
                                eff_params_sub_probs, wl1) ->
                                 let uu___2 =
                                   let uu___3 =
                                     FStarC_Compiler_List.splitAt
                                       (FStarC_Compiler_List.length args1)
                                       bs2 in
                                   match uu___3 with
                                   | (f_bs, bs3) ->
                                       let f_substs =
                                         FStarC_Compiler_List.map2
                                           (fun f_b ->
                                              fun uu___4 ->
                                                match uu___4 with
                                                | (arg, uu___5) ->
                                                    FStarC_Syntax_Syntax.NT
                                                      ((f_b.FStarC_Syntax_Syntax.binder_bv),
                                                        arg)) f_bs args1 in
                                       (bs3,
                                         (FStarC_Compiler_List.op_At subst1
                                            f_substs)) in
                                 (match uu___2 with
                                  | (bs3, subst2) ->
                                      let uu___3 =
                                        if
                                          FStarC_Syntax_Syntax.uu___is_Substitutive_combinator
                                            k
                                        then
                                          let uu___4 =
                                            FStarC_Compiler_List.splitAt
                                              (FStarC_Compiler_List.length
                                                 args2) bs3 in
                                          match uu___4 with
                                          | (g_bs, bs4) ->
                                              let g_substs =
                                                FStarC_Compiler_List.map2
                                                  (fun g_b ->
                                                     fun uu___5 ->
                                                       match uu___5 with
                                                       | (arg, uu___6) ->
                                                           FStarC_Syntax_Syntax.NT
                                                             ((g_b.FStarC_Syntax_Syntax.binder_bv),
                                                               arg)) g_bs
                                                  args2 in
                                              (bs4,
                                                (FStarC_Compiler_List.op_At
                                                   subst2 g_substs), [], wl1)
                                        else
                                          if
                                            FStarC_Syntax_Syntax.uu___is_Substitutive_invariant_combinator
                                              k
                                          then
                                            (let uu___5 =
                                               FStarC_Compiler_List.fold_left2
                                                 (fun uu___6 ->
                                                    fun uu___7 ->
                                                      fun uu___8 ->
                                                        match (uu___6,
                                                                uu___7,
                                                                uu___8)
                                                        with
                                                        | ((ps, wl2),
                                                           (t1, uu___9),
                                                           (t2, uu___10)) ->
                                                            let uu___11 =
                                                              sub_prob wl2 t1
                                                                FStarC_TypeChecker_Common.EQ
                                                                t2
                                                                "substitutive inv subcomp args" in
                                                            (match uu___11
                                                             with
                                                             | (p, wl3) ->
                                                                 ((FStarC_Compiler_List.op_At
                                                                    ps 
                                                                    [p]),
                                                                   wl3)))
                                                 ([], wl1) args1 args2 in
                                             match uu___5 with
                                             | (probs, wl2) ->
                                                 (bs3, subst2, probs, wl2))
                                          else
                                            failwith
                                              "Impossible (rel.apply_substitutive_indexed_subcomp unexpected k" in
                                      (match uu___3 with
                                       | (bs4, subst3, f_g_args_eq_sub_probs,
                                          wl2) ->
                                           let bs5 =
                                             let uu___4 =
                                               FStarC_Compiler_List.splitAt
                                                 ((FStarC_Compiler_List.length
                                                     bs4)
                                                    - Prims.int_one) bs4 in
                                             FStar_Pervasives_Native.fst
                                               uu___4 in
                                           let uu___4 =
                                             FStarC_Compiler_List.fold_left
                                               (fun uu___5 ->
                                                  fun b ->
                                                    match uu___5 with
                                                    | (ss, wl3) ->
                                                        let uu___6 =
                                                          FStarC_TypeChecker_Env.uvars_for_binders
                                                            env [b] ss
                                                            (fun b1 ->
                                                               let uu___7 =
                                                                 FStarC_Compiler_Effect.op_Bang
                                                                   dbg_LayeredEffectsApp in
                                                               if uu___7
                                                               then
                                                                 let uu___8 =
                                                                   FStarC_Class_Show.show
                                                                    FStarC_Syntax_Print.showable_binder
                                                                    b1 in
                                                                 let uu___9 =
                                                                   FStarC_Compiler_Range_Ops.string_of_range
                                                                    r1 in
                                                                 FStarC_Compiler_Util.format3
                                                                   "implicit var for additional binder %s in subcomp %s at %s"
                                                                   uu___8
                                                                   subcomp_name
                                                                   uu___9
                                                               else
                                                                 "apply_substitutive_indexed_subcomp")
                                                            r1 in
                                                        (match uu___6 with
                                                         | (uv_t::[], g) ->
                                                             let uu___7 =
                                                               let uu___8 =
                                                                 FStarC_Class_Monoid.op_Plus_Plus
                                                                   (FStarC_Compiler_CList.monoid_clist
                                                                    ())
                                                                   g.FStarC_TypeChecker_Common.implicits
                                                                   wl3.wl_implicits in
                                                               {
                                                                 attempting =
                                                                   (wl3.attempting);
                                                                 wl_deferred
                                                                   =
                                                                   (wl3.wl_deferred);
                                                                 wl_deferred_to_tac
                                                                   =
                                                                   (wl3.wl_deferred_to_tac);
                                                                 ctr =
                                                                   (wl3.ctr);
                                                                 defer_ok =
                                                                   (wl3.defer_ok);
                                                                 smt_ok =
                                                                   (wl3.smt_ok);
                                                                 umax_heuristic_ok
                                                                   =
                                                                   (wl3.umax_heuristic_ok);
                                                                 tcenv =
                                                                   (wl3.tcenv);
                                                                 wl_implicits
                                                                   = uu___8;
                                                                 repr_subcomp_allowed
                                                                   =
                                                                   (wl3.repr_subcomp_allowed);
                                                                 typeclass_variables
                                                                   =
                                                                   (wl3.typeclass_variables)
                                                               } in
                                                             ((FStarC_Compiler_List.op_At
                                                                 ss
                                                                 [FStarC_Syntax_Syntax.NT
                                                                    ((b.FStarC_Syntax_Syntax.binder_bv),
                                                                    uv_t)]),
                                                               uu___7)))
                                               (subst3, wl2) bs5 in
                                           (match uu___4 with
                                            | (subst4, wl3) ->
                                                let subcomp_ct =
                                                  let uu___5 =
                                                    FStarC_Syntax_Subst.subst_comp
                                                      subst4 subcomp_c in
                                                  FStarC_TypeChecker_Env.comp_to_comp_typ
                                                    env uu___5 in
                                                let fml =
                                                  let uu___5 =
                                                    let uu___6 =
                                                      FStarC_Compiler_List.hd
                                                        subcomp_ct.FStarC_Syntax_Syntax.comp_univs in
                                                    let uu___7 =
                                                      let uu___8 =
                                                        FStarC_Compiler_List.hd
                                                          subcomp_ct.FStarC_Syntax_Syntax.effect_args in
                                                      FStar_Pervasives_Native.fst
                                                        uu___8 in
                                                    (uu___6, uu___7) in
                                                  match uu___5 with
                                                  | (u, wp) ->
                                                      FStarC_TypeChecker_Env.pure_precondition_for_trivial_post
                                                        env u
                                                        subcomp_ct.FStarC_Syntax_Syntax.result_typ
                                                        wp
                                                        FStarC_Compiler_Range_Type.dummyRange in
                                                (fml,
                                                  (FStarC_Compiler_List.op_At
                                                     eff_params_sub_probs
                                                     f_g_args_eq_sub_probs),
                                                  wl3)))))
let (apply_ad_hoc_indexed_subcomp :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.binders ->
      FStarC_Syntax_Syntax.comp ->
        FStarC_Syntax_Syntax.comp_typ ->
          FStarC_Syntax_Syntax.comp_typ ->
            (worklist ->
               FStarC_Syntax_Syntax.term ->
                 FStarC_TypeChecker_Common.rel ->
                   FStarC_Syntax_Syntax.term ->
                     Prims.string ->
                       (FStarC_TypeChecker_Common.prob * worklist))
              ->
              worklist ->
                Prims.string ->
                  FStarC_Compiler_Range_Type.range ->
                    (FStarC_Syntax_Syntax.typ *
                      FStarC_TypeChecker_Common.prob Prims.list * worklist))
  =
  fun env ->
    fun bs ->
      fun subcomp_c ->
        fun ct1 ->
          fun ct2 ->
            fun sub_prob ->
              fun wl ->
                fun subcomp_name ->
                  fun r1 ->
                    let stronger_t_shape_error s =
                      let uu___ =
                        FStarC_Ident.string_of_lid
                          ct2.FStarC_Syntax_Syntax.effect_name in
                      FStarC_Compiler_Util.format2
                        "Unexpected shape of stronger for %s, reason: %s"
                        uu___ s in
                    let uu___ =
                      if
                        (FStarC_Compiler_List.length bs) >=
                          (Prims.of_int (2))
                      then
                        let uu___1 = bs in
                        match uu___1 with
                        | a_b::bs1 ->
                            let uu___2 =
                              let uu___3 =
                                FStarC_Compiler_List.splitAt
                                  ((FStarC_Compiler_List.length bs1) -
                                     Prims.int_one) bs1 in
                              match uu___3 with
                              | (l1, l2) ->
                                  let uu___4 = FStarC_Compiler_List.hd l2 in
                                  (l1, uu___4) in
                            (match uu___2 with
                             | (rest_bs, f_b) -> (a_b, rest_bs, f_b))
                      else
                        (let uu___2 =
                           stronger_t_shape_error
                             "not an arrow or not enough binders" in
                         FStarC_Errors.raise_error
                           FStarC_Class_HasRange.hasRange_range r1
                           FStarC_Errors_Codes.Fatal_UnexpectedExpressionType
                           ()
                           (Obj.magic
                              FStarC_Errors_Msg.is_error_message_string)
                           (Obj.magic uu___2)) in
                    match uu___ with
                    | (a_b, rest_bs, f_b) ->
                        let uu___1 =
                          FStarC_TypeChecker_Env.uvars_for_binders env
                            rest_bs
                            [FStarC_Syntax_Syntax.NT
                               ((a_b.FStarC_Syntax_Syntax.binder_bv),
                                 (ct2.FStarC_Syntax_Syntax.result_typ))]
                            (fun b ->
                               let uu___2 =
                                 FStarC_Compiler_Effect.op_Bang
                                   dbg_LayeredEffectsApp in
                               if uu___2
                               then
                                 let uu___3 =
                                   FStarC_Class_Show.show
                                     FStarC_Syntax_Print.showable_binder b in
                                 let uu___4 =
                                   FStarC_Compiler_Range_Ops.string_of_range
                                     r1 in
                                 FStarC_Compiler_Util.format3
                                   "implicit for binder %s in subcomp %s at %s"
                                   uu___3 subcomp_name uu___4
                               else "apply_ad_hoc_indexed_subcomp") r1 in
                        (match uu___1 with
                         | (rest_bs_uvars, g_uvars) ->
                             let wl1 =
                               let uu___2 =
                                 FStarC_Class_Monoid.op_Plus_Plus
                                   (FStarC_Compiler_CList.monoid_clist ())
                                   g_uvars.FStarC_TypeChecker_Common.implicits
                                   wl.wl_implicits in
                               {
                                 attempting = (wl.attempting);
                                 wl_deferred = (wl.wl_deferred);
                                 wl_deferred_to_tac = (wl.wl_deferred_to_tac);
                                 ctr = (wl.ctr);
                                 defer_ok = (wl.defer_ok);
                                 smt_ok = (wl.smt_ok);
                                 umax_heuristic_ok = (wl.umax_heuristic_ok);
                                 tcenv = (wl.tcenv);
                                 wl_implicits = uu___2;
                                 repr_subcomp_allowed =
                                   (wl.repr_subcomp_allowed);
                                 typeclass_variables =
                                   (wl.typeclass_variables)
                               } in
                             let substs =
                               FStarC_Compiler_List.map2
                                 (fun b ->
                                    fun t ->
                                      FStarC_Syntax_Syntax.NT
                                        ((b.FStarC_Syntax_Syntax.binder_bv),
                                          t)) (a_b :: rest_bs)
                                 ((ct2.FStarC_Syntax_Syntax.result_typ) ::
                                 rest_bs_uvars) in
                             let uu___2 =
                               let f_sort_is =
                                 let uu___3 =
                                   let uu___4 =
                                     FStarC_TypeChecker_Env.is_layered_effect
                                       env
                                       ct1.FStarC_Syntax_Syntax.effect_name in
                                   let uu___5 =
                                     stronger_t_shape_error
                                       "type of f is not a repr type" in
                                   FStarC_Syntax_Util.effect_indices_from_repr
                                     (f_b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort
                                     uu___4 r1 uu___5 in
                                 FStarC_Compiler_List.map
                                   (FStarC_Syntax_Subst.subst substs) uu___3 in
                               let uu___3 =
                                 FStarC_Compiler_List.map
                                   FStar_Pervasives_Native.fst
                                   ct1.FStarC_Syntax_Syntax.effect_args in
                               FStarC_Compiler_List.fold_left2
                                 (fun uu___4 ->
                                    fun f_sort_i ->
                                      fun c1_i ->
                                        match uu___4 with
                                        | (ps, wl2) ->
                                            ((let uu___6 =
                                                FStarC_Compiler_Effect.op_Bang
                                                  dbg_LayeredEffectsApp in
                                              if uu___6
                                              then
                                                let uu___7 =
                                                  FStarC_Class_Show.show
                                                    FStarC_Syntax_Print.showable_term
                                                    f_sort_i in
                                                let uu___8 =
                                                  FStarC_Class_Show.show
                                                    FStarC_Syntax_Print.showable_term
                                                    c1_i in
                                                FStarC_Compiler_Util.print3
                                                  "Layered Effects (%s) %s = %s\n"
                                                  subcomp_name uu___7 uu___8
                                              else ());
                                             (let uu___6 =
                                                sub_prob wl2 f_sort_i
                                                  FStarC_TypeChecker_Common.EQ
                                                  c1_i "indices of c1" in
                                              match uu___6 with
                                              | (p, wl3) ->
                                                  ((FStarC_Compiler_List.op_At
                                                      ps [p]), wl3))))
                                 ([], wl1) f_sort_is uu___3 in
                             (match uu___2 with
                              | (f_sub_probs, wl2) ->
                                  let subcomp_ct =
                                    let uu___3 =
                                      FStarC_Syntax_Subst.subst_comp substs
                                        subcomp_c in
                                    FStarC_TypeChecker_Env.comp_to_comp_typ
                                      env uu___3 in
                                  let uu___3 =
                                    let g_sort_is =
                                      let uu___4 =
                                        FStarC_TypeChecker_Env.is_layered_effect
                                          env
                                          ct2.FStarC_Syntax_Syntax.effect_name in
                                      let uu___5 =
                                        stronger_t_shape_error
                                          "subcomp return type is not a repr" in
                                      FStarC_Syntax_Util.effect_indices_from_repr
                                        subcomp_ct.FStarC_Syntax_Syntax.result_typ
                                        uu___4 r1 uu___5 in
                                    let uu___4 =
                                      FStarC_Compiler_List.map
                                        FStar_Pervasives_Native.fst
                                        ct2.FStarC_Syntax_Syntax.effect_args in
                                    FStarC_Compiler_List.fold_left2
                                      (fun uu___5 ->
                                         fun g_sort_i ->
                                           fun c2_i ->
                                             match uu___5 with
                                             | (ps, wl3) ->
                                                 ((let uu___7 =
                                                     FStarC_Compiler_Effect.op_Bang
                                                       dbg_LayeredEffectsApp in
                                                   if uu___7
                                                   then
                                                     let uu___8 =
                                                       FStarC_Class_Show.show
                                                         FStarC_Syntax_Print.showable_term
                                                         g_sort_i in
                                                     let uu___9 =
                                                       FStarC_Class_Show.show
                                                         FStarC_Syntax_Print.showable_term
                                                         c2_i in
                                                     FStarC_Compiler_Util.print3
                                                       "Layered Effects (%s) %s = %s\n"
                                                       subcomp_name uu___8
                                                       uu___9
                                                   else ());
                                                  (let uu___7 =
                                                     sub_prob wl3 g_sort_i
                                                       FStarC_TypeChecker_Common.EQ
                                                       c2_i "indices of c2" in
                                                   match uu___7 with
                                                   | (p, wl4) ->
                                                       ((FStarC_Compiler_List.op_At
                                                           ps [p]), wl4))))
                                      ([], wl2) g_sort_is uu___4 in
                                  (match uu___3 with
                                   | (g_sub_probs, wl3) ->
                                       let fml =
                                         let uu___4 =
                                           let uu___5 =
                                             FStarC_Compiler_List.hd
                                               subcomp_ct.FStarC_Syntax_Syntax.comp_univs in
                                           let uu___6 =
                                             let uu___7 =
                                               FStarC_Compiler_List.hd
                                                 subcomp_ct.FStarC_Syntax_Syntax.effect_args in
                                             FStar_Pervasives_Native.fst
                                               uu___7 in
                                           (uu___5, uu___6) in
                                         match uu___4 with
                                         | (u, wp) ->
                                             FStarC_TypeChecker_Env.pure_precondition_for_trivial_post
                                               env u
                                               subcomp_ct.FStarC_Syntax_Syntax.result_typ
                                               wp
                                               FStarC_Compiler_Range_Type.dummyRange in
                                       (fml,
                                         (FStarC_Compiler_List.op_At
                                            f_sub_probs g_sub_probs), wl3))))
let (has_typeclass_constraint :
  FStarC_Syntax_Syntax.ctx_uvar -> worklist -> Prims.bool) =
  fun u ->
    fun wl ->
      FStarC_Class_Setlike.for_any ()
        (Obj.magic
           (FStarC_Compiler_RBSet.setlike_rbset
              FStarC_Syntax_Free.ord_ctx_uvar))
        (fun v ->
           FStarC_Syntax_Unionfind.equiv v.FStarC_Syntax_Syntax.ctx_uvar_head
             u.FStarC_Syntax_Syntax.ctx_uvar_head)
        (Obj.magic wl.typeclass_variables)
let (lazy_complete_repr : FStarC_Syntax_Syntax.lazy_kind -> Prims.bool) =
  fun k ->
    match k with
    | FStarC_Syntax_Syntax.Lazy_bv -> true
    | FStarC_Syntax_Syntax.Lazy_namedv -> true
    | FStarC_Syntax_Syntax.Lazy_binder -> true
    | FStarC_Syntax_Syntax.Lazy_letbinding -> true
    | FStarC_Syntax_Syntax.Lazy_fvar -> true
    | FStarC_Syntax_Syntax.Lazy_comp -> true
    | FStarC_Syntax_Syntax.Lazy_sigelt -> true
    | FStarC_Syntax_Syntax.Lazy_universe -> true
    | uu___ -> false
let (has_free_uvars : FStarC_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu___ =
      let uu___1 = FStarC_Syntax_Free.uvars_uncached t in
      FStarC_Class_Setlike.is_empty ()
        (Obj.magic
           (FStarC_Compiler_FlatSet.setlike_flat_set
              FStarC_Syntax_Free.ord_ctx_uvar)) (Obj.magic uu___1) in
    Prims.op_Negation uu___
let (env_has_free_uvars : FStarC_TypeChecker_Env.env_t -> Prims.bool) =
  fun e ->
    let uu___ = FStarC_TypeChecker_Env.all_binders e in
    FStarC_Compiler_List.existsb
      (fun b ->
         has_free_uvars
           (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort)
      uu___
let (gamma_has_free_uvars :
  FStarC_Syntax_Syntax.binding Prims.list -> Prims.bool) =
  fun g ->
    FStarC_Compiler_List.existsb
      (fun uu___ ->
         match uu___ with
         | FStarC_Syntax_Syntax.Binding_var bv ->
             has_free_uvars bv.FStarC_Syntax_Syntax.sort
         | uu___1 -> false) g
type reveal_hide_t =
  | Hide of (FStarC_Syntax_Syntax.universe * FStarC_Syntax_Syntax.typ *
  FStarC_Syntax_Syntax.term) 
  | Reveal of (FStarC_Syntax_Syntax.universe * FStarC_Syntax_Syntax.typ *
  FStarC_Syntax_Syntax.term) 
let (uu___is_Hide : reveal_hide_t -> Prims.bool) =
  fun projectee -> match projectee with | Hide _0 -> true | uu___ -> false
let (__proj__Hide__item___0 :
  reveal_hide_t ->
    (FStarC_Syntax_Syntax.universe * FStarC_Syntax_Syntax.typ *
      FStarC_Syntax_Syntax.term))
  = fun projectee -> match projectee with | Hide _0 -> _0
let (uu___is_Reveal : reveal_hide_t -> Prims.bool) =
  fun projectee -> match projectee with | Reveal _0 -> true | uu___ -> false
let (__proj__Reveal__item___0 :
  reveal_hide_t ->
    (FStarC_Syntax_Syntax.universe * FStarC_Syntax_Syntax.typ *
      FStarC_Syntax_Syntax.term))
  = fun projectee -> match projectee with | Reveal _0 -> _0
let rec (solve : worklist -> solution) =
  fun probs ->
    (let uu___1 = FStarC_Compiler_Effect.op_Bang dbg_Rel in
     if uu___1
     then
       let uu___2 = wl_to_string probs in
       FStarC_Compiler_Util.print1 "solve:\n\t%s\n" uu___2
     else ());
    (let uu___2 = FStarC_Compiler_Effect.op_Bang dbg_ImplicitTrace in
     if uu___2
     then
       let uu___3 =
         FStarC_Class_Show.show
           (FStarC_Compiler_CList.showable_clist
              FStarC_TypeChecker_Common.showable_implicit) probs.wl_implicits in
       FStarC_Compiler_Util.print1 "solve: wl_implicits = %s\n" uu___3
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
             repr_subcomp_allowed = (probs.repr_subcomp_allowed);
             typeclass_variables = (probs.typeclass_variables)
           } in
         (def_check_prob "solve,hd" hd;
          (match hd with
           | FStarC_TypeChecker_Common.CProb cp ->
               solve_c (maybe_invert cp) probs1
           | FStarC_TypeChecker_Common.TProb tp ->
               let uu___4 =
                 FStarC_Compiler_Util.physical_equality
                   tp.FStarC_TypeChecker_Common.lhs
                   tp.FStarC_TypeChecker_Common.rhs in
               if uu___4
               then
                 let uu___5 =
                   solve_prob hd FStar_Pervasives_Native.None [] probs1 in
                 solve uu___5
               else
                 (let is_expand_uvar t =
                    let uu___6 =
                      let uu___7 = FStarC_Syntax_Subst.compress t in
                      uu___7.FStarC_Syntax_Syntax.n in
                    match uu___6 with
                    | FStarC_Syntax_Syntax.Tm_uvar (ctx_u, uu___7) ->
                        let uu___8 =
                          FStarC_Syntax_Unionfind.find_decoration
                            ctx_u.FStarC_Syntax_Syntax.ctx_uvar_head in
                        uu___8.FStarC_Syntax_Syntax.uvar_decoration_should_unrefine
                    | uu___7 -> false in
                  let maybe_expand tp1 =
                    let uu___6 =
                      ((let uu___7 = FStarC_Options_Ext.get "__unrefine" in
                        uu___7 <> "") &&
                         (tp1.FStarC_TypeChecker_Common.relation =
                            FStarC_TypeChecker_Common.SUB))
                        && (is_expand_uvar tp1.FStarC_TypeChecker_Common.rhs) in
                    if uu___6
                    then
                      let lhs = tp1.FStarC_TypeChecker_Common.lhs in
                      let lhs_norm =
                        FStarC_TypeChecker_Normalize.unfold_whnf'
                          [FStarC_TypeChecker_Env.DontUnfoldAttr
                             [FStarC_Parser_Const.do_not_unrefine_attr]]
                          (p_env probs1 hd) lhs in
                      let uu___7 =
                        let uu___8 =
                          let uu___9 = FStarC_Syntax_Subst.compress lhs_norm in
                          uu___9.FStarC_Syntax_Syntax.n in
                        FStarC_Syntax_Syntax.uu___is_Tm_refine uu___8 in
                      (if uu___7
                       then
                         let lhs' =
                           FStarC_TypeChecker_Normalize.unfold_whnf'
                             [FStarC_TypeChecker_Env.DontUnfoldAttr
                                [FStarC_Parser_Const.do_not_unrefine_attr];
                             FStarC_TypeChecker_Env.Unrefine]
                             (p_env probs1 hd) lhs_norm in
                         ((let uu___9 =
                             FStarC_Compiler_Effect.op_Bang dbg_Rel in
                           if uu___9
                           then
                             let uu___10 =
                               FStarC_Class_Show.show
                                 FStarC_Syntax_Print.showable_term
                                 tp1.FStarC_TypeChecker_Common.rhs in
                             let uu___11 =
                               FStarC_Class_Show.show
                                 FStarC_Syntax_Print.showable_term lhs in
                             let uu___12 =
                               FStarC_Class_Show.show
                                 FStarC_Syntax_Print.showable_term lhs' in
                             FStarC_Compiler_Util.print3
                               "GGG widening uvar %s! RHS %s ~> %s\n" uu___10
                               uu___11 uu___12
                           else ());
                          {
                            FStarC_TypeChecker_Common.pid =
                              (tp1.FStarC_TypeChecker_Common.pid);
                            FStarC_TypeChecker_Common.lhs = lhs';
                            FStarC_TypeChecker_Common.relation =
                              (tp1.FStarC_TypeChecker_Common.relation);
                            FStarC_TypeChecker_Common.rhs =
                              (tp1.FStarC_TypeChecker_Common.rhs);
                            FStarC_TypeChecker_Common.element =
                              (tp1.FStarC_TypeChecker_Common.element);
                            FStarC_TypeChecker_Common.logical_guard =
                              (tp1.FStarC_TypeChecker_Common.logical_guard);
                            FStarC_TypeChecker_Common.logical_guard_uvar =
                              (tp1.FStarC_TypeChecker_Common.logical_guard_uvar);
                            FStarC_TypeChecker_Common.reason =
                              (tp1.FStarC_TypeChecker_Common.reason);
                            FStarC_TypeChecker_Common.loc =
                              (tp1.FStarC_TypeChecker_Common.loc);
                            FStarC_TypeChecker_Common.rank =
                              (tp1.FStarC_TypeChecker_Common.rank);
                            FStarC_TypeChecker_Common.logical =
                              (tp1.FStarC_TypeChecker_Common.logical)
                          })
                       else tp1)
                    else tp1 in
                  let tp1 = maybe_expand tp in
                  if
                    (rank1 = FStarC_TypeChecker_Common.Rigid_rigid) ||
                      ((tp1.FStarC_TypeChecker_Common.relation =
                          FStarC_TypeChecker_Common.EQ)
                         && (rank1 <> FStarC_TypeChecker_Common.Flex_flex))
                  then solve_t' tp1 probs1
                  else
                    if probs1.defer_ok = DeferAny
                    then
                      maybe_defer_to_user_tac tp1
                        "deferring flex_rigid or flex_flex subtyping" probs1
                    else
                      if rank1 = FStarC_TypeChecker_Common.Flex_flex
                      then
                        solve_t'
                          {
                            FStarC_TypeChecker_Common.pid =
                              (tp1.FStarC_TypeChecker_Common.pid);
                            FStarC_TypeChecker_Common.lhs =
                              (tp1.FStarC_TypeChecker_Common.lhs);
                            FStarC_TypeChecker_Common.relation =
                              FStarC_TypeChecker_Common.EQ;
                            FStarC_TypeChecker_Common.rhs =
                              (tp1.FStarC_TypeChecker_Common.rhs);
                            FStarC_TypeChecker_Common.element =
                              (tp1.FStarC_TypeChecker_Common.element);
                            FStarC_TypeChecker_Common.logical_guard =
                              (tp1.FStarC_TypeChecker_Common.logical_guard);
                            FStarC_TypeChecker_Common.logical_guard_uvar =
                              (tp1.FStarC_TypeChecker_Common.logical_guard_uvar);
                            FStarC_TypeChecker_Common.reason =
                              (tp1.FStarC_TypeChecker_Common.reason);
                            FStarC_TypeChecker_Common.loc =
                              (tp1.FStarC_TypeChecker_Common.loc);
                            FStarC_TypeChecker_Common.rank =
                              (tp1.FStarC_TypeChecker_Common.rank);
                            FStarC_TypeChecker_Common.logical =
                              (tp1.FStarC_TypeChecker_Common.logical)
                          } probs1
                      else
                        solve_rigid_flex_or_flex_rigid_subtyping rank1 tp1
                          probs1)))
     | FStar_Pervasives_Native.None ->
         let uu___3 =
           Obj.magic
             (FStarC_Class_Listlike.view ()
                (Obj.magic (FStarC_Compiler_CList.listlike_clist ()))
                (Obj.magic probs.wl_deferred)) in
         (match uu___3 with
          | FStarC_Class_Listlike.VNil ->
              let uu___4 =
                let uu___5 = as_deferred probs.wl_deferred_to_tac in
                ((Obj.magic
                    (FStarC_Class_Listlike.empty ()
                       (Obj.magic (FStarC_Compiler_CList.listlike_clist ())))),
                  uu___5, (probs.wl_implicits)) in
              Success uu___4
          | FStarC_Class_Listlike.VCons (uu___4, uu___5) ->
              let uu___6 =
                FStarC_Compiler_CList.partition
                  (fun uu___7 ->
                     match uu___7 with
                     | (c, uu___8, uu___9, uu___10) -> c < probs.ctr)
                  probs.wl_deferred in
              (match uu___6 with
               | (attempt1, rest) ->
                   let uu___7 =
                     Obj.magic
                       (FStarC_Class_Listlike.view ()
                          (Obj.magic
                             (FStarC_Compiler_CList.listlike_clist ()))
                          (Obj.magic attempt1)) in
                   (match uu___7 with
                    | FStarC_Class_Listlike.VNil ->
                        let uu___8 =
                          let uu___9 = as_deferred probs.wl_deferred in
                          let uu___10 = as_deferred probs.wl_deferred_to_tac in
                          (uu___9, uu___10, (probs.wl_implicits)) in
                        Success uu___8
                    | uu___8 ->
                        let uu___9 =
                          let uu___10 =
                            let uu___11 =
                              FStarC_Class_Listlike.to_list
                                (FStarC_Compiler_CList.listlike_clist ())
                                attempt1 in
                            FStarC_Compiler_List.map
                              (fun uu___12 ->
                                 match uu___12 with
                                 | (uu___13, uu___14, uu___15, y) -> y)
                              uu___11 in
                          {
                            attempting = uu___10;
                            wl_deferred = rest;
                            wl_deferred_to_tac = (probs.wl_deferred_to_tac);
                            ctr = (probs.ctr);
                            defer_ok = (probs.defer_ok);
                            smt_ok = (probs.smt_ok);
                            umax_heuristic_ok = (probs.umax_heuristic_ok);
                            tcenv = (probs.tcenv);
                            wl_implicits = (probs.wl_implicits);
                            repr_subcomp_allowed =
                              (probs.repr_subcomp_allowed);
                            typeclass_variables = (probs.typeclass_variables)
                          } in
                        solve uu___9))))
and (solve_one_universe_eq :
  FStarC_TypeChecker_Common.prob ->
    FStarC_Syntax_Syntax.universe ->
      FStarC_Syntax_Syntax.universe -> worklist -> solution)
  =
  fun orig ->
    fun u1 ->
      fun u2 ->
        fun wl ->
          let uu___ = solve_universe_eq (p_pid orig) wl u1 u2 in
          match uu___ with
          | USolved wl1 ->
              let uu___1 =
                solve_prob orig FStar_Pervasives_Native.None [] wl1 in
              solve uu___1
          | UFailed msg -> giveup wl msg orig
          | UDeferred wl1 ->
              let uu___1 =
                defer_lit FStarC_TypeChecker_Common.Deferred_univ_constraint
                  "" orig wl1 in
              solve uu___1
and (solve_maybe_uinsts :
  FStarC_TypeChecker_Common.prob ->
    FStarC_Syntax_Syntax.term ->
      FStarC_Syntax_Syntax.term -> worklist -> univ_eq_sol)
  =
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
          let env = p_env wl orig in
          FStarC_Defensive.def_check_scoped
            FStarC_TypeChecker_Env.hasBinders_env
            FStarC_Class_Binders.hasNames_term
            FStarC_Syntax_Print.pretty_term t1.FStarC_Syntax_Syntax.pos
            "solve_maybe_uinsts.whnf1" env t1;
          FStarC_Defensive.def_check_scoped
            FStarC_TypeChecker_Env.hasBinders_env
            FStarC_Class_Binders.hasNames_term
            FStarC_Syntax_Print.pretty_term t2.FStarC_Syntax_Syntax.pos
            "solve_maybe_uinsts.whnf2" env t2;
          (let t11 = whnf env t1 in
           let t21 = whnf env t2 in
           match ((t11.FStarC_Syntax_Syntax.n), (t21.FStarC_Syntax_Syntax.n))
           with
           | (FStarC_Syntax_Syntax.Tm_uinst
              ({ FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_fvar f;
                 FStarC_Syntax_Syntax.pos = uu___2;
                 FStarC_Syntax_Syntax.vars = uu___3;
                 FStarC_Syntax_Syntax.hash_code = uu___4;_},
               us1),
              FStarC_Syntax_Syntax.Tm_uinst
              ({ FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_fvar g;
                 FStarC_Syntax_Syntax.pos = uu___5;
                 FStarC_Syntax_Syntax.vars = uu___6;
                 FStarC_Syntax_Syntax.hash_code = uu___7;_},
               us2)) ->
               let b = FStarC_Syntax_Syntax.fv_eq f g in aux wl us1 us2
           | (FStarC_Syntax_Syntax.Tm_uinst uu___2, uu___3) ->
               failwith "Impossible: expect head symbols to match"
           | (uu___2, FStarC_Syntax_Syntax.Tm_uinst uu___3) ->
               failwith "Impossible: expect head symbols to match"
           | uu___2 -> USolved wl)
and (giveup_or_defer :
  FStarC_TypeChecker_Common.prob ->
    worklist ->
      FStarC_TypeChecker_Common.deferred_reason -> lstring -> solution)
  =
  fun orig ->
    fun wl ->
      fun reason ->
        fun msg ->
          if wl.defer_ok = DeferAny
          then
            ((let uu___1 = FStarC_Compiler_Effect.op_Bang dbg_Rel in
              if uu___1
              then
                let uu___2 = prob_to_string wl.tcenv orig in
                let uu___3 = FStarC_Thunk.force msg in
                FStarC_Compiler_Util.print2
                  "\n\t\tDeferring %s\n\t\tBecause %s\n" uu___2 uu___3
              else ());
             (let uu___1 = defer reason msg orig wl in solve uu___1))
          else giveup wl msg orig
and (giveup_or_defer_flex_flex :
  FStarC_TypeChecker_Common.prob ->
    worklist ->
      FStarC_TypeChecker_Common.deferred_reason -> lstring -> solution)
  =
  fun orig ->
    fun wl ->
      fun reason ->
        fun msg ->
          if wl.defer_ok <> NoDefer
          then
            ((let uu___1 = FStarC_Compiler_Effect.op_Bang dbg_Rel in
              if uu___1
              then
                let uu___2 = prob_to_string wl.tcenv orig in
                let uu___3 = FStarC_Thunk.force msg in
                FStarC_Compiler_Util.print2
                  "\n\t\tDeferring %s\n\t\tBecause %s\n" uu___2 uu___3
              else ());
             (let uu___1 = defer reason msg orig wl in solve uu___1))
          else giveup wl msg orig
and (defer_to_user_tac :
  FStarC_TypeChecker_Common.prob -> Prims.string -> worklist -> solution) =
  fun orig ->
    fun reason ->
      fun wl ->
        (let uu___1 = FStarC_Compiler_Effect.op_Bang dbg_Rel in
         if uu___1
         then
           let uu___2 = prob_to_string wl.tcenv orig in
           FStarC_Compiler_Util.print1 "\n\t\tDeferring %s to a tactic\n"
             uu___2
         else ());
        (let wl1 = solve_prob orig FStar_Pervasives_Native.None [] wl in
         let wl2 =
           let uu___1 =
             let uu___2 =
               let uu___3 = FStarC_Thunk.mkv reason in
               ((wl1.ctr), FStarC_TypeChecker_Common.Deferred_to_user_tac,
                 uu___3, orig) in
             Obj.magic
               (FStarC_Class_Listlike.cons ()
                  (Obj.magic (FStarC_Compiler_CList.listlike_clist ()))
                  uu___2 (Obj.magic wl1.wl_deferred_to_tac)) in
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
             repr_subcomp_allowed = (wl1.repr_subcomp_allowed);
             typeclass_variables = (wl1.typeclass_variables)
           } in
         solve wl2)
and (maybe_defer_to_user_tac : tprob -> Prims.string -> worklist -> solution)
  =
  fun prob ->
    fun reason ->
      fun wl ->
        match prob.FStarC_TypeChecker_Common.relation with
        | FStarC_TypeChecker_Common.EQ ->
            let should_defer_tac t =
              let uu___ = FStarC_Syntax_Util.head_and_args t in
              match uu___ with
              | (head, uu___1) ->
                  let uu___2 =
                    let uu___3 = FStarC_Syntax_Subst.compress head in
                    uu___3.FStarC_Syntax_Syntax.n in
                  (match uu___2 with
                   | FStarC_Syntax_Syntax.Tm_uvar (uv, uu___3) ->
                       let uu___4 =
                         FStarC_TypeChecker_DeferredImplicits.should_defer_uvar_to_user_tac
                           wl.tcenv uv in
                       (uu___4, (uv.FStarC_Syntax_Syntax.ctx_uvar_reason))
                   | uu___3 -> (false, "")) in
            let uu___ = should_defer_tac prob.FStarC_TypeChecker_Common.lhs in
            (match uu___ with
             | (l1, r1) ->
                 let uu___1 =
                   should_defer_tac prob.FStarC_TypeChecker_Common.rhs in
                 (match uu___1 with
                  | (l2, r2) ->
                      if l1 || l2
                      then
                        defer_to_user_tac
                          (FStarC_TypeChecker_Common.TProb prob)
                          (Prims.strcat r1 (Prims.strcat ", " r2)) wl
                      else
                        (let uu___3 =
                           defer_lit FStarC_TypeChecker_Common.Deferred_flex
                             reason (FStarC_TypeChecker_Common.TProb prob) wl in
                         solve uu___3)))
        | uu___ ->
            let uu___1 =
              defer_lit FStarC_TypeChecker_Common.Deferred_flex reason
                (FStarC_TypeChecker_Common.TProb prob) wl in
            solve uu___1
and (solve_rigid_flex_or_flex_rigid_subtyping :
  FStarC_TypeChecker_Common.rank_t -> tprob -> worklist -> solution) =
  fun rank1 ->
    fun tp ->
      fun wl ->
        def_check_prob "solve_rigid_flex_or_flex_rigid_subtyping"
          (FStarC_TypeChecker_Common.TProb tp);
        (let flip = rank1 = FStarC_TypeChecker_Common.Flex_rigid in
         let meet_or_join op ts wl1 =
           let eq_prob t1 t2 wl2 =
             let uu___1 =
               new_problem wl2
                 (p_env wl2 (FStarC_TypeChecker_Common.TProb tp)) t1
                 FStarC_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
                 t1.FStarC_Syntax_Syntax.pos "join/meet refinements" in
             match uu___1 with
             | (p, wl3) ->
                 (def_check_prob "meet_or_join"
                    (FStarC_TypeChecker_Common.TProb p);
                  ((FStarC_TypeChecker_Common.TProb p), wl3)) in
           let pairwise t1 t2 wl2 =
             (let uu___2 = FStarC_Compiler_Effect.op_Bang dbg_Rel in
              if uu___2
              then
                let uu___3 =
                  FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t1 in
                let uu___4 =
                  FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t2 in
                FStarC_Compiler_Util.print2
                  "[meet/join]: pairwise: %s and %s\n" uu___3 uu___4
              else ());
             (let uu___2 =
                head_matches_delta
                  (p_env wl2 (FStarC_TypeChecker_Common.TProb tp))
                  tp.FStarC_TypeChecker_Common.logical wl2.smt_ok t1 t2 in
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
                             let uu___4 = FStarC_Syntax_Subst.compress t11 in
                             let uu___5 = FStarC_Syntax_Subst.compress t21 in
                             (uu___4, uu___5)
                         | FStar_Pervasives_Native.None ->
                             let uu___4 = FStarC_Syntax_Subst.compress t1 in
                             let uu___5 = FStarC_Syntax_Subst.compress t2 in
                             (uu___4, uu___5) in
                       (match uu___3 with
                        | (t11, t21) ->
                            let try_eq t12 t22 wl3 =
                              let uu___4 =
                                FStarC_Syntax_Util.head_and_args t12 in
                              match uu___4 with
                              | (t1_hd, t1_args) ->
                                  let uu___5 =
                                    FStarC_Syntax_Util.head_and_args t22 in
                                  (match uu___5 with
                                   | (t2_hd, t2_args) ->
                                       if
                                         (FStarC_Compiler_List.length t1_args)
                                           <>
                                           (FStarC_Compiler_List.length
                                              t2_args)
                                       then FStar_Pervasives_Native.None
                                       else
                                         (let uu___7 =
                                            let uu___8 =
                                              let uu___9 =
                                                FStarC_Syntax_Syntax.as_arg
                                                  t1_hd in
                                              uu___9 :: t1_args in
                                            let uu___9 =
                                              let uu___10 =
                                                FStarC_Syntax_Syntax.as_arg
                                                  t2_hd in
                                              uu___10 :: t2_args in
                                            FStarC_Compiler_List.fold_left2
                                              (fun uu___10 ->
                                                 fun uu___11 ->
                                                   fun uu___12 ->
                                                     match (uu___10, uu___11,
                                                             uu___12)
                                                     with
                                                     | ((probs, wl4),
                                                        (a1, uu___13),
                                                        (a2, uu___14)) ->
                                                         let uu___15 =
                                                           eq_prob a1 a2 wl4 in
                                                         (match uu___15 with
                                                          | (p, wl5) ->
                                                              ((p :: probs),
                                                                wl5)))
                                              ([], wl3) uu___8 uu___9 in
                                          match uu___7 with
                                          | (probs, wl4) ->
                                              let wl' =
                                                {
                                                  attempting = probs;
                                                  wl_deferred =
                                                    (Obj.magic
                                                       (FStarC_Class_Listlike.empty
                                                          ()
                                                          (Obj.magic
                                                             (FStarC_Compiler_CList.listlike_clist
                                                                ()))));
                                                  wl_deferred_to_tac =
                                                    (wl4.wl_deferred_to_tac);
                                                  ctr = (wl4.ctr);
                                                  defer_ok = NoDefer;
                                                  smt_ok = false;
                                                  umax_heuristic_ok =
                                                    (wl4.umax_heuristic_ok);
                                                  tcenv = (wl4.tcenv);
                                                  wl_implicits =
                                                    (Obj.magic
                                                       (FStarC_Class_Listlike.empty
                                                          ()
                                                          (Obj.magic
                                                             (FStarC_Compiler_CList.listlike_clist
                                                                ()))));
                                                  repr_subcomp_allowed =
                                                    (wl4.repr_subcomp_allowed);
                                                  typeclass_variables =
                                                    (wl4.typeclass_variables)
                                                } in
                                              let tx =
                                                FStarC_Syntax_Unionfind.new_transaction
                                                  () in
                                              let uu___8 = solve wl' in
                                              (match uu___8 with
                                               | Success
                                                   (uu___9, defer_to_tac,
                                                    imps)
                                                   ->
                                                   (FStarC_Syntax_Unionfind.commit
                                                      tx;
                                                    (let uu___11 =
                                                       extend_wl wl4
                                                         (Obj.magic
                                                            (FStarC_Class_Listlike.empty
                                                               ()
                                                               (Obj.magic
                                                                  (FStarC_Compiler_CList.listlike_clist
                                                                    ()))))
                                                         defer_to_tac imps in
                                                     FStar_Pervasives_Native.Some
                                                       uu___11))
                                               | Failed uu___9 ->
                                                   (FStarC_Syntax_Unionfind.rollback
                                                      tx;
                                                    FStar_Pervasives_Native.None)))) in
                            let combine t12 t22 wl3 =
                              let env =
                                p_env wl3
                                  (FStarC_TypeChecker_Common.TProb tp) in
                              let uu___4 =
                                base_and_refinement_maybe_delta false env t12 in
                              match uu___4 with
                              | (t1_base, p1_opt) ->
                                  let uu___5 =
                                    base_and_refinement_maybe_delta false env
                                      t22 in
                                  (match uu___5 with
                                   | (t2_base, p2_opt) ->
                                       let apply_op env1 op1 phi1 phi2 =
                                         let squash phi =
                                           let uu___6 =
                                             env1.FStarC_TypeChecker_Env.universe_of
                                               env1 phi in
                                           match uu___6 with
                                           | FStarC_Syntax_Syntax.U_zero ->
                                               phi
                                           | u ->
                                               FStarC_Syntax_Util.mk_squash u
                                                 phi in
                                         let uu___6 = squash phi1 in
                                         let uu___7 = squash phi2 in
                                         op1 uu___6 uu___7 in
                                       let combine_refinements t_base p1_opt1
                                         p2_opt1 =
                                         match op with
                                         | FStar_Pervasives_Native.None ->
                                             t_base
                                         | FStar_Pervasives_Native.Some op1
                                             ->
                                             let refine x t =
                                               let uu___6 =
                                                 FStarC_Syntax_Util.is_t_true
                                                   t in
                                               if uu___6
                                               then
                                                 x.FStarC_Syntax_Syntax.sort
                                               else
                                                 FStarC_Syntax_Util.refine x
                                                   t in
                                             (match (p1_opt1, p2_opt1) with
                                              | (FStar_Pervasives_Native.Some
                                                 (x, phi1),
                                                 FStar_Pervasives_Native.Some
                                                 (y, phi2)) ->
                                                  let x1 =
                                                    FStarC_Syntax_Syntax.freshen_bv
                                                      x in
                                                  let subst =
                                                    [FStarC_Syntax_Syntax.DB
                                                       (Prims.int_zero, x1)] in
                                                  let phi11 =
                                                    FStarC_Syntax_Subst.subst
                                                      subst phi1 in
                                                  let phi21 =
                                                    FStarC_Syntax_Subst.subst
                                                      subst phi2 in
                                                  let env_x =
                                                    FStarC_TypeChecker_Env.push_bv
                                                      env x1 in
                                                  let uu___6 =
                                                    apply_op env_x op1 phi11
                                                      phi21 in
                                                  refine x1 uu___6
                                              | (FStar_Pervasives_Native.None,
                                                 FStar_Pervasives_Native.Some
                                                 (x, phi)) ->
                                                  let x1 =
                                                    FStarC_Syntax_Syntax.freshen_bv
                                                      x in
                                                  let subst =
                                                    [FStarC_Syntax_Syntax.DB
                                                       (Prims.int_zero, x1)] in
                                                  let phi1 =
                                                    FStarC_Syntax_Subst.subst
                                                      subst phi in
                                                  let env_x =
                                                    FStarC_TypeChecker_Env.push_bv
                                                      env x1 in
                                                  let uu___6 =
                                                    apply_op env_x op1
                                                      FStarC_Syntax_Util.t_true
                                                      phi1 in
                                                  refine x1 uu___6
                                              | (FStar_Pervasives_Native.Some
                                                 (x, phi),
                                                 FStar_Pervasives_Native.None)
                                                  ->
                                                  let x1 =
                                                    FStarC_Syntax_Syntax.freshen_bv
                                                      x in
                                                  let subst =
                                                    [FStarC_Syntax_Syntax.DB
                                                       (Prims.int_zero, x1)] in
                                                  let phi1 =
                                                    FStarC_Syntax_Subst.subst
                                                      subst phi in
                                                  let env_x =
                                                    FStarC_TypeChecker_Env.push_bv
                                                      env x1 in
                                                  let uu___6 =
                                                    apply_op env_x op1
                                                      FStarC_Syntax_Util.t_true
                                                      phi1 in
                                                  refine x1 uu___6
                                              | uu___6 -> t_base) in
                                       let uu___6 =
                                         try_eq t1_base t2_base wl3 in
                                       (match uu___6 with
                                        | FStar_Pervasives_Native.Some wl4 ->
                                            let uu___7 =
                                              combine_refinements t1_base
                                                p1_opt p2_opt in
                                            (uu___7, [], wl4)
                                        | FStar_Pervasives_Native.None ->
                                            let uu___7 =
                                              base_and_refinement_maybe_delta
                                                true env t12 in
                                            (match uu___7 with
                                             | (t1_base1, p1_opt1) ->
                                                 let uu___8 =
                                                   base_and_refinement_maybe_delta
                                                     true env t22 in
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
                                     FStarC_Compiler_Effect.op_Bang dbg_Rel in
                                   if uu___6
                                   then
                                     let uu___7 =
                                       FStarC_Class_Show.show
                                         FStarC_Syntax_Print.showable_term
                                         t12 in
                                     FStarC_Compiler_Util.print1
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
                               (FStarC_Compiler_List.op_At probs probs'),
                               wl3) ts2)) in
           let uu___1 =
             let uu___2 = FStarC_Compiler_List.hd ts in (uu___2, [], wl1) in
           let uu___2 = FStarC_Compiler_List.tl ts in aux uu___1 uu___2 in
         let uu___1 =
           if flip
           then
             ((tp.FStarC_TypeChecker_Common.lhs),
               (tp.FStarC_TypeChecker_Common.rhs))
           else
             ((tp.FStarC_TypeChecker_Common.rhs),
               (tp.FStarC_TypeChecker_Common.lhs)) in
         match uu___1 with
         | (this_flex, this_rigid) ->
             let uu___2 =
               let uu___3 = FStarC_Syntax_Subst.compress this_rigid in
               uu___3.FStarC_Syntax_Syntax.n in
             (match uu___2 with
              | FStarC_Syntax_Syntax.Tm_arrow
                  { FStarC_Syntax_Syntax.bs1 = _bs;
                    FStarC_Syntax_Syntax.comp = comp;_}
                  ->
                  let uu___3 = FStarC_Syntax_Util.is_tot_or_gtot_comp comp in
                  if uu___3
                  then
                    let uu___4 = destruct_flex_t this_flex wl in
                    (match uu___4 with
                     | (flex, wl1) ->
                         let uu___5 = quasi_pattern wl1.tcenv flex in
                         (match uu___5 with
                          | FStar_Pervasives_Native.None ->
                              giveup_lit wl1
                                "flex-arrow subtyping, not a quasi pattern"
                                (FStarC_TypeChecker_Common.TProb tp)
                          | FStar_Pervasives_Native.Some (flex_bs, flex_t1)
                              ->
                              ((let uu___7 =
                                  FStarC_Compiler_Effect.op_Bang dbg_Rel in
                                if uu___7
                                then
                                  let uu___8 =
                                    FStarC_Compiler_Util.string_of_int
                                      tp.FStarC_TypeChecker_Common.pid in
                                  FStarC_Compiler_Util.print1
                                    "Trying to solve by imitating arrow:%s\n"
                                    uu___8
                                else ());
                               imitate_arrow
                                 (FStarC_TypeChecker_Common.TProb tp) wl1
                                 flex flex_bs flex_t1
                                 tp.FStarC_TypeChecker_Common.relation
                                 this_rigid)))
                  else
                    (let uu___5 =
                       attempt
                         [FStarC_TypeChecker_Common.TProb
                            {
                              FStarC_TypeChecker_Common.pid =
                                (tp.FStarC_TypeChecker_Common.pid);
                              FStarC_TypeChecker_Common.lhs =
                                (tp.FStarC_TypeChecker_Common.lhs);
                              FStarC_TypeChecker_Common.relation =
                                FStarC_TypeChecker_Common.EQ;
                              FStarC_TypeChecker_Common.rhs =
                                (tp.FStarC_TypeChecker_Common.rhs);
                              FStarC_TypeChecker_Common.element =
                                (tp.FStarC_TypeChecker_Common.element);
                              FStarC_TypeChecker_Common.logical_guard =
                                (tp.FStarC_TypeChecker_Common.logical_guard);
                              FStarC_TypeChecker_Common.logical_guard_uvar =
                                (tp.FStarC_TypeChecker_Common.logical_guard_uvar);
                              FStarC_TypeChecker_Common.reason =
                                (tp.FStarC_TypeChecker_Common.reason);
                              FStarC_TypeChecker_Common.loc =
                                (tp.FStarC_TypeChecker_Common.loc);
                              FStarC_TypeChecker_Common.rank =
                                (tp.FStarC_TypeChecker_Common.rank);
                              FStarC_TypeChecker_Common.logical =
                                (tp.FStarC_TypeChecker_Common.logical)
                            }] wl in
                     solve uu___5)
              | uu___3 ->
                  ((let uu___5 = FStarC_Compiler_Effect.op_Bang dbg_Rel in
                    if uu___5
                    then
                      let uu___6 =
                        FStarC_Class_Show.show FStarC_Class_Show.showable_int
                          tp.FStarC_TypeChecker_Common.pid in
                      FStarC_Compiler_Util.print1
                        "Trying to solve by meeting refinements:%s\n" uu___6
                    else ());
                   (let uu___5 = FStarC_Syntax_Util.head_and_args this_flex in
                    match uu___5 with
                    | (u, _args) ->
                        let env =
                          p_env wl (FStarC_TypeChecker_Common.TProb tp) in
                        let uu___6 =
                          let uu___7 = FStarC_Syntax_Subst.compress u in
                          uu___7.FStarC_Syntax_Syntax.n in
                        (match uu___6 with
                         | FStarC_Syntax_Syntax.Tm_uvar (ctx_uvar, _subst) ->
                             let equiv t =
                               let uu___7 =
                                 FStarC_Syntax_Util.head_and_args t in
                               match uu___7 with
                               | (u', uu___8) ->
                                   let uu___9 =
                                     let uu___10 = whnf env u' in
                                     uu___10.FStarC_Syntax_Syntax.n in
                                   (match uu___9 with
                                    | FStarC_Syntax_Syntax.Tm_uvar
                                        (ctx_uvar', _subst') ->
                                        FStarC_Syntax_Unionfind.equiv
                                          ctx_uvar.FStarC_Syntax_Syntax.ctx_uvar_head
                                          ctx_uvar'.FStarC_Syntax_Syntax.ctx_uvar_head
                                    | uu___10 -> false) in
                             let uu___7 =
                               FStarC_Compiler_List.partition
                                 (fun uu___8 ->
                                    match uu___8 with
                                    | FStarC_TypeChecker_Common.TProb tp1 ->
                                        let tp2 = maybe_invert tp1 in
                                        (match tp2.FStarC_TypeChecker_Common.rank
                                         with
                                         | FStar_Pervasives_Native.Some rank'
                                             when rank1 = rank' ->
                                             if flip
                                             then
                                               equiv
                                                 tp2.FStarC_TypeChecker_Common.lhs
                                             else
                                               equiv
                                                 tp2.FStarC_TypeChecker_Common.rhs
                                         | uu___9 -> false)
                                    | uu___9 -> false) wl.attempting in
                             (match uu___7 with
                              | (bounds_probs, rest) ->
                                  let bounds_typs =
                                    let uu___8 = whnf env this_rigid in
                                    let uu___9 =
                                      FStarC_Compiler_List.collect
                                        (fun uu___10 ->
                                           match uu___10 with
                                           | FStarC_TypeChecker_Common.TProb
                                               p ->
                                               let uu___11 =
                                                 if flip
                                                 then
                                                   whnf env
                                                     (maybe_invert p).FStarC_TypeChecker_Common.rhs
                                                 else
                                                   whnf env
                                                     (maybe_invert p).FStarC_TypeChecker_Common.lhs in
                                               [uu___11]
                                           | uu___11 -> []) bounds_probs in
                                    uu___8 :: uu___9 in
                                  let uu___8 =
                                    let uu___9 =
                                      (has_typeclass_constraint ctx_uvar wl)
                                        && (Prims.op_Negation flip) in
                                    if uu___9
                                    then (true, FStar_Pervasives_Native.None)
                                    else
                                      (false,
                                        (FStar_Pervasives_Native.Some
                                           (if flip
                                            then
                                              FStarC_Syntax_Util.mk_conj_simp
                                            else
                                              FStarC_Syntax_Util.mk_disj_simp))) in
                                  (match uu___8 with
                                   | (widen, meet_or_join_op) ->
                                       let uu___9 =
                                         match bounds_typs with
                                         | t::[] ->
                                             if widen
                                             then
                                               let uu___10 =
                                                 let uu___11 =
                                                   base_and_refinement_maybe_delta
                                                     false env t in
                                                 FStar_Pervasives_Native.fst
                                                   uu___11 in
                                               (uu___10, [], wl)
                                             else (t, [], wl)
                                         | uu___10 ->
                                             meet_or_join meet_or_join_op
                                               bounds_typs wl in
                                       (match uu___9 with
                                        | (bound, sub_probs, wl1) ->
                                            let uu___10 =
                                              let flex_u =
                                                flex_uvar_head this_flex in
                                              let bound1 =
                                                let uu___11 =
                                                  let uu___12 =
                                                    FStarC_Syntax_Subst.compress
                                                      bound in
                                                  uu___12.FStarC_Syntax_Syntax.n in
                                                match uu___11 with
                                                | FStarC_Syntax_Syntax.Tm_refine
                                                    {
                                                      FStarC_Syntax_Syntax.b
                                                        = x;
                                                      FStarC_Syntax_Syntax.phi
                                                        = phi;_}
                                                    when
                                                    (tp.FStarC_TypeChecker_Common.relation
                                                       =
                                                       FStarC_TypeChecker_Common.SUB)
                                                      &&
                                                      (let uu___12 =
                                                         occurs flex_u
                                                           x.FStarC_Syntax_Syntax.sort in
                                                       FStar_Pervasives_Native.snd
                                                         uu___12)
                                                    ->
                                                    x.FStarC_Syntax_Syntax.sort
                                                | uu___12 -> bound in
                                              let uu___11 =
                                                new_problem wl1
                                                  (p_env wl1
                                                     (FStarC_TypeChecker_Common.TProb
                                                        tp)) bound1
                                                  FStarC_TypeChecker_Common.EQ
                                                  this_flex
                                                  FStar_Pervasives_Native.None
                                                  tp.FStarC_TypeChecker_Common.loc
                                                  (if flip
                                                   then "joining refinements"
                                                   else "meeting refinements") in
                                              (bound1, uu___11) in
                                            (match uu___10 with
                                             | (bound_typ, (eq_prob, wl')) ->
                                                 (def_check_prob
                                                    "meet_or_join2"
                                                    (FStarC_TypeChecker_Common.TProb
                                                       eq_prob);
                                                  (let uu___13 =
                                                     FStarC_Compiler_Effect.op_Bang
                                                       dbg_Rel in
                                                   if uu___13
                                                   then
                                                     let wl'1 =
                                                       {
                                                         attempting =
                                                           ((FStarC_TypeChecker_Common.TProb
                                                               eq_prob) ::
                                                           sub_probs);
                                                         wl_deferred =
                                                           (wl1.wl_deferred);
                                                         wl_deferred_to_tac =
                                                           (wl1.wl_deferred_to_tac);
                                                         ctr = (wl1.ctr);
                                                         defer_ok =
                                                           (wl1.defer_ok);
                                                         smt_ok =
                                                           (wl1.smt_ok);
                                                         umax_heuristic_ok =
                                                           (wl1.umax_heuristic_ok);
                                                         tcenv = (wl1.tcenv);
                                                         wl_implicits =
                                                           (wl1.wl_implicits);
                                                         repr_subcomp_allowed
                                                           =
                                                           (wl1.repr_subcomp_allowed);
                                                         typeclass_variables
                                                           =
                                                           (wl1.typeclass_variables)
                                                       } in
                                                     let uu___14 =
                                                       wl_to_string wl'1 in
                                                     FStarC_Compiler_Util.print1
                                                       "After meet/join refinements: %s\n"
                                                       uu___14
                                                   else ());
                                                  (let tx =
                                                     FStarC_Syntax_Unionfind.new_transaction
                                                       () in
                                                   FStarC_Compiler_List.iter
                                                     (def_check_prob
                                                        "meet_or_join3_sub")
                                                     sub_probs;
                                                   (let uu___14 =
                                                      solve_t eq_prob
                                                        {
                                                          attempting =
                                                            sub_probs;
                                                          wl_deferred =
                                                            (Obj.magic
                                                               (FStarC_Class_Listlike.empty
                                                                  ()
                                                                  (Obj.magic
                                                                    (FStarC_Compiler_CList.listlike_clist
                                                                    ()))));
                                                          wl_deferred_to_tac
                                                            =
                                                            (wl'.wl_deferred_to_tac);
                                                          ctr = (wl'.ctr);
                                                          defer_ok = NoDefer;
                                                          smt_ok =
                                                            (wl'.smt_ok);
                                                          umax_heuristic_ok =
                                                            (wl'.umax_heuristic_ok);
                                                          tcenv = (wl'.tcenv);
                                                          wl_implicits =
                                                            (Obj.magic
                                                               (FStarC_Class_Listlike.empty
                                                                  ()
                                                                  (Obj.magic
                                                                    (FStarC_Compiler_CList.listlike_clist
                                                                    ()))));
                                                          repr_subcomp_allowed
                                                            =
                                                            (wl'.repr_subcomp_allowed);
                                                          typeclass_variables
                                                            =
                                                            (wl'.typeclass_variables)
                                                        } in
                                                    match uu___14 with
                                                    | Success
                                                        (uu___15,
                                                         defer_to_tac, imps)
                                                        ->
                                                        let wl2 =
                                                          {
                                                            attempting = rest;
                                                            wl_deferred =
                                                              (wl'.wl_deferred);
                                                            wl_deferred_to_tac
                                                              =
                                                              (wl'.wl_deferred_to_tac);
                                                            ctr = (wl'.ctr);
                                                            defer_ok =
                                                              (wl'.defer_ok);
                                                            smt_ok =
                                                              (wl'.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (wl'.umax_heuristic_ok);
                                                            tcenv =
                                                              (wl'.tcenv);
                                                            wl_implicits =
                                                              (wl'.wl_implicits);
                                                            repr_subcomp_allowed
                                                              =
                                                              (wl'.repr_subcomp_allowed);
                                                            typeclass_variables
                                                              =
                                                              (wl'.typeclass_variables)
                                                          } in
                                                        let wl3 =
                                                          extend_wl wl2
                                                            (Obj.magic
                                                               (FStarC_Class_Listlike.empty
                                                                  ()
                                                                  (Obj.magic
                                                                    (FStarC_Compiler_CList.listlike_clist
                                                                    ()))))
                                                            defer_to_tac imps in
                                                        let g =
                                                          FStarC_Compiler_List.fold_left
                                                            (fun g1 ->
                                                               fun p ->
                                                                 FStarC_Syntax_Util.mk_conj
                                                                   g1
                                                                   (p_guard p))
                                                            eq_prob.FStarC_TypeChecker_Common.logical_guard
                                                            sub_probs in
                                                        let wl4 =
                                                          solve_prob' false
                                                            (FStarC_TypeChecker_Common.TProb
                                                               tp)
                                                            (FStar_Pervasives_Native.Some
                                                               g) [] wl3 in
                                                        let uu___16 =
                                                          FStarC_Compiler_List.fold_left
                                                            (fun wl5 ->
                                                               fun p ->
                                                                 solve_prob'
                                                                   true p
                                                                   FStar_Pervasives_Native.None
                                                                   [] wl5)
                                                            wl4 bounds_probs in
                                                        (FStarC_Syntax_Unionfind.commit
                                                           tx;
                                                         solve wl4)
                                                    | Failed (p, msg) ->
                                                        ((let uu___16 =
                                                            FStarC_Compiler_Effect.op_Bang
                                                              dbg_Rel in
                                                          if uu___16
                                                          then
                                                            let uu___17 =
                                                              let uu___18 =
                                                                FStarC_Compiler_List.map
                                                                  (prob_to_string
                                                                    env)
                                                                  ((FStarC_TypeChecker_Common.TProb
                                                                    eq_prob)
                                                                  ::
                                                                  sub_probs) in
                                                              FStarC_Compiler_String.concat
                                                                "\n" uu___18 in
                                                            FStarC_Compiler_Util.print1
                                                              "meet/join attempted and failed to solve problems:\n%s\n"
                                                              uu___17
                                                          else ());
                                                         (let uu___16 =
                                                            let uu___17 =
                                                              base_and_refinement
                                                                env bound_typ in
                                                            (rank1, uu___17) in
                                                          match uu___16 with
                                                          | (FStarC_TypeChecker_Common.Rigid_flex,
                                                             (t_base,
                                                              FStar_Pervasives_Native.Some
                                                              uu___17)) ->
                                                              (FStarC_Syntax_Unionfind.rollback
                                                                 tx;
                                                               (let uu___19 =
                                                                  new_problem
                                                                    wl1
                                                                    (
                                                                    p_env wl1
                                                                    (FStarC_TypeChecker_Common.TProb
                                                                    tp))
                                                                    t_base
                                                                    FStarC_TypeChecker_Common.EQ
                                                                    this_flex
                                                                    FStar_Pervasives_Native.None
                                                                    tp.FStarC_TypeChecker_Common.loc
                                                                    "widened subtyping" in
                                                                match uu___19
                                                                with
                                                                | (eq_prob1,
                                                                   wl2) ->
                                                                    (
                                                                    def_check_prob
                                                                    "meet_or_join3"
                                                                    (FStarC_TypeChecker_Common.TProb
                                                                    eq_prob1);
                                                                    (
                                                                    let wl3 =
                                                                    solve_prob'
                                                                    false
                                                                    (FStarC_TypeChecker_Common.TProb
                                                                    tp)
                                                                    (FStar_Pervasives_Native.Some
                                                                    (p_guard
                                                                    (FStarC_TypeChecker_Common.TProb
                                                                    eq_prob1)))
                                                                    [] wl2 in
                                                                    let uu___21
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStarC_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3 in
                                                                    solve
                                                                    uu___21))))
                                                          | (FStarC_TypeChecker_Common.Flex_rigid,
                                                             (t_base,
                                                              FStar_Pervasives_Native.Some
                                                              (x, phi))) ->
                                                              (FStarC_Syntax_Unionfind.rollback
                                                                 tx;
                                                               (let x1 =
                                                                  FStarC_Syntax_Syntax.freshen_bv
                                                                    x in
                                                                let uu___18 =
                                                                  let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    FStarC_Syntax_Syntax.mk_binder
                                                                    x1 in
                                                                    [uu___20] in
                                                                  FStarC_Syntax_Subst.open_term
                                                                    uu___19
                                                                    phi in
                                                                match uu___18
                                                                with
                                                                | (uu___19,
                                                                   phi1) ->
                                                                    let uu___20
                                                                    =
                                                                    new_problem
                                                                    wl1 env
                                                                    t_base
                                                                    FStarC_TypeChecker_Common.EQ
                                                                    this_flex
                                                                    FStar_Pervasives_Native.None
                                                                    tp.FStarC_TypeChecker_Common.loc
                                                                    "widened subtyping" in
                                                                    (match uu___20
                                                                    with
                                                                    | 
                                                                    (eq_prob1,
                                                                    wl2) ->
                                                                    (def_check_prob
                                                                    "meet_or_join4"
                                                                    (FStarC_TypeChecker_Common.TProb
                                                                    eq_prob1);
                                                                    (let phi2
                                                                    =
                                                                    guard_on_element
                                                                    wl2 tp x1
                                                                    phi1 in
                                                                    let wl3 =
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    FStarC_Syntax_Util.mk_conj
                                                                    phi2
                                                                    (p_guard
                                                                    (FStarC_TypeChecker_Common.TProb
                                                                    eq_prob1)) in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___23 in
                                                                    solve_prob'
                                                                    false
                                                                    (FStarC_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu___22
                                                                    [] wl2 in
                                                                    let uu___22
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStarC_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3 in
                                                                    solve
                                                                    uu___22)))))
                                                          | uu___17 ->
                                                              let uu___18 =
                                                                FStarC_Thunk.map
                                                                  (fun s ->
                                                                    Prims.strcat
                                                                    "failed to solve the sub-problems: "
                                                                    s) msg in
                                                              giveup wl1
                                                                uu___18 p)))))))))
                         | uu___7 when flip ->
                             let uu___8 =
                               let uu___9 =
                                 FStarC_Compiler_Util.string_of_int
                                   (rank_t_num rank1) in
                               let uu___10 =
                                 prob_to_string env
                                   (FStarC_TypeChecker_Common.TProb tp) in
                               FStarC_Compiler_Util.format2
                                 "Impossible: (rank=%s) Not a flex-rigid: %s"
                                 uu___9 uu___10 in
                             failwith uu___8
                         | uu___7 ->
                             let uu___8 =
                               let uu___9 =
                                 FStarC_Compiler_Util.string_of_int
                                   (rank_t_num rank1) in
                               let uu___10 =
                                 prob_to_string env
                                   (FStarC_TypeChecker_Common.TProb tp) in
                               FStarC_Compiler_Util.format2
                                 "Impossible: (rank=%s) Not a rigid-flex: %s"
                                 uu___9 uu___10 in
                             failwith uu___8)))))
and (imitate_arrow :
  FStarC_TypeChecker_Common.prob ->
    worklist ->
      flex_t ->
        FStarC_Syntax_Syntax.binders ->
          FStarC_Syntax_Syntax.term ->
            FStarC_TypeChecker_Common.rel ->
              FStarC_Syntax_Syntax.term -> solution)
  =
  fun orig ->
    fun wl ->
      fun lhs ->
        fun bs_lhs ->
          fun t_res_lhs ->
            fun rel ->
              fun arrow ->
                let bs_lhs_args =
                  FStarC_Compiler_List.map
                    (fun uu___ ->
                       match uu___ with
                       | { FStarC_Syntax_Syntax.binder_bv = x;
                           FStarC_Syntax_Syntax.binder_qual = i;
                           FStarC_Syntax_Syntax.binder_positivity = uu___1;
                           FStarC_Syntax_Syntax.binder_attrs = uu___2;_} ->
                           let uu___3 = FStarC_Syntax_Syntax.bv_to_name x in
                           (uu___3, i)) bs_lhs in
                let uu___ = lhs in
                match uu___ with
                | Flex (uu___1, u_lhs, uu___2) ->
                    let imitate_comp bs bs_terms c wl1 =
                      let imitate_tot_or_gtot t f wl2 =
                        let uu___3 = FStarC_Syntax_Util.type_u () in
                        match uu___3 with
                        | (k, uu___4) ->
                            let uu___5 =
                              copy_uvar u_lhs
                                (FStarC_Compiler_List.op_At bs_lhs bs) k wl2 in
                            (match uu___5 with
                             | (uu___6, u, wl3) ->
                                 let uu___7 = f u in (uu___7, wl3)) in
                      match c.FStarC_Syntax_Syntax.n with
                      | FStarC_Syntax_Syntax.Total t ->
                          imitate_tot_or_gtot t FStarC_Syntax_Syntax.mk_Total
                            wl1
                      | FStarC_Syntax_Syntax.GTotal t ->
                          imitate_tot_or_gtot t
                            FStarC_Syntax_Syntax.mk_GTotal wl1
                      | FStarC_Syntax_Syntax.Comp ct ->
                          let uu___3 =
                            let uu___4 =
                              let uu___5 =
                                FStarC_Syntax_Syntax.as_arg
                                  ct.FStarC_Syntax_Syntax.result_typ in
                              uu___5 :: (ct.FStarC_Syntax_Syntax.effect_args) in
                            FStarC_Compiler_List.fold_right
                              (fun uu___5 ->
                                 fun uu___6 ->
                                   match (uu___5, uu___6) with
                                   | ((a, i), (out_args, wl2)) ->
                                       let uu___7 =
                                         let uu___8 =
                                           let uu___9 =
                                             FStarC_Syntax_Util.type_u () in
                                           FStar_Pervasives_Native.fst uu___9 in
                                         copy_uvar u_lhs [] uu___8 wl2 in
                                       (match uu___7 with
                                        | (uu___8, t_a, wl3) ->
                                            let uu___9 =
                                              copy_uvar u_lhs bs t_a wl3 in
                                            (match uu___9 with
                                             | (uu___10, a', wl4) ->
                                                 (((a', i) :: out_args), wl4))))
                              uu___4 ([], wl1) in
                          (match uu___3 with
                           | (out_args, wl2) ->
                               let nodec flags =
                                 FStarC_Compiler_List.filter
                                   (fun uu___4 ->
                                      match uu___4 with
                                      | FStarC_Syntax_Syntax.DECREASES uu___5
                                          -> false
                                      | uu___5 -> true) flags in
                               let ct' =
                                 let uu___4 =
                                   let uu___5 =
                                     FStarC_Compiler_List.hd out_args in
                                   FStar_Pervasives_Native.fst uu___5 in
                                 let uu___5 =
                                   FStarC_Compiler_List.tl out_args in
                                 let uu___6 =
                                   nodec ct.FStarC_Syntax_Syntax.flags in
                                 {
                                   FStarC_Syntax_Syntax.comp_univs =
                                     (ct.FStarC_Syntax_Syntax.comp_univs);
                                   FStarC_Syntax_Syntax.effect_name =
                                     (ct.FStarC_Syntax_Syntax.effect_name);
                                   FStarC_Syntax_Syntax.result_typ = uu___4;
                                   FStarC_Syntax_Syntax.effect_args = uu___5;
                                   FStarC_Syntax_Syntax.flags = uu___6
                                 } in
                               ({
                                  FStarC_Syntax_Syntax.n =
                                    (FStarC_Syntax_Syntax.Comp ct');
                                  FStarC_Syntax_Syntax.pos =
                                    (c.FStarC_Syntax_Syntax.pos);
                                  FStarC_Syntax_Syntax.vars =
                                    (c.FStarC_Syntax_Syntax.vars);
                                  FStarC_Syntax_Syntax.hash_code =
                                    (c.FStarC_Syntax_Syntax.hash_code)
                                }, wl2)) in
                    let uu___3 = FStarC_Syntax_Util.arrow_formals_comp arrow in
                    (match uu___3 with
                     | (formals, c) ->
                         let rec aux bs bs_terms formals1 wl1 =
                           match formals1 with
                           | [] ->
                               let uu___4 = imitate_comp bs bs_terms c wl1 in
                               (match uu___4 with
                                | (c', wl2) ->
                                    let lhs' = FStarC_Syntax_Util.arrow bs c' in
                                    let sol =
                                      let uu___5 =
                                        let uu___6 =
                                          FStarC_Syntax_Util.abs bs_lhs lhs'
                                            (FStar_Pervasives_Native.Some
                                               (FStarC_Syntax_Util.residual_tot
                                                  t_res_lhs)) in
                                        (u_lhs, uu___6) in
                                      TERM uu___5 in
                                    let uu___5 =
                                      mk_t_problem wl2 [] orig lhs' rel arrow
                                        FStar_Pervasives_Native.None
                                        "arrow imitation" in
                                    (match uu___5 with
                                     | (sub_prob, wl3) ->
                                         let uu___6 =
                                           let uu___7 =
                                             solve_prob orig
                                               FStar_Pervasives_Native.None
                                               [sol] wl3 in
                                           attempt [sub_prob] uu___7 in
                                         solve uu___6))
                           | { FStarC_Syntax_Syntax.binder_bv = x;
                               FStarC_Syntax_Syntax.binder_qual = imp;
                               FStarC_Syntax_Syntax.binder_positivity = pqual;
                               FStarC_Syntax_Syntax.binder_attrs = attrs;_}::formals2
                               ->
                               let uu___4 =
                                 let uu___5 =
                                   let uu___6 = FStarC_Syntax_Util.type_u () in
                                   FStar_Pervasives_Native.fst uu___6 in
                                 copy_uvar u_lhs
                                   (FStarC_Compiler_List.op_At bs_lhs bs)
                                   uu___5 wl1 in
                               (match uu___4 with
                                | (_ctx_u_x, u_x, wl2) ->
                                    let y =
                                      let uu___5 =
                                        let uu___6 =
                                          FStarC_Syntax_Syntax.range_of_bv x in
                                        FStar_Pervasives_Native.Some uu___6 in
                                      FStarC_Syntax_Syntax.new_bv uu___5 u_x in
                                    let b =
                                      FStarC_Syntax_Syntax.mk_binder_with_attrs
                                        y imp pqual attrs in
                                    let uu___5 =
                                      let uu___6 =
                                        let uu___7 =
                                          FStarC_Syntax_Util.arg_of_non_null_binder
                                            b in
                                        [uu___7] in
                                      FStarC_Compiler_List.op_At bs_terms
                                        uu___6 in
                                    aux (FStarC_Compiler_List.op_At bs [b])
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
                                         FStarC_Compiler_Option.get msg in
                                       Prims.strcat "occurs-check failed: "
                                         uu___8) in
                                giveup_or_defer orig wl
                                  FStarC_TypeChecker_Common.Deferred_occur_check_failed
                                  uu___6
                              else aux [] [] formals wl))
and (solve_binders :
  FStarC_Syntax_Syntax.binders ->
    FStarC_Syntax_Syntax.binders ->
      FStarC_TypeChecker_Common.prob ->
        worklist ->
          (worklist ->
             FStarC_Syntax_Syntax.binders ->
               FStarC_Syntax_Syntax.subst_elt Prims.list ->
                 (FStarC_TypeChecker_Common.prob * worklist))
            -> solution)
  =
  fun bs1 ->
    fun bs2 ->
      fun orig ->
        fun wl ->
          fun rhs ->
            (let uu___1 = FStarC_Compiler_Effect.op_Bang dbg_Rel in
             if uu___1
             then
               let uu___2 =
                 FStarC_Class_Show.show
                   (FStarC_Class_Show.show_list
                      FStarC_Syntax_Print.showable_binder) bs1 in
               let uu___3 =
                 FStarC_Class_Show.show
                   (FStarC_Class_Show.show_list
                      FStarC_Syntax_Print.showable_binder) bs2 in
               FStarC_Compiler_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                 uu___2 (rel_to_string (p_rel orig)) uu___3
             else ());
            (let eq_bqual a1 a2 =
               match (a1, a2) with
               | (FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Implicit
                  b1), FStar_Pervasives_Native.Some
                  (FStarC_Syntax_Syntax.Implicit b2)) -> true
               | uu___1 -> FStarC_Syntax_Util.eq_bqual a1 a2 in
             let compat_positivity_qualifiers p1 p2 =
               match p_rel orig with
               | FStarC_TypeChecker_Common.EQ ->
                   FStarC_TypeChecker_Common.check_positivity_qual false p1
                     p2
               | FStarC_TypeChecker_Common.SUB ->
                   FStarC_TypeChecker_Common.check_positivity_qual true p1 p2
               | FStarC_TypeChecker_Common.SUBINV ->
                   FStarC_TypeChecker_Common.check_positivity_qual true p2 p1 in
             let rec aux wl1 scope subst xs ys =
               match (xs, ys) with
               | ([], []) ->
                   let uu___1 = rhs wl1 scope subst in
                   (match uu___1 with
                    | (rhs_prob, wl2) ->
                        ((let uu___3 = FStarC_Compiler_Effect.op_Bang dbg_Rel in
                          if uu___3
                          then
                            let uu___4 =
                              prob_to_string (p_env wl2 rhs_prob) rhs_prob in
                            FStarC_Compiler_Util.print1 "rhs_prob = %s\n"
                              uu___4
                          else ());
                         (let formula = p_guard rhs_prob in
                          ((FStar_Pervasives.Inl ([rhs_prob], formula)), wl2))))
               | (x::xs1, y::ys1) when
                   (eq_bqual x.FStarC_Syntax_Syntax.binder_qual
                      y.FStarC_Syntax_Syntax.binder_qual)
                     &&
                     (compat_positivity_qualifiers
                        x.FStarC_Syntax_Syntax.binder_positivity
                        y.FStarC_Syntax_Syntax.binder_positivity)
                   ->
                   let uu___1 =
                     ((x.FStarC_Syntax_Syntax.binder_bv),
                       (x.FStarC_Syntax_Syntax.binder_qual)) in
                   (match uu___1 with
                    | (hd1, imp) ->
                        let uu___2 =
                          ((y.FStarC_Syntax_Syntax.binder_bv),
                            (y.FStarC_Syntax_Syntax.binder_qual)) in
                        (match uu___2 with
                         | (hd2, imp') ->
                             let hd11 =
                               let uu___3 =
                                 FStarC_Syntax_Subst.subst subst
                                   hd1.FStarC_Syntax_Syntax.sort in
                               {
                                 FStarC_Syntax_Syntax.ppname =
                                   (hd1.FStarC_Syntax_Syntax.ppname);
                                 FStarC_Syntax_Syntax.index =
                                   (hd1.FStarC_Syntax_Syntax.index);
                                 FStarC_Syntax_Syntax.sort = uu___3
                               } in
                             let hd21 =
                               let uu___3 =
                                 FStarC_Syntax_Subst.subst subst
                                   hd2.FStarC_Syntax_Syntax.sort in
                               {
                                 FStarC_Syntax_Syntax.ppname =
                                   (hd2.FStarC_Syntax_Syntax.ppname);
                                 FStarC_Syntax_Syntax.index =
                                   (hd2.FStarC_Syntax_Syntax.index);
                                 FStarC_Syntax_Syntax.sort = uu___3
                               } in
                             let uu___3 =
                               mk_t_problem wl1 scope orig
                                 hd11.FStarC_Syntax_Syntax.sort
                                 (invert_rel (p_rel orig))
                                 hd21.FStarC_Syntax_Syntax.sort
                                 FStar_Pervasives_Native.None
                                 "Formal parameter" in
                             (match uu___3 with
                              | (prob, wl2) ->
                                  let hd12 =
                                    FStarC_Syntax_Syntax.freshen_bv hd11 in
                                  let subst1 =
                                    let uu___4 =
                                      FStarC_Syntax_Subst.shift_subst
                                        Prims.int_one subst in
                                    (FStarC_Syntax_Syntax.DB
                                       (Prims.int_zero, hd12))
                                      :: uu___4 in
                                  let uu___4 =
                                    aux wl2
                                      (FStarC_Compiler_List.op_At scope
                                         [{
                                            FStarC_Syntax_Syntax.binder_bv =
                                              hd12;
                                            FStarC_Syntax_Syntax.binder_qual
                                              =
                                              (x.FStarC_Syntax_Syntax.binder_qual);
                                            FStarC_Syntax_Syntax.binder_positivity
                                              =
                                              (x.FStarC_Syntax_Syntax.binder_positivity);
                                            FStarC_Syntax_Syntax.binder_attrs
                                              =
                                              (x.FStarC_Syntax_Syntax.binder_attrs)
                                          }]) subst1 xs1 ys1 in
                                  (match uu___4 with
                                   | (FStar_Pervasives.Inl (sub_probs, phi),
                                      wl3) ->
                                       let phi1 =
                                         let uu___5 =
                                           FStarC_TypeChecker_Env.close_forall
                                             (p_env wl3 prob)
                                             [{
                                                FStarC_Syntax_Syntax.binder_bv
                                                  = hd12;
                                                FStarC_Syntax_Syntax.binder_qual
                                                  =
                                                  (x.FStarC_Syntax_Syntax.binder_qual);
                                                FStarC_Syntax_Syntax.binder_positivity
                                                  =
                                                  (x.FStarC_Syntax_Syntax.binder_positivity);
                                                FStarC_Syntax_Syntax.binder_attrs
                                                  =
                                                  (x.FStarC_Syntax_Syntax.binder_attrs)
                                              }] phi in
                                         FStarC_Syntax_Util.mk_conj
                                           (p_guard prob) uu___5 in
                                       ((let uu___6 =
                                           FStarC_Compiler_Effect.op_Bang
                                             dbg_Rel in
                                         if uu___6
                                         then
                                           let uu___7 =
                                             FStarC_Class_Show.show
                                               FStarC_Syntax_Print.showable_term
                                               phi1 in
                                           let uu___8 =
                                             FStarC_Class_Show.show
                                               FStarC_Syntax_Print.showable_bv
                                               hd12 in
                                           FStarC_Compiler_Util.print2
                                             "Formula is %s\n\thd1=%s\n"
                                             uu___7 uu___8
                                         else ());
                                        ((FStar_Pervasives.Inl
                                            ((prob :: sub_probs), phi1)),
                                          wl3))
                                   | fail -> fail))))
               | uu___1 ->
                   ((FStar_Pervasives.Inr
                       "arity or argument-qualifier mismatch"), wl1) in
             let uu___1 = aux wl [] [] bs1 bs2 in
             match uu___1 with
             | (FStar_Pervasives.Inr msg, wl1) -> giveup_lit wl1 msg orig
             | (FStar_Pervasives.Inl (sub_probs, phi), wl1) ->
                 let wl2 =
                   solve_prob orig (FStar_Pervasives_Native.Some phi) [] wl1 in
                 let uu___2 = attempt sub_probs wl2 in solve uu___2)
and (try_solve_without_smt_or_else :
  worklist ->
    (worklist -> solution) ->
      (worklist -> (FStarC_TypeChecker_Common.prob * lstring) -> solution) ->
        solution)
  =
  fun wl ->
    fun try_solve ->
      fun else_solve ->
        let wl' =
          {
            attempting = [];
            wl_deferred =
              (Obj.magic
                 (FStarC_Class_Listlike.empty ()
                    (Obj.magic (FStarC_Compiler_CList.listlike_clist ()))));
            wl_deferred_to_tac = (wl.wl_deferred_to_tac);
            ctr = (wl.ctr);
            defer_ok = NoDefer;
            smt_ok = false;
            umax_heuristic_ok = false;
            tcenv = (wl.tcenv);
            wl_implicits =
              (Obj.magic
                 (FStarC_Class_Listlike.empty ()
                    (Obj.magic (FStarC_Compiler_CList.listlike_clist ()))));
            repr_subcomp_allowed = (wl.repr_subcomp_allowed);
            typeclass_variables = (wl.typeclass_variables)
          } in
        let tx = FStarC_Syntax_Unionfind.new_transaction () in
        let uu___ = try_solve wl' in
        match uu___ with
        | Success (uu___1, defer_to_tac, imps) ->
            (FStarC_Syntax_Unionfind.commit tx;
             (let wl1 =
                extend_wl wl
                  (Obj.magic
                     (FStarC_Class_Listlike.empty ()
                        (Obj.magic (FStarC_Compiler_CList.listlike_clist ()))))
                  defer_to_tac imps in
              solve wl1))
        | Failed (p, s) ->
            (FStarC_Syntax_Unionfind.rollback tx; else_solve wl (p, s))
and (try_solve_then_or_else :
  worklist ->
    (worklist -> solution) ->
      (worklist -> solution) -> (worklist -> solution) -> solution)
  =
  fun wl ->
    fun try_solve ->
      fun then_solve ->
        fun else_solve ->
          let empty_wl =
            {
              attempting = [];
              wl_deferred =
                (Obj.magic
                   (FStarC_Class_Listlike.empty ()
                      (Obj.magic (FStarC_Compiler_CList.listlike_clist ()))));
              wl_deferred_to_tac = (wl.wl_deferred_to_tac);
              ctr = (wl.ctr);
              defer_ok = NoDefer;
              smt_ok = (wl.smt_ok);
              umax_heuristic_ok = (wl.umax_heuristic_ok);
              tcenv = (wl.tcenv);
              wl_implicits =
                (Obj.magic
                   (FStarC_Class_Listlike.empty ()
                      (Obj.magic (FStarC_Compiler_CList.listlike_clist ()))));
              repr_subcomp_allowed = (wl.repr_subcomp_allowed);
              typeclass_variables = (wl.typeclass_variables)
            } in
          let tx = FStarC_Syntax_Unionfind.new_transaction () in
          let uu___ = try_solve empty_wl in
          match uu___ with
          | Success (uu___1, defer_to_tac, imps) ->
              (FStarC_Syntax_Unionfind.commit tx;
               (let wl1 =
                  extend_wl wl
                    (Obj.magic
                       (FStarC_Class_Listlike.empty ()
                          (Obj.magic
                             (FStarC_Compiler_CList.listlike_clist ()))))
                    defer_to_tac imps in
                then_solve wl1))
          | Failed (p, s) ->
              (FStarC_Syntax_Unionfind.rollback tx; else_solve wl)
and (try_solve_probs_without_smt :
  worklist ->
    (worklist -> (FStarC_TypeChecker_Common.probs * worklist)) ->
      (worklist, lstring) FStar_Pervasives.either)
  =
  fun wl ->
    fun probs ->
      let uu___ = probs wl in
      match uu___ with
      | (probs1, wl') ->
          let wl'1 =
            {
              attempting = probs1;
              wl_deferred =
                (Obj.magic
                   (FStarC_Class_Listlike.empty ()
                      (Obj.magic (FStarC_Compiler_CList.listlike_clist ()))));
              wl_deferred_to_tac = (wl.wl_deferred_to_tac);
              ctr = (wl.ctr);
              defer_ok = NoDefer;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (wl.tcenv);
              wl_implicits =
                (Obj.magic
                   (FStarC_Class_Listlike.empty ()
                      (Obj.magic (FStarC_Compiler_CList.listlike_clist ()))));
              repr_subcomp_allowed = (wl.repr_subcomp_allowed);
              typeclass_variables = (wl.typeclass_variables)
            } in
          let uu___1 = solve wl'1 in
          (match uu___1 with
           | Success (uu___2, defer_to_tac, imps) ->
               let wl1 =
                 extend_wl wl
                   (Obj.magic
                      (FStarC_Class_Listlike.empty ()
                         (Obj.magic (FStarC_Compiler_CList.listlike_clist ()))))
                   defer_to_tac imps in
               FStar_Pervasives.Inl wl1
           | Failed (uu___2, ls) -> FStar_Pervasives.Inr ls)
and (solve_t : tprob -> worklist -> solution) =
  fun problem ->
    fun wl ->
      def_check_prob "solve_t" (FStarC_TypeChecker_Common.TProb problem);
      (let uu___1 = compress_tprob wl problem in solve_t' uu___1 wl)
and (solve_t_flex_rigid_eq :
  FStarC_TypeChecker_Common.prob ->
    worklist -> flex_t -> FStarC_Syntax_Syntax.term -> solution)
  =
  fun orig ->
    fun wl ->
      fun lhs ->
        fun rhs ->
          (let uu___1 = FStarC_Compiler_Effect.op_Bang dbg_Rel in
           if uu___1
           then
             let uu___2 =
               FStarC_Class_Show.show FStarC_Syntax_Print.showable_term rhs in
             FStarC_Compiler_Util.print1 "solve_t_flex_rigid_eq rhs=%s\n"
               uu___2
           else ());
          (let uu___1 = should_defer_flex_to_user_tac wl lhs in
           if uu___1
           then defer_to_user_tac orig (flex_reason lhs) wl
           else
             (let mk_solution env lhs1 bs rhs1 =
                let bs_orig = bs in
                let rhs_orig = rhs1 in
                let uu___3 = lhs1 in
                match uu___3 with
                | Flex (uu___4, ctx_u, args) ->
                    let uu___5 =
                      let bv_not_free_in_arg x arg =
                        let uu___6 =
                          let uu___7 =
                            FStarC_Syntax_Free.names
                              (FStar_Pervasives_Native.fst arg) in
                          FStarC_Class_Setlike.mem ()
                            (Obj.magic
                               (FStarC_Compiler_FlatSet.setlike_flat_set
                                  FStarC_Syntax_Syntax.ord_bv)) x
                            (Obj.magic uu___7) in
                        Prims.op_Negation uu___6 in
                      let bv_not_free_in_args x args1 =
                        FStarC_Compiler_Util.for_all (bv_not_free_in_arg x)
                          args1 in
                      let binder_matches_aqual b aq =
                        match ((b.FStarC_Syntax_Syntax.binder_qual), aq) with
                        | (FStar_Pervasives_Native.None,
                           FStar_Pervasives_Native.None) -> true
                        | (FStar_Pervasives_Native.Some
                           (FStarC_Syntax_Syntax.Implicit uu___6),
                           FStar_Pervasives_Native.Some a) ->
                            a.FStarC_Syntax_Syntax.aqual_implicit &&
                              (FStarC_Syntax_Util.eqlist
                                 (fun x ->
                                    fun y ->
                                      let uu___7 =
                                        FStarC_TypeChecker_TermEqAndSimplify.eq_tm
                                          env x y in
                                      uu___7 =
                                        FStarC_TypeChecker_TermEqAndSimplify.Equal)
                                 b.FStarC_Syntax_Syntax.binder_attrs
                                 a.FStarC_Syntax_Syntax.aqual_attributes)
                        | uu___6 -> false in
                      let rec remove_matching_prefix lhs_binders rhs_args =
                        match (lhs_binders, rhs_args) with
                        | ([], uu___6) -> (lhs_binders, rhs_args)
                        | (uu___6, []) -> (lhs_binders, rhs_args)
                        | (b::lhs_tl, (t, aq)::rhs_tl) ->
                            let uu___6 =
                              let uu___7 = FStarC_Syntax_Subst.compress t in
                              uu___7.FStarC_Syntax_Syntax.n in
                            (match uu___6 with
                             | FStarC_Syntax_Syntax.Tm_name x when
                                 ((FStarC_Syntax_Syntax.bv_eq
                                     b.FStarC_Syntax_Syntax.binder_bv x)
                                    && (binder_matches_aqual b aq))
                                   &&
                                   (bv_not_free_in_args
                                      b.FStarC_Syntax_Syntax.binder_bv rhs_tl)
                                 -> remove_matching_prefix lhs_tl rhs_tl
                             | uu___7 -> (lhs_binders, rhs_args)) in
                      let uu___6 = FStarC_Syntax_Util.head_and_args rhs1 in
                      match uu___6 with
                      | (rhs_hd, rhs_args) ->
                          let uu___7 =
                            let uu___8 =
                              remove_matching_prefix
                                (FStarC_Compiler_List.rev bs_orig)
                                (FStarC_Compiler_List.rev rhs_args) in
                            match uu___8 with
                            | (bs_rev, args_rev) ->
                                ((FStarC_Compiler_List.rev bs_rev),
                                  (FStarC_Compiler_List.rev args_rev)) in
                          (match uu___7 with
                           | (bs1, rhs_args1) ->
                               let uu___8 =
                                 FStarC_Syntax_Syntax.mk_Tm_app rhs_hd
                                   rhs_args1 rhs1.FStarC_Syntax_Syntax.pos in
                               (bs1, uu___8)) in
                    (match uu___5 with
                     | (bs1, rhs2) ->
                         let sol =
                           match bs1 with
                           | [] -> rhs2
                           | uu___6 ->
                               let uu___7 =
                                 FStarC_Syntax_Util.ctx_uvar_typ ctx_u in
                               let uu___8 = sn_binders env bs1 in
                               u_abs uu___7 uu___8 rhs2 in
                         [TERM (ctx_u, sol)]) in
              let try_quasi_pattern orig1 env wl1 lhs1 rhs1 =
                (let uu___4 = FStarC_Compiler_Effect.op_Bang dbg_Rel in
                 if uu___4
                 then FStarC_Compiler_Util.print_string "try_quasi_pattern\n"
                 else ());
                (let uu___4 = quasi_pattern env lhs1 in
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
                                       FStarC_Compiler_Option.get msg in
                                     Prims.strcat
                                       "quasi-pattern, occurs-check failed: "
                                       uu___10 in
                                   FStar_Pervasives.Inl uu___9 in
                                 (uu___8, wl1)
                               else
                                 (let fvs_lhs =
                                    binders_as_bv_set
                                      (FStarC_Compiler_List.op_At
                                         ctx_u.FStarC_Syntax_Syntax.ctx_uvar_binders
                                         bs) in
                                  let fvs_rhs = FStarC_Syntax_Free.names rhs1 in
                                  let uu___9 =
                                    let uu___10 =
                                      FStarC_Class_Setlike.subset ()
                                        (Obj.magic
                                           (FStarC_Compiler_FlatSet.setlike_flat_set
                                              FStarC_Syntax_Syntax.ord_bv))
                                        (Obj.magic fvs_rhs)
                                        (Obj.magic fvs_lhs) in
                                    Prims.op_Negation uu___10 in
                                  if uu___9
                                  then
                                    ((FStar_Pervasives.Inl
                                        "quasi-pattern, free names on the RHS are not included in the LHS"),
                                      wl1)
                                  else
                                    (let uu___11 =
                                       let uu___12 =
                                         mk_solution env lhs1 bs rhs1 in
                                       FStar_Pervasives.Inr uu___12 in
                                     let uu___12 =
                                       restrict_all_uvars env ctx_u [] uvars
                                         wl1 in
                                     (uu___11, uu___12)))))) in
              let imitate_app orig1 env wl1 lhs1 bs_lhs t_res_lhs rhs1 =
                let uu___3 = FStarC_Syntax_Util.head_and_args rhs1 in
                match uu___3 with
                | (rhs_hd, args) ->
                    let uu___4 = FStarC_Compiler_Util.prefix args in
                    (match uu___4 with
                     | (args_rhs, last_arg_rhs) ->
                         let rhs' =
                           FStarC_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                             rhs1.FStarC_Syntax_Syntax.pos in
                         let uu___5 = lhs1 in
                         (match uu___5 with
                          | Flex (t_lhs, u_lhs, _lhs_args) ->
                              let uu___6 =
                                let uu___7 =
                                  let env1 = p_env wl1 orig1 in
                                  env1.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                    {
                                      FStarC_TypeChecker_Env.solver =
                                        (env1.FStarC_TypeChecker_Env.solver);
                                      FStarC_TypeChecker_Env.range =
                                        (env1.FStarC_TypeChecker_Env.range);
                                      FStarC_TypeChecker_Env.curmodule =
                                        (env1.FStarC_TypeChecker_Env.curmodule);
                                      FStarC_TypeChecker_Env.gamma =
                                        (env1.FStarC_TypeChecker_Env.gamma);
                                      FStarC_TypeChecker_Env.gamma_sig =
                                        (env1.FStarC_TypeChecker_Env.gamma_sig);
                                      FStarC_TypeChecker_Env.gamma_cache =
                                        (env1.FStarC_TypeChecker_Env.gamma_cache);
                                      FStarC_TypeChecker_Env.modules =
                                        (env1.FStarC_TypeChecker_Env.modules);
                                      FStarC_TypeChecker_Env.expected_typ =
                                        FStar_Pervasives_Native.None;
                                      FStarC_TypeChecker_Env.sigtab =
                                        (env1.FStarC_TypeChecker_Env.sigtab);
                                      FStarC_TypeChecker_Env.attrtab =
                                        (env1.FStarC_TypeChecker_Env.attrtab);
                                      FStarC_TypeChecker_Env.instantiate_imp
                                        =
                                        (env1.FStarC_TypeChecker_Env.instantiate_imp);
                                      FStarC_TypeChecker_Env.effects =
                                        (env1.FStarC_TypeChecker_Env.effects);
                                      FStarC_TypeChecker_Env.generalize =
                                        (env1.FStarC_TypeChecker_Env.generalize);
                                      FStarC_TypeChecker_Env.letrecs =
                                        (env1.FStarC_TypeChecker_Env.letrecs);
                                      FStarC_TypeChecker_Env.top_level =
                                        (env1.FStarC_TypeChecker_Env.top_level);
                                      FStarC_TypeChecker_Env.check_uvars =
                                        (env1.FStarC_TypeChecker_Env.check_uvars);
                                      FStarC_TypeChecker_Env.use_eq_strict =
                                        (env1.FStarC_TypeChecker_Env.use_eq_strict);
                                      FStarC_TypeChecker_Env.is_iface =
                                        (env1.FStarC_TypeChecker_Env.is_iface);
                                      FStarC_TypeChecker_Env.admit = true;
                                      FStarC_TypeChecker_Env.lax_universes =
                                        (env1.FStarC_TypeChecker_Env.lax_universes);
                                      FStarC_TypeChecker_Env.phase1 =
                                        (env1.FStarC_TypeChecker_Env.phase1);
                                      FStarC_TypeChecker_Env.failhard =
                                        (env1.FStarC_TypeChecker_Env.failhard);
                                      FStarC_TypeChecker_Env.flychecking =
                                        (env1.FStarC_TypeChecker_Env.flychecking);
                                      FStarC_TypeChecker_Env.uvar_subtyping =
                                        (env1.FStarC_TypeChecker_Env.uvar_subtyping);
                                      FStarC_TypeChecker_Env.intactics =
                                        (env1.FStarC_TypeChecker_Env.intactics);
                                      FStarC_TypeChecker_Env.nocoerce =
                                        (env1.FStarC_TypeChecker_Env.nocoerce);
                                      FStarC_TypeChecker_Env.tc_term =
                                        (env1.FStarC_TypeChecker_Env.tc_term);
                                      FStarC_TypeChecker_Env.typeof_tot_or_gtot_term
                                        =
                                        (env1.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                                      FStarC_TypeChecker_Env.universe_of =
                                        (env1.FStarC_TypeChecker_Env.universe_of);
                                      FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                        =
                                        (env1.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                      FStarC_TypeChecker_Env.teq_nosmt_force
                                        =
                                        (env1.FStarC_TypeChecker_Env.teq_nosmt_force);
                                      FStarC_TypeChecker_Env.subtype_nosmt_force
                                        =
                                        (env1.FStarC_TypeChecker_Env.subtype_nosmt_force);
                                      FStarC_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (env1.FStarC_TypeChecker_Env.qtbl_name_and_index);
                                      FStarC_TypeChecker_Env.normalized_eff_names
                                        =
                                        (env1.FStarC_TypeChecker_Env.normalized_eff_names);
                                      FStarC_TypeChecker_Env.fv_delta_depths
                                        =
                                        (env1.FStarC_TypeChecker_Env.fv_delta_depths);
                                      FStarC_TypeChecker_Env.proof_ns =
                                        (env1.FStarC_TypeChecker_Env.proof_ns);
                                      FStarC_TypeChecker_Env.synth_hook =
                                        (env1.FStarC_TypeChecker_Env.synth_hook);
                                      FStarC_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (env1.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                                      FStarC_TypeChecker_Env.splice =
                                        (env1.FStarC_TypeChecker_Env.splice);
                                      FStarC_TypeChecker_Env.mpreprocess =
                                        (env1.FStarC_TypeChecker_Env.mpreprocess);
                                      FStarC_TypeChecker_Env.postprocess =
                                        (env1.FStarC_TypeChecker_Env.postprocess);
                                      FStarC_TypeChecker_Env.identifier_info
                                        =
                                        (env1.FStarC_TypeChecker_Env.identifier_info);
                                      FStarC_TypeChecker_Env.tc_hooks =
                                        (env1.FStarC_TypeChecker_Env.tc_hooks);
                                      FStarC_TypeChecker_Env.dsenv =
                                        (env1.FStarC_TypeChecker_Env.dsenv);
                                      FStarC_TypeChecker_Env.nbe =
                                        (env1.FStarC_TypeChecker_Env.nbe);
                                      FStarC_TypeChecker_Env.strict_args_tab
                                        =
                                        (env1.FStarC_TypeChecker_Env.strict_args_tab);
                                      FStarC_TypeChecker_Env.erasable_types_tab
                                        =
                                        (env1.FStarC_TypeChecker_Env.erasable_types_tab);
                                      FStarC_TypeChecker_Env.enable_defer_to_tac
                                        =
                                        (env1.FStarC_TypeChecker_Env.enable_defer_to_tac);
                                      FStarC_TypeChecker_Env.unif_allow_ref_guards
                                        =
                                        (env1.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                                      FStarC_TypeChecker_Env.erase_erasable_args
                                        =
                                        (env1.FStarC_TypeChecker_Env.erase_erasable_args);
                                      FStarC_TypeChecker_Env.core_check =
                                        (env1.FStarC_TypeChecker_Env.core_check);
                                      FStarC_TypeChecker_Env.missing_decl =
                                        (env1.FStarC_TypeChecker_Env.missing_decl)
                                    }
                                    (FStar_Pervasives_Native.fst last_arg_rhs)
                                    false in
                                match uu___7 with
                                | (t_last_arg, uu___8) ->
                                    let uu___9 =
                                      let b =
                                        FStarC_Syntax_Syntax.null_binder
                                          t_last_arg in
                                      let uu___10 =
                                        let uu___11 =
                                          FStarC_Syntax_Syntax.mk_Total
                                            t_res_lhs in
                                        FStarC_Syntax_Util.arrow [b] uu___11 in
                                      copy_uvar u_lhs
                                        (FStarC_Compiler_List.op_At bs_lhs
                                           [b]) uu___10 wl1 in
                                    (match uu___9 with
                                     | (uu___10, lhs', wl2) ->
                                         let uu___11 =
                                           copy_uvar u_lhs bs_lhs t_last_arg
                                             wl2 in
                                         (match uu___11 with
                                          | (uu___12, lhs'_last_arg, wl3) ->
                                              (lhs', lhs'_last_arg, wl3))) in
                              (match uu___6 with
                               | (lhs', lhs'_last_arg, wl2) ->
                                   let sol =
                                     let uu___7 =
                                       let uu___8 =
                                         let uu___9 =
                                           let uu___10 =
                                             FStarC_Syntax_Syntax.mk_Tm_app
                                               lhs'
                                               [(lhs'_last_arg,
                                                  (FStar_Pervasives_Native.snd
                                                     last_arg_rhs))]
                                               t_lhs.FStarC_Syntax_Syntax.pos in
                                           FStarC_Syntax_Util.abs bs_lhs
                                             uu___10
                                             (FStar_Pervasives_Native.Some
                                                (FStarC_Syntax_Util.residual_tot
                                                   t_res_lhs)) in
                                         (u_lhs, uu___9) in
                                       TERM uu___8 in
                                     [uu___7] in
                                   let uu___7 =
                                     let uu___8 =
                                       mk_t_problem wl2 [] orig1 lhs'
                                         FStarC_TypeChecker_Common.EQ rhs'
                                         FStar_Pervasives_Native.None
                                         "first-order lhs" in
                                     match uu___8 with
                                     | (p1, wl3) ->
                                         let uu___9 =
                                           mk_t_problem wl3 [] orig1
                                             lhs'_last_arg
                                             FStarC_TypeChecker_Common.EQ
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
                                        solve uu___8)))) in
              let imitate orig1 env wl1 lhs1 rhs1 =
                (let uu___4 = FStarC_Compiler_Effect.op_Bang dbg_Rel in
                 if uu___4
                 then FStarC_Compiler_Util.print_string "imitate\n"
                 else ());
                (let is_app rhs2 =
                   let uu___4 = FStarC_Syntax_Util.head_and_args rhs2 in
                   match uu___4 with
                   | (uu___5, args) ->
                       (match args with | [] -> false | uu___6 -> true) in
                 let is_arrow rhs2 =
                   let uu___4 =
                     let uu___5 = FStarC_Syntax_Subst.compress rhs2 in
                     uu___5.FStarC_Syntax_Syntax.n in
                   match uu___4 with
                   | FStarC_Syntax_Syntax.Tm_arrow uu___5 -> true
                   | uu___5 -> false in
                 let uu___4 = quasi_pattern env lhs1 in
                 match uu___4 with
                 | FStar_Pervasives_Native.None ->
                     let msg =
                       mklstr
                         (fun uu___5 ->
                            let uu___6 = prob_to_string env orig1 in
                            FStarC_Compiler_Util.format1
                              "imitate heuristic cannot solve %s; lhs not a quasi-pattern"
                              uu___6) in
                     giveup_or_defer orig1 wl1
                       FStarC_TypeChecker_Common.Deferred_first_order_heuristic_failed
                       msg
                 | FStar_Pervasives_Native.Some (bs_lhs, t_res_lhs) ->
                     let uu___5 = is_app rhs1 in
                     if uu___5
                     then
                       imitate_app orig1 env wl1 lhs1 bs_lhs t_res_lhs rhs1
                     else
                       (let uu___7 = is_arrow rhs1 in
                        if uu___7
                        then
                          imitate_arrow orig1 wl1 lhs1 bs_lhs t_res_lhs
                            FStarC_TypeChecker_Common.EQ rhs1
                        else
                          (let msg =
                             mklstr
                               (fun uu___9 ->
                                  let uu___10 = prob_to_string env orig1 in
                                  FStarC_Compiler_Util.format1
                                    "imitate heuristic cannot solve %s; rhs not an app or arrow"
                                    uu___10) in
                           giveup_or_defer orig1 wl1
                             FStarC_TypeChecker_Common.Deferred_first_order_heuristic_failed
                             msg))) in
              let try_first_order orig1 env wl1 lhs1 rhs1 =
                let inapplicable msg lstring_opt =
                  (let uu___4 = FStarC_Compiler_Effect.op_Bang dbg_Rel in
                   if uu___4
                   then
                     let extra_msg =
                       match lstring_opt with
                       | FStar_Pervasives_Native.None -> ""
                       | FStar_Pervasives_Native.Some l ->
                           FStarC_Thunk.force l in
                     FStarC_Compiler_Util.print2
                       "try_first_order failed because: %s\n%s\n" msg
                       extra_msg
                   else ());
                  FStar_Pervasives.Inl "first_order doesn't apply" in
                (let uu___4 = FStarC_Compiler_Effect.op_Bang dbg_Rel in
                 if uu___4
                 then
                   let uu___5 = flex_t_to_string lhs1 in
                   let uu___6 =
                     FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                       rhs1 in
                   FStarC_Compiler_Util.print2
                     "try_first_order\n\tlhs=%s\n\trhs=%s\n" uu___5 uu___6
                 else ());
                (let uu___4 = lhs1 in
                 match uu___4 with
                 | Flex (_t1, ctx_uv, args_lhs) ->
                     let n_args_lhs = FStarC_Compiler_List.length args_lhs in
                     let uu___5 = FStarC_Syntax_Util.head_and_args rhs1 in
                     (match uu___5 with
                      | (head, args_rhs) ->
                          let n_args_rhs =
                            FStarC_Compiler_List.length args_rhs in
                          if n_args_lhs > n_args_rhs
                          then
                            inapplicable "not enough args"
                              FStar_Pervasives_Native.None
                          else
                            (let i = n_args_rhs - n_args_lhs in
                             let uu___7 =
                               FStarC_Compiler_List.splitAt i args_rhs in
                             match uu___7 with
                             | (prefix, args_rhs1) ->
                                 let head1 =
                                   FStarC_Syntax_Syntax.mk_Tm_app head prefix
                                     head.FStarC_Syntax_Syntax.pos in
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
                                               FStarC_Syntax_Free.names head1 in
                                             let uu___14 =
                                               binders_as_bv_set
                                                 ctx_uv.FStarC_Syntax_Syntax.ctx_uvar_binders in
                                             FStarC_Class_Setlike.subset ()
                                               (Obj.magic
                                                  (FStarC_Compiler_FlatSet.setlike_flat_set
                                                     FStarC_Syntax_Syntax.ord_bv))
                                               (Obj.magic uu___13)
                                               (Obj.magic uu___14) in
                                           Prims.op_Negation uu___12 in
                                         if uu___11
                                         then
                                           inapplicable
                                             "free name inclusion failed"
                                             FStar_Pervasives_Native.None
                                         else
                                           (let uu___13 =
                                              env.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                                {
                                                  FStarC_TypeChecker_Env.solver
                                                    =
                                                    (env.FStarC_TypeChecker_Env.solver);
                                                  FStarC_TypeChecker_Env.range
                                                    =
                                                    (env.FStarC_TypeChecker_Env.range);
                                                  FStarC_TypeChecker_Env.curmodule
                                                    =
                                                    (env.FStarC_TypeChecker_Env.curmodule);
                                                  FStarC_TypeChecker_Env.gamma
                                                    =
                                                    (env.FStarC_TypeChecker_Env.gamma);
                                                  FStarC_TypeChecker_Env.gamma_sig
                                                    =
                                                    (env.FStarC_TypeChecker_Env.gamma_sig);
                                                  FStarC_TypeChecker_Env.gamma_cache
                                                    =
                                                    (env.FStarC_TypeChecker_Env.gamma_cache);
                                                  FStarC_TypeChecker_Env.modules
                                                    =
                                                    (env.FStarC_TypeChecker_Env.modules);
                                                  FStarC_TypeChecker_Env.expected_typ
                                                    =
                                                    FStar_Pervasives_Native.None;
                                                  FStarC_TypeChecker_Env.sigtab
                                                    =
                                                    (env.FStarC_TypeChecker_Env.sigtab);
                                                  FStarC_TypeChecker_Env.attrtab
                                                    =
                                                    (env.FStarC_TypeChecker_Env.attrtab);
                                                  FStarC_TypeChecker_Env.instantiate_imp
                                                    =
                                                    (env.FStarC_TypeChecker_Env.instantiate_imp);
                                                  FStarC_TypeChecker_Env.effects
                                                    =
                                                    (env.FStarC_TypeChecker_Env.effects);
                                                  FStarC_TypeChecker_Env.generalize
                                                    =
                                                    (env.FStarC_TypeChecker_Env.generalize);
                                                  FStarC_TypeChecker_Env.letrecs
                                                    =
                                                    (env.FStarC_TypeChecker_Env.letrecs);
                                                  FStarC_TypeChecker_Env.top_level
                                                    =
                                                    (env.FStarC_TypeChecker_Env.top_level);
                                                  FStarC_TypeChecker_Env.check_uvars
                                                    =
                                                    (env.FStarC_TypeChecker_Env.check_uvars);
                                                  FStarC_TypeChecker_Env.use_eq_strict
                                                    =
                                                    (env.FStarC_TypeChecker_Env.use_eq_strict);
                                                  FStarC_TypeChecker_Env.is_iface
                                                    =
                                                    (env.FStarC_TypeChecker_Env.is_iface);
                                                  FStarC_TypeChecker_Env.admit
                                                    = true;
                                                  FStarC_TypeChecker_Env.lax_universes
                                                    =
                                                    (env.FStarC_TypeChecker_Env.lax_universes);
                                                  FStarC_TypeChecker_Env.phase1
                                                    =
                                                    (env.FStarC_TypeChecker_Env.phase1);
                                                  FStarC_TypeChecker_Env.failhard
                                                    =
                                                    (env.FStarC_TypeChecker_Env.failhard);
                                                  FStarC_TypeChecker_Env.flychecking
                                                    =
                                                    (env.FStarC_TypeChecker_Env.flychecking);
                                                  FStarC_TypeChecker_Env.uvar_subtyping
                                                    =
                                                    (env.FStarC_TypeChecker_Env.uvar_subtyping);
                                                  FStarC_TypeChecker_Env.intactics
                                                    =
                                                    (env.FStarC_TypeChecker_Env.intactics);
                                                  FStarC_TypeChecker_Env.nocoerce
                                                    =
                                                    (env.FStarC_TypeChecker_Env.nocoerce);
                                                  FStarC_TypeChecker_Env.tc_term
                                                    =
                                                    (env.FStarC_TypeChecker_Env.tc_term);
                                                  FStarC_TypeChecker_Env.typeof_tot_or_gtot_term
                                                    =
                                                    (env.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                                                  FStarC_TypeChecker_Env.universe_of
                                                    =
                                                    (env.FStarC_TypeChecker_Env.universe_of);
                                                  FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                                    =
                                                    (env.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                                  FStarC_TypeChecker_Env.teq_nosmt_force
                                                    =
                                                    (env.FStarC_TypeChecker_Env.teq_nosmt_force);
                                                  FStarC_TypeChecker_Env.subtype_nosmt_force
                                                    =
                                                    (env.FStarC_TypeChecker_Env.subtype_nosmt_force);
                                                  FStarC_TypeChecker_Env.qtbl_name_and_index
                                                    =
                                                    (env.FStarC_TypeChecker_Env.qtbl_name_and_index);
                                                  FStarC_TypeChecker_Env.normalized_eff_names
                                                    =
                                                    (env.FStarC_TypeChecker_Env.normalized_eff_names);
                                                  FStarC_TypeChecker_Env.fv_delta_depths
                                                    =
                                                    (env.FStarC_TypeChecker_Env.fv_delta_depths);
                                                  FStarC_TypeChecker_Env.proof_ns
                                                    =
                                                    (env.FStarC_TypeChecker_Env.proof_ns);
                                                  FStarC_TypeChecker_Env.synth_hook
                                                    =
                                                    (env.FStarC_TypeChecker_Env.synth_hook);
                                                  FStarC_TypeChecker_Env.try_solve_implicits_hook
                                                    =
                                                    (env.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                                                  FStarC_TypeChecker_Env.splice
                                                    =
                                                    (env.FStarC_TypeChecker_Env.splice);
                                                  FStarC_TypeChecker_Env.mpreprocess
                                                    =
                                                    (env.FStarC_TypeChecker_Env.mpreprocess);
                                                  FStarC_TypeChecker_Env.postprocess
                                                    =
                                                    (env.FStarC_TypeChecker_Env.postprocess);
                                                  FStarC_TypeChecker_Env.identifier_info
                                                    =
                                                    (env.FStarC_TypeChecker_Env.identifier_info);
                                                  FStarC_TypeChecker_Env.tc_hooks
                                                    =
                                                    (env.FStarC_TypeChecker_Env.tc_hooks);
                                                  FStarC_TypeChecker_Env.dsenv
                                                    =
                                                    (env.FStarC_TypeChecker_Env.dsenv);
                                                  FStarC_TypeChecker_Env.nbe
                                                    =
                                                    (env.FStarC_TypeChecker_Env.nbe);
                                                  FStarC_TypeChecker_Env.strict_args_tab
                                                    =
                                                    (env.FStarC_TypeChecker_Env.strict_args_tab);
                                                  FStarC_TypeChecker_Env.erasable_types_tab
                                                    =
                                                    (env.FStarC_TypeChecker_Env.erasable_types_tab);
                                                  FStarC_TypeChecker_Env.enable_defer_to_tac
                                                    =
                                                    (env.FStarC_TypeChecker_Env.enable_defer_to_tac);
                                                  FStarC_TypeChecker_Env.unif_allow_ref_guards
                                                    =
                                                    (env.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                                                  FStarC_TypeChecker_Env.erase_erasable_args
                                                    =
                                                    (env.FStarC_TypeChecker_Env.erase_erasable_args);
                                                  FStarC_TypeChecker_Env.core_check
                                                    =
                                                    (env.FStarC_TypeChecker_Env.core_check);
                                                  FStarC_TypeChecker_Env.missing_decl
                                                    =
                                                    (env.FStarC_TypeChecker_Env.missing_decl)
                                                } head1 false in
                                            match uu___13 with
                                            | (t_head, uu___14) ->
                                                let tx =
                                                  FStarC_Syntax_Unionfind.new_transaction
                                                    () in
                                                let solve_sub_probs_if_head_types_equal
                                                  head_uvars_to_restrict wl2
                                                  =
                                                  let sol =
                                                    [TERM (ctx_uv, head1)] in
                                                  let wl3 =
                                                    restrict_all_uvars env
                                                      ctx_uv []
                                                      head_uvars_to_restrict
                                                      wl2 in
                                                  let wl4 =
                                                    solve_prob orig1
                                                      FStar_Pervasives_Native.None
                                                      sol wl3 in
                                                  let uu___15 =
                                                    FStarC_Compiler_List.fold_left2
                                                      (fun uu___16 ->
                                                         fun uu___17 ->
                                                           fun uu___18 ->
                                                             match (uu___16,
                                                                    uu___17,
                                                                    uu___18)
                                                             with
                                                             | ((probs, wl5),
                                                                (arg_lhs,
                                                                 uu___19),
                                                                (arg_rhs,
                                                                 uu___20)) ->
                                                                 let uu___21
                                                                   =
                                                                   mk_t_problem
                                                                    wl5 []
                                                                    orig1
                                                                    arg_lhs
                                                                    FStarC_TypeChecker_Common.EQ
                                                                    arg_rhs
                                                                    FStar_Pervasives_Native.None
                                                                    "first-order arg" in
                                                                 (match uu___21
                                                                  with
                                                                  | (p, wl6)
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
                                                          wl_deferred =
                                                            (Obj.magic
                                                               (FStarC_Class_Listlike.empty
                                                                  ()
                                                                  (Obj.magic
                                                                    (FStarC_Compiler_CList.listlike_clist
                                                                    ()))));
                                                          wl_deferred_to_tac
                                                            =
                                                            (wl5.wl_deferred_to_tac);
                                                          ctr = (wl5.ctr);
                                                          defer_ok = NoDefer;
                                                          smt_ok = false;
                                                          umax_heuristic_ok =
                                                            (wl5.umax_heuristic_ok);
                                                          tcenv = (wl5.tcenv);
                                                          wl_implicits =
                                                            (Obj.magic
                                                               (FStarC_Class_Listlike.empty
                                                                  ()
                                                                  (Obj.magic
                                                                    (FStarC_Compiler_CList.listlike_clist
                                                                    ()))));
                                                          repr_subcomp_allowed
                                                            =
                                                            (wl5.repr_subcomp_allowed);
                                                          typeclass_variables
                                                            =
                                                            (wl5.typeclass_variables)
                                                        } in
                                                      let uu___16 = solve wl' in
                                                      (match uu___16 with
                                                       | Success
                                                           (uu___17,
                                                            defer_to_tac,
                                                            imps)
                                                           ->
                                                           let wl6 =
                                                             extend_wl wl5
                                                               (Obj.magic
                                                                  (FStarC_Class_Listlike.empty
                                                                    ()
                                                                    (Obj.magic
                                                                    (FStarC_Compiler_CList.listlike_clist
                                                                    ()))))
                                                               defer_to_tac
                                                               imps in
                                                           (FStarC_Syntax_Unionfind.commit
                                                              tx;
                                                            FStar_Pervasives.Inr
                                                              wl6)
                                                       | Failed
                                                           (uu___17,
                                                            lstring1)
                                                           ->
                                                           (FStarC_Syntax_Unionfind.rollback
                                                              tx;
                                                            inapplicable
                                                              "Subprobs failed: "
                                                              (FStar_Pervasives_Native.Some
                                                                 lstring1))) in
                                                let uu___15 =
                                                  let uu___16 =
                                                    let uu___17 =
                                                      FStarC_Syntax_Util.ctx_uvar_typ
                                                        ctx_uv in
                                                    FStarC_TypeChecker_TermEqAndSimplify.eq_tm
                                                      env t_head uu___17 in
                                                  uu___16 =
                                                    FStarC_TypeChecker_TermEqAndSimplify.Equal in
                                                if uu___15
                                                then
                                                  solve_sub_probs_if_head_types_equal
                                                    uvars_head wl1
                                                else
                                                  ((let uu___18 =
                                                      FStarC_Compiler_Effect.op_Bang
                                                        dbg_Rel in
                                                    if uu___18
                                                    then
                                                      let uu___19 =
                                                        let uu___20 =
                                                          FStarC_Syntax_Util.ctx_uvar_typ
                                                            ctx_uv in
                                                        FStarC_Class_Show.show
                                                          FStarC_Syntax_Print.showable_term
                                                          uu___20 in
                                                      let uu___20 =
                                                        FStarC_Class_Show.show
                                                          FStarC_Syntax_Print.showable_term
                                                          t_head in
                                                      FStarC_Compiler_Util.print2
                                                        "first-order: head type mismatch:\n\tlhs=%s\n\trhs=%s\n"
                                                        uu___19 uu___20
                                                    else ());
                                                   (let typ_equality_prob wl2
                                                      =
                                                      let uu___18 =
                                                        let uu___19 =
                                                          FStarC_Syntax_Util.ctx_uvar_typ
                                                            ctx_uv in
                                                        mk_t_problem wl2 []
                                                          orig1 uu___19
                                                          FStarC_TypeChecker_Common.EQ
                                                          t_head
                                                          FStar_Pervasives_Native.None
                                                          "first-order head type" in
                                                      match uu___18 with
                                                      | (p, wl3) ->
                                                          ([p], wl3) in
                                                    let uu___18 =
                                                      try_solve_probs_without_smt
                                                        wl1 typ_equality_prob in
                                                    match uu___18 with
                                                    | FStar_Pervasives.Inl
                                                        wl2 ->
                                                        let uu___19 =
                                                          let uu___20 =
                                                            FStarC_Syntax_Free.uvars
                                                              head1 in
                                                          FStarC_Class_Setlike.elems
                                                            ()
                                                            (Obj.magic
                                                               (FStarC_Compiler_FlatSet.setlike_flat_set
                                                                  FStarC_Syntax_Free.ord_ctx_uvar))
                                                            (Obj.magic
                                                               uu___20) in
                                                        solve_sub_probs_if_head_types_equal
                                                          uu___19 wl2
                                                    | FStar_Pervasives.Inr
                                                        msg ->
                                                        (FStarC_Syntax_Unionfind.rollback
                                                           tx;
                                                         inapplicable
                                                           "first-order: head type mismatch"
                                                           (FStar_Pervasives_Native.Some
                                                              msg)))))))))) in
              match p_rel orig with
              | FStarC_TypeChecker_Common.SUB ->
                  if wl.defer_ok = DeferAny
                  then
                    let uu___3 = FStarC_Thunk.mkv "flex-rigid subtyping" in
                    giveup_or_defer orig wl
                      FStarC_TypeChecker_Common.Deferred_flex uu___3
                  else solve_t_flex_rigid_eq (make_prob_eq orig) wl lhs rhs
              | FStarC_TypeChecker_Common.SUBINV ->
                  if wl.defer_ok = DeferAny
                  then
                    let uu___3 = FStarC_Thunk.mkv "flex-rigid subtyping" in
                    giveup_or_defer orig wl
                      FStarC_TypeChecker_Common.Deferred_flex uu___3
                  else solve_t_flex_rigid_eq (make_prob_eq orig) wl lhs rhs
              | FStarC_TypeChecker_Common.EQ ->
                  let uu___3 = lhs in
                  (match uu___3 with
                   | Flex (_t1, ctx_uv, args_lhs) ->
                       let env = p_env wl orig in
                       let uu___4 =
                         pat_vars env
                           ctx_uv.FStarC_Syntax_Syntax.ctx_uvar_binders
                           args_lhs in
                       (match uu___4 with
                        | FStar_Pervasives_Native.Some lhs_binders ->
                            ((let uu___6 =
                                FStarC_Compiler_Effect.op_Bang dbg_Rel in
                              if uu___6
                              then
                                FStarC_Compiler_Util.print_string
                                  "it's a pattern\n"
                              else ());
                             (let rhs1 = sn env rhs in
                              let fvs1 =
                                binders_as_bv_set
                                  (FStarC_Compiler_List.op_At
                                     ctx_uv.FStarC_Syntax_Syntax.ctx_uvar_binders
                                     lhs_binders) in
                              let fvs2 = FStarC_Syntax_Free.names rhs1 in
                              let uu___6 = occurs_check ctx_uv rhs1 in
                              match uu___6 with
                              | (uvars, occurs_ok, msg) ->
                                  let uu___7 =
                                    if occurs_ok
                                    then ((uvars, occurs_ok, msg), rhs1)
                                    else
                                      (let rhs2 =
                                         FStarC_TypeChecker_Normalize.normalize
                                           [FStarC_TypeChecker_Env.Primops;
                                           FStarC_TypeChecker_Env.Weak;
                                           FStarC_TypeChecker_Env.HNF;
                                           FStarC_TypeChecker_Env.Beta;
                                           FStarC_TypeChecker_Env.Eager_unfolding;
                                           FStarC_TypeChecker_Env.Unascribe]
                                           (p_env wl orig) rhs1 in
                                       let uu___9 = occurs_check ctx_uv rhs2 in
                                       (uu___9, rhs2)) in
                                  (match uu___7 with
                                   | ((uvars1, occurs_ok1, msg1), rhs2) ->
                                       let uu___8 =
                                         (term_is_uvar ctx_uv rhs2) &&
                                           (Prims.uu___is_Nil args_lhs) in
                                       if uu___8
                                       then
                                         let uu___9 =
                                           solve_prob orig
                                             FStar_Pervasives_Native.None []
                                             wl in
                                         solve uu___9
                                       else
                                         if Prims.op_Negation occurs_ok1
                                         then
                                           (let uu___10 =
                                              let uu___11 =
                                                let uu___12 =
                                                  FStarC_Compiler_Option.get
                                                    msg1 in
                                                Prims.strcat
                                                  "occurs-check failed: "
                                                  uu___12 in
                                              FStarC_Thunk.mkv uu___11 in
                                            giveup_or_defer orig wl
                                              FStarC_TypeChecker_Common.Deferred_occur_check_failed
                                              uu___10)
                                         else
                                           (let uu___11 =
                                              FStarC_Class_Setlike.subset ()
                                                (Obj.magic
                                                   (FStarC_Compiler_FlatSet.setlike_flat_set
                                                      FStarC_Syntax_Syntax.ord_bv))
                                                (Obj.magic fvs2)
                                                (Obj.magic fvs1) in
                                            if uu___11
                                            then
                                              let sol =
                                                mk_solution env lhs
                                                  lhs_binders rhs2 in
                                              let wl1 =
                                                restrict_all_uvars env ctx_uv
                                                  lhs_binders uvars1 wl in
                                              let uu___12 =
                                                solve_prob orig
                                                  FStar_Pervasives_Native.None
                                                  sol wl1 in
                                              solve uu___12
                                            else
                                              if wl.defer_ok = DeferAny
                                              then
                                                (let msg2 =
                                                   mklstr
                                                     (fun uu___13 ->
                                                        let uu___14 =
                                                          FStarC_Class_Show.show
                                                            (FStarC_Compiler_FlatSet.showable_set
                                                               FStarC_Syntax_Syntax.ord_bv
                                                               FStarC_Syntax_Print.showable_bv)
                                                            fvs2 in
                                                        let uu___15 =
                                                          FStarC_Class_Show.show
                                                            (FStarC_Compiler_FlatSet.showable_set
                                                               FStarC_Syntax_Syntax.ord_bv
                                                               FStarC_Syntax_Print.showable_bv)
                                                            fvs1 in
                                                        let uu___16 =
                                                          FStarC_Class_Show.show
                                                            (FStarC_Class_Show.show_list
                                                               FStarC_Syntax_Print.showable_binder)
                                                            (FStarC_Compiler_List.op_At
                                                               ctx_uv.FStarC_Syntax_Syntax.ctx_uvar_binders
                                                               lhs_binders) in
                                                        FStarC_Compiler_Util.format3
                                                          "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                                          uu___14 uu___15
                                                          uu___16) in
                                                 giveup_or_defer orig wl
                                                   FStarC_TypeChecker_Common.Deferred_free_names_check_failed
                                                   msg2)
                                              else
                                                imitate orig env wl lhs rhs2))))
                        | uu___5 ->
                            if wl.defer_ok = DeferAny
                            then
                              let uu___6 = FStarC_Thunk.mkv "Not a pattern" in
                              giveup_or_defer orig wl
                                FStarC_TypeChecker_Common.Deferred_not_a_pattern
                                uu___6
                            else
                              (let uu___7 =
                                 try_first_order orig env wl lhs rhs in
                               match uu___7 with
                               | FStar_Pervasives.Inr wl1 -> solve wl1
                               | uu___8 ->
                                   let uu___9 =
                                     try_quasi_pattern orig env wl lhs rhs in
                                   (match uu___9 with
                                    | (FStar_Pervasives.Inr sol, wl1) ->
                                        let uu___10 =
                                          solve_prob orig
                                            FStar_Pervasives_Native.None sol
                                            wl1 in
                                        solve uu___10
                                    | (FStar_Pervasives.Inl msg, uu___10) ->
                                        imitate orig env wl lhs rhs))))))
and (solve_t_flex_flex :
  FStarC_TypeChecker_Env.env_t ->
    FStarC_TypeChecker_Common.prob ->
      worklist -> flex_t -> flex_t -> solution)
  =
  fun env ->
    fun orig ->
      fun wl ->
        fun lhs ->
          fun rhs ->
            let should_run_meta_arg_tac flex =
              let uv = flex_uvar flex in
              ((flex_uvar_has_meta_tac uv) &&
                 (let uu___ =
                    let uu___1 = FStarC_Syntax_Util.ctx_uvar_typ uv in
                    has_free_uvars uu___1 in
                  Prims.op_Negation uu___))
                &&
                (let uu___ =
                   gamma_has_free_uvars
                     uv.FStarC_Syntax_Syntax.ctx_uvar_gamma in
                 Prims.op_Negation uu___) in
            let run_meta_arg_tac_and_try_again flex =
              let uv = flex_uvar flex in
              let t = run_meta_arg_tac env uv in
              (let uu___1 = FStarC_Compiler_Effect.op_Bang dbg_Rel in
               if uu___1
               then
                 let uu___2 =
                   FStarC_Class_Show.show FStarC_Syntax_Print.showable_ctxu
                     uv in
                 let uu___3 =
                   FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
                 FStarC_Compiler_Util.print2
                   "solve_t_flex_flex: solving meta arg uvar %s with %s\n"
                   uu___2 uu___3
               else ());
              set_uvar env uv FStar_Pervasives_Native.None t;
              (let uu___2 = attempt [orig] wl in solve uu___2) in
            match p_rel orig with
            | FStarC_TypeChecker_Common.SUB ->
                if wl.defer_ok = DeferAny
                then
                  let uu___ = FStarC_Thunk.mkv "flex-flex subtyping" in
                  giveup_or_defer_flex_flex orig wl
                    FStarC_TypeChecker_Common.Deferred_flex uu___
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStarC_TypeChecker_Common.SUBINV ->
                if wl.defer_ok = DeferAny
                then
                  let uu___ = FStarC_Thunk.mkv "flex-flex subtyping" in
                  giveup_or_defer_flex_flex orig wl
                    FStarC_TypeChecker_Common.Deferred_flex uu___
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStarC_TypeChecker_Common.EQ ->
                let uu___ =
                  (should_defer_flex_to_user_tac wl lhs) ||
                    (should_defer_flex_to_user_tac wl rhs) in
                if uu___
                then
                  defer_to_user_tac orig
                    (Prims.strcat (flex_reason lhs)
                       (Prims.strcat ", " (flex_reason rhs))) wl
                else
                  if
                    ((wl.defer_ok = DeferAny) ||
                       (wl.defer_ok = DeferFlexFlexOnly))
                      &&
                      ((Prims.op_Negation (is_flex_pat lhs)) ||
                         (Prims.op_Negation (is_flex_pat rhs)))
                  then
                    (let uu___2 = FStarC_Thunk.mkv "flex-flex non-pattern" in
                     giveup_or_defer_flex_flex orig wl
                       FStarC_TypeChecker_Common.Deferred_flex_flex_nonpattern
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
                          (let rec occurs_bs u bs =
                             match bs with
                             | [] -> false
                             | b::bs1 ->
                                 (let uu___7 =
                                    occurs u
                                      (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                                  FStar_Pervasives_Native.snd uu___7) ||
                                   (occurs_bs u bs1) in
                           let uu___7 =
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
                                    ({ FStarC_Syntax_Syntax.n = uu___9;
                                       FStarC_Syntax_Syntax.pos = range;
                                       FStarC_Syntax_Syntax.vars = uu___10;
                                       FStarC_Syntax_Syntax.hash_code =
                                         uu___11;_},
                                     u_lhs, uu___12)
                                    ->
                                    let uu___13 = occurs_bs u_lhs binders_lhs in
                                    if uu___13
                                    then
                                      let uu___14 =
                                        FStarC_Thunk.mkv
                                          "flex-flex: occurs check failed on the LHS flex quasi-pattern" in
                                      giveup_or_defer orig wl
                                        FStarC_TypeChecker_Common.Deferred_flex_flex_nonpattern
                                        uu___14
                                    else
                                      (let uu___15 = rhs in
                                       match uu___15 with
                                       | Flex (uu___16, u_rhs, uu___17) ->
                                           let uu___18 =
                                             (FStarC_Syntax_Unionfind.equiv
                                                u_lhs.FStarC_Syntax_Syntax.ctx_uvar_head
                                                u_rhs.FStarC_Syntax_Syntax.ctx_uvar_head)
                                               &&
                                               (binders_eq binders_lhs
                                                  binders_rhs) in
                                           if uu___18
                                           then
                                             let uu___19 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [] wl in
                                             solve uu___19
                                           else
                                             (let uu___20 =
                                                maximal_prefix
                                                  u_lhs.FStarC_Syntax_Syntax.ctx_uvar_binders
                                                  u_rhs.FStarC_Syntax_Syntax.ctx_uvar_binders in
                                              match uu___20 with
                                              | (ctx_w, (ctx_l, ctx_r)) ->
                                                  let gamma_w =
                                                    gamma_until
                                                      u_lhs.FStarC_Syntax_Syntax.ctx_uvar_gamma
                                                      ctx_w in
                                                  let zs =
                                                    intersect_binders gamma_w
                                                      (FStarC_Compiler_List.op_At
                                                         ctx_l binders_lhs)
                                                      (FStarC_Compiler_List.op_At
                                                         ctx_r binders_rhs) in
                                                  let new_uvar_typ =
                                                    let uu___21 =
                                                      FStarC_Syntax_Syntax.mk_Total
                                                        t_res_lhs in
                                                    FStarC_Syntax_Util.arrow
                                                      zs uu___21 in
                                                  let uu___21 =
                                                    (let uu___22 =
                                                       occurs u_lhs
                                                         new_uvar_typ in
                                                     FStar_Pervasives_Native.snd
                                                       uu___22)
                                                      ||
                                                      ((let uu___22 =
                                                          FStarC_Syntax_Unionfind.equiv
                                                            u_lhs.FStarC_Syntax_Syntax.ctx_uvar_head
                                                            u_rhs.FStarC_Syntax_Syntax.ctx_uvar_head in
                                                        Prims.op_Negation
                                                          uu___22)
                                                         &&
                                                         (let uu___22 =
                                                            occurs u_rhs
                                                              new_uvar_typ in
                                                          FStar_Pervasives_Native.snd
                                                            uu___22)) in
                                                  if uu___21
                                                  then
                                                    let uu___22 =
                                                      let uu___23 =
                                                        let uu___24 =
                                                          FStarC_Class_Show.show
                                                            uu___0
                                                            wl.defer_ok in
                                                        FStarC_Compiler_Util.format1
                                                          "flex-flex: occurs\n defer_ok=%s\n"
                                                          uu___24 in
                                                      FStarC_Thunk.mkv
                                                        uu___23 in
                                                    giveup_or_defer_flex_flex
                                                      orig wl
                                                      FStarC_TypeChecker_Common.Deferred_flex_flex_nonpattern
                                                      uu___22
                                                  else
                                                    (let uu___23 =
                                                       let uu___24 =
                                                         let uu___25 =
                                                           FStarC_Syntax_Util.ctx_uvar_should_check
                                                             u_lhs in
                                                         let uu___26 =
                                                           FStarC_Syntax_Util.ctx_uvar_should_check
                                                             u_rhs in
                                                         (uu___25, uu___26) in
                                                       match uu___24 with
                                                       | (FStarC_Syntax_Syntax.Allow_untyped
                                                          r,
                                                          FStarC_Syntax_Syntax.Allow_untyped
                                                          uu___25) ->
                                                           ((FStarC_Syntax_Syntax.Allow_untyped
                                                               r), false)
                                                       | (FStarC_Syntax_Syntax.Allow_ghost
                                                          r, uu___25) ->
                                                           ((FStarC_Syntax_Syntax.Allow_ghost
                                                               r), true)
                                                       | (uu___25,
                                                          FStarC_Syntax_Syntax.Allow_ghost
                                                          r) ->
                                                           ((FStarC_Syntax_Syntax.Allow_ghost
                                                               r), true)
                                                       | uu___25 ->
                                                           (FStarC_Syntax_Syntax.Strict,
                                                             false) in
                                                     match uu___23 with
                                                     | (new_uvar_should_check,
                                                        is_ghost) ->
                                                         let uu___24 =
                                                           new_uvar
                                                             (Prims.strcat
                                                                "flex-flex quasi:"
                                                                (Prims.strcat
                                                                   "\tlhs="
                                                                   (Prims.strcat
                                                                    u_lhs.FStarC_Syntax_Syntax.ctx_uvar_reason
                                                                    (Prims.strcat
                                                                    "\trhs="
                                                                    u_rhs.FStarC_Syntax_Syntax.ctx_uvar_reason))))
                                                             wl range gamma_w
                                                             ctx_w
                                                             new_uvar_typ
                                                             new_uvar_should_check
                                                             (if
                                                                FStar_Pervasives_Native.uu___is_Some
                                                                  u_lhs.FStarC_Syntax_Syntax.ctx_uvar_meta
                                                              then
                                                                u_lhs.FStarC_Syntax_Syntax.ctx_uvar_meta
                                                              else
                                                                u_rhs.FStarC_Syntax_Syntax.ctx_uvar_meta) in
                                                         (match uu___24 with
                                                          | (uu___25, w, wl1)
                                                              ->
                                                              let w_app =
                                                                let uu___26 =
                                                                  FStarC_Compiler_List.map
                                                                    (
                                                                    fun
                                                                    uu___27
                                                                    ->
                                                                    match uu___27
                                                                    with
                                                                    | 
                                                                    {
                                                                    FStarC_Syntax_Syntax.binder_bv
                                                                    = z;
                                                                    FStarC_Syntax_Syntax.binder_qual
                                                                    = uu___28;
                                                                    FStarC_Syntax_Syntax.binder_positivity
                                                                    = uu___29;
                                                                    FStarC_Syntax_Syntax.binder_attrs
                                                                    = uu___30;_}
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    z in
                                                                    FStarC_Syntax_Syntax.as_arg
                                                                    uu___31)
                                                                    zs in
                                                                FStarC_Syntax_Syntax.mk_Tm_app
                                                                  w uu___26
                                                                  w.FStarC_Syntax_Syntax.pos in
                                                              ((let uu___27 =
                                                                  FStarC_Compiler_Effect.op_Bang
                                                                    dbg_Rel in
                                                                if uu___27
                                                                then
                                                                  let uu___28
                                                                    =
                                                                    let uu___29
                                                                    =
                                                                    flex_t_to_string
                                                                    lhs in
                                                                    let uu___30
                                                                    =
                                                                    let uu___31
                                                                    =
                                                                    flex_t_to_string
                                                                    rhs in
                                                                    let uu___32
                                                                    =
                                                                    let uu___33
                                                                    =
                                                                    term_to_string
                                                                    w in
                                                                    let uu___34
                                                                    =
                                                                    let uu___35
                                                                    =
                                                                    FStarC_Class_Show.show
                                                                    (FStarC_Class_Show.show_list
                                                                    FStarC_Syntax_Print.showable_binder)
                                                                    (FStarC_Compiler_List.op_At
                                                                    ctx_l
                                                                    binders_lhs) in
                                                                    let uu___36
                                                                    =
                                                                    let uu___37
                                                                    =
                                                                    FStarC_Class_Show.show
                                                                    (FStarC_Class_Show.show_list
                                                                    FStarC_Syntax_Print.showable_binder)
                                                                    (FStarC_Compiler_List.op_At
                                                                    ctx_r
                                                                    binders_rhs) in
                                                                    let uu___38
                                                                    =
                                                                    let uu___39
                                                                    =
                                                                    FStarC_Class_Show.show
                                                                    (FStarC_Class_Show.show_list
                                                                    FStarC_Syntax_Print.showable_binder)
                                                                    zs in
                                                                    [uu___39] in
                                                                    uu___37
                                                                    ::
                                                                    uu___38 in
                                                                    uu___35
                                                                    ::
                                                                    uu___36 in
                                                                    uu___33
                                                                    ::
                                                                    uu___34 in
                                                                    uu___31
                                                                    ::
                                                                    uu___32 in
                                                                    uu___29
                                                                    ::
                                                                    uu___30 in
                                                                  FStarC_Compiler_Util.print
                                                                    "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                                    uu___28
                                                                else ());
                                                               (let rc =
                                                                  if is_ghost
                                                                  then
                                                                    FStarC_Syntax_Util.residual_gtot
                                                                    t_res_lhs
                                                                  else
                                                                    FStarC_Syntax_Util.residual_tot
                                                                    t_res_lhs in
                                                                let s1_sol =
                                                                  FStarC_Syntax_Util.abs
                                                                    binders_lhs
                                                                    w_app
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    rc) in
                                                                let s1 =
                                                                  TERM
                                                                    (u_lhs,
                                                                    s1_sol) in
                                                                let uu___27 =
                                                                  FStarC_Syntax_Unionfind.equiv
                                                                    u_lhs.FStarC_Syntax_Syntax.ctx_uvar_head
                                                                    u_rhs.FStarC_Syntax_Syntax.ctx_uvar_head in
                                                                if uu___27
                                                                then
                                                                  let uu___28
                                                                    =
                                                                    solve_prob
                                                                    orig
                                                                    FStar_Pervasives_Native.None
                                                                    [s1] wl1 in
                                                                  solve
                                                                    uu___28
                                                                else
                                                                  (let s2_sol
                                                                    =
                                                                    FStarC_Syntax_Util.abs
                                                                    binders_rhs
                                                                    w_app
                                                                    (FStar_Pervasives_Native.Some
                                                                    rc) in
                                                                   let s2 =
                                                                    TERM
                                                                    (u_rhs,
                                                                    s2_sol) in
                                                                   let uu___29
                                                                    =
                                                                    solve_prob
                                                                    orig
                                                                    FStar_Pervasives_Native.None
                                                                    [s1; s2]
                                                                    wl1 in
                                                                   solve
                                                                    uu___29))))))))
                           | uu___8 ->
                               let uu___9 =
                                 FStarC_Thunk.mkv "flex-flex: non-patterns" in
                               giveup_or_defer orig wl
                                 FStarC_TypeChecker_Common.Deferred_flex_flex_nonpattern
                                 uu___9)))
and (solve_t' : tprob -> worklist -> solution) =
  fun problem ->
    fun wl ->
      def_check_prob "solve_t'.1" (FStarC_TypeChecker_Common.TProb problem);
      (let giveup_or_defer1 orig msg = giveup_or_defer orig wl msg in
       let rigid_heads_match need_unif torig wl1 t1 t2 =
         let orig = FStarC_TypeChecker_Common.TProb torig in
         let env = p_env wl1 orig in
         (let uu___2 = FStarC_Compiler_Effect.op_Bang dbg_Rel in
          if uu___2
          then
            let uu___3 =
              FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t1 in
            let uu___4 =
              FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term t1 in
            let uu___5 =
              FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t2 in
            let uu___6 =
              FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term t2 in
            FStarC_Compiler_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
              (if need_unif then "need unification" else "match") uu___3
              uu___4 uu___5 uu___6
          else ());
         (let uu___2 = FStarC_Syntax_Util.head_and_args t1 in
          match uu___2 with
          | (head1, args1) ->
              let uu___3 = FStarC_Syntax_Util.head_and_args t2 in
              (match uu___3 with
               | (head2, args2) ->
                   let need_unif1 =
                     match (((head1.FStarC_Syntax_Syntax.n), args1),
                             ((head2.FStarC_Syntax_Syntax.n), args2))
                     with
                     | ((FStarC_Syntax_Syntax.Tm_uinst (uu___4, us1),
                         uu___5::uu___6),
                        (FStarC_Syntax_Syntax.Tm_uinst (uu___7, us2),
                         uu___8::uu___9)) ->
                         let uu___10 =
                           (FStarC_Compiler_List.for_all
                              (fun u ->
                                 let uu___11 = universe_has_max env u in
                                 Prims.op_Negation uu___11) us1)
                             &&
                             (FStarC_Compiler_List.for_all
                                (fun u ->
                                   let uu___11 = universe_has_max env u in
                                   Prims.op_Negation uu___11) us2) in
                         if uu___10 then need_unif else true
                     | uu___4 -> need_unif in
                   let solve_head_then wl2 k =
                     if need_unif1
                     then k true wl2
                     else
                       (let uu___5 = solve_maybe_uinsts orig head1 head2 wl2 in
                        match uu___5 with
                        | USolved wl3 -> k true wl3
                        | UFailed msg -> giveup wl2 msg orig
                        | UDeferred wl3 ->
                            let uu___6 =
                              defer_lit
                                FStarC_TypeChecker_Common.Deferred_univ_constraint
                                "universe constraints" orig wl3 in
                            k false uu___6) in
                   let nargs = FStarC_Compiler_List.length args1 in
                   if nargs <> (FStarC_Compiler_List.length args2)
                   then
                     let uu___4 =
                       mklstr
                         (fun uu___5 ->
                            let uu___6 =
                              FStarC_Class_Show.show
                                FStarC_Syntax_Print.showable_term head1 in
                            let uu___7 =
                              FStarC_Class_Show.show
                                (FStarC_Class_Show.show_list
                                   (FStarC_Class_Show.show_tuple2
                                      FStarC_Syntax_Print.showable_term
                                      FStarC_Syntax_Print.showable_aqual))
                                args1 in
                            let uu___8 =
                              FStarC_Class_Show.show
                                FStarC_Syntax_Print.showable_term head2 in
                            let uu___9 =
                              FStarC_Class_Show.show
                                (FStarC_Class_Show.show_list
                                   (FStarC_Class_Show.show_tuple2
                                      FStarC_Syntax_Print.showable_term
                                      FStarC_Syntax_Print.showable_aqual))
                                args2 in
                            FStarC_Compiler_Util.format4
                              "unequal number of arguments: %s[%s] and %s[%s]"
                              uu___6 uu___7 uu___8 uu___9) in
                     giveup wl1 uu___4 orig
                   else
                     (let uu___5 =
                        (nargs = Prims.int_zero) ||
                          (let uu___6 =
                             FStarC_TypeChecker_TermEqAndSimplify.eq_args env
                               args1 args2 in
                           uu___6 =
                             FStarC_TypeChecker_TermEqAndSimplify.Equal) in
                      if uu___5
                      then
                        (if need_unif1
                         then
                           solve_t
                             {
                               FStarC_TypeChecker_Common.pid =
                                 (problem.FStarC_TypeChecker_Common.pid);
                               FStarC_TypeChecker_Common.lhs = head1;
                               FStarC_TypeChecker_Common.relation =
                                 (problem.FStarC_TypeChecker_Common.relation);
                               FStarC_TypeChecker_Common.rhs = head2;
                               FStarC_TypeChecker_Common.element =
                                 (problem.FStarC_TypeChecker_Common.element);
                               FStarC_TypeChecker_Common.logical_guard =
                                 (problem.FStarC_TypeChecker_Common.logical_guard);
                               FStarC_TypeChecker_Common.logical_guard_uvar =
                                 (problem.FStarC_TypeChecker_Common.logical_guard_uvar);
                               FStarC_TypeChecker_Common.reason =
                                 (problem.FStarC_TypeChecker_Common.reason);
                               FStarC_TypeChecker_Common.loc =
                                 (problem.FStarC_TypeChecker_Common.loc);
                               FStarC_TypeChecker_Common.rank =
                                 (problem.FStarC_TypeChecker_Common.rank);
                               FStarC_TypeChecker_Common.logical =
                                 (problem.FStarC_TypeChecker_Common.logical)
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
                                    solve uu___7
                                  else solve wl2))
                      else
                        (let uu___7 = base_and_refinement env t1 in
                         match uu___7 with
                         | (base1, refinement1) ->
                             let uu___8 = base_and_refinement env t2 in
                             (match uu___8 with
                              | (base2, refinement2) ->
                                  (match (refinement1, refinement2) with
                                   | (FStar_Pervasives_Native.None,
                                      FStar_Pervasives_Native.None) ->
                                       let mk_sub_probs wl2 =
                                         let argp =
                                           if need_unif1
                                           then
                                             FStarC_Compiler_List.zip
                                               ((head1,
                                                  FStar_Pervasives_Native.None)
                                               :: args1)
                                               ((head2,
                                                  FStar_Pervasives_Native.None)
                                               :: args2)
                                           else
                                             FStarC_Compiler_List.zip args1
                                               args2 in
                                         let uu___9 =
                                           FStarC_Compiler_List.fold_right
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
                                                          FStarC_TypeChecker_Common.EQ
                                                          a2
                                                          FStar_Pervasives_Native.None
                                                          "index" in
                                                      (match uu___14 with
                                                       | (prob', wl4) ->
                                                           (((FStarC_TypeChecker_Common.TProb
                                                                prob') ::
                                                             probs), wl4)))
                                             argp ([], wl2) in
                                         match uu___9 with
                                         | (subprobs, wl3) ->
                                             ((let uu___11 =
                                                 FStarC_Compiler_Effect.op_Bang
                                                   dbg_Rel in
                                               if uu___11
                                               then
                                                 let uu___12 =
                                                   FStarC_Compiler_Util.string_of_bool
                                                     wl3.smt_ok in
                                                 let uu___13 =
                                                   (FStarC_Common.string_of_list
                                                      ())
                                                     (prob_to_string env)
                                                     subprobs in
                                                 FStarC_Compiler_Util.print2
                                                   "Adding subproblems for arguments (smtok=%s): %s"
                                                   uu___12 uu___13
                                               else ());
                                              (let uu___12 =
                                                 FStarC_Options.defensive () in
                                               if uu___12
                                               then
                                                 FStarC_Compiler_List.iter
                                                   (def_check_prob
                                                      "solve_t' subprobs")
                                                   subprobs
                                               else ());
                                              (subprobs, wl3)) in
                                       let solve_sub_probs env1 wl2 =
                                         solve_head_then wl2
                                           (fun ok ->
                                              fun wl3 ->
                                                if Prims.op_Negation ok
                                                then solve wl3
                                                else
                                                  (let uu___10 =
                                                     mk_sub_probs wl3 in
                                                   match uu___10 with
                                                   | (subprobs, wl4) ->
                                                       let formula =
                                                         let uu___11 =
                                                           FStarC_Compiler_List.map
                                                             (fun p ->
                                                                p_guard p)
                                                             subprobs in
                                                         FStarC_Syntax_Util.mk_conj_l
                                                           uu___11 in
                                                       let wl5 =
                                                         solve_prob orig
                                                           (FStar_Pervasives_Native.Some
                                                              formula) [] wl4 in
                                                       let uu___11 =
                                                         attempt subprobs wl5 in
                                                       solve uu___11)) in
                                       let solve_sub_probs_no_smt wl2 =
                                         solve_head_then wl2
                                           (fun ok ->
                                              fun wl3 ->
                                                let uu___9 = mk_sub_probs wl3 in
                                                match uu___9 with
                                                | (subprobs, wl4) ->
                                                    let formula =
                                                      let uu___10 =
                                                        FStarC_Compiler_List.map
                                                          (fun p -> p_guard p)
                                                          subprobs in
                                                      FStarC_Syntax_Util.mk_conj_l
                                                        uu___10 in
                                                    let wl5 =
                                                      solve_prob orig
                                                        (FStar_Pervasives_Native.Some
                                                           formula) [] wl4 in
                                                    let uu___10 =
                                                      attempt subprobs wl5 in
                                                    solve uu___10) in
                                       let unfold_and_retry d wl2 uu___9 =
                                         match uu___9 with
                                         | (prob, reason) ->
                                             ((let uu___11 =
                                                 FStarC_Compiler_Effect.op_Bang
                                                   dbg_Rel in
                                               if uu___11
                                               then
                                                 let uu___12 =
                                                   prob_to_string env orig in
                                                 let uu___13 =
                                                   FStarC_Thunk.force reason in
                                                 FStarC_Compiler_Util.print2
                                                   "Failed to solve %s because a sub-problem is not solvable without SMT because %s"
                                                   uu___12 uu___13
                                               else ());
                                              (let env1 = p_env wl2 prob in
                                               let uu___11 =
                                                 let uu___12 =
                                                   FStarC_TypeChecker_Normalize.unfold_head_once
                                                     env1 t1 in
                                                 let uu___13 =
                                                   FStarC_TypeChecker_Normalize.unfold_head_once
                                                     env1 t2 in
                                                 (uu___12, uu___13) in
                                               match uu___11 with
                                               | (FStar_Pervasives_Native.Some
                                                  t1',
                                                  FStar_Pervasives_Native.Some
                                                  t2') ->
                                                   let uu___12 =
                                                     FStarC_Syntax_Util.head_and_args
                                                       t1' in
                                                   (match uu___12 with
                                                    | (head1', uu___13) ->
                                                        let uu___14 =
                                                          FStarC_Syntax_Util.head_and_args
                                                            t2' in
                                                        (match uu___14 with
                                                         | (head2', uu___15)
                                                             ->
                                                             let uu___16 =
                                                               let uu___17 =
                                                                 FStarC_TypeChecker_TermEqAndSimplify.eq_tm
                                                                   env1
                                                                   head1'
                                                                   head1 in
                                                               let uu___18 =
                                                                 FStarC_TypeChecker_TermEqAndSimplify.eq_tm
                                                                   env1
                                                                   head2'
                                                                   head2 in
                                                               (uu___17,
                                                                 uu___18) in
                                                             (match uu___16
                                                              with
                                                              | (FStarC_TypeChecker_TermEqAndSimplify.Equal,
                                                                 FStarC_TypeChecker_TermEqAndSimplify.Equal)
                                                                  ->
                                                                  ((let uu___18
                                                                    =
                                                                    FStarC_Compiler_Effect.op_Bang
                                                                    dbg_Rel in
                                                                    if
                                                                    uu___18
                                                                    then
                                                                    let uu___19
                                                                    =
                                                                    FStarC_Class_Show.show
                                                                    FStarC_Syntax_Print.showable_term
                                                                    t1 in
                                                                    let uu___20
                                                                    =
                                                                    FStarC_Class_Show.show
                                                                    FStarC_Syntax_Print.showable_term
                                                                    t1' in
                                                                    let uu___21
                                                                    =
                                                                    FStarC_Class_Show.show
                                                                    FStarC_Syntax_Print.showable_term
                                                                    t2 in
                                                                    let uu___22
                                                                    =
                                                                    FStarC_Class_Show.show
                                                                    FStarC_Syntax_Print.showable_term
                                                                    t2' in
                                                                    FStarC_Compiler_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu___19
                                                                    uu___20
                                                                    uu___21
                                                                    uu___22
                                                                    else ());
                                                                   solve_sub_probs
                                                                    env1 wl2)
                                                              | uu___17 ->
                                                                  let torig'
                                                                    =
                                                                    {
                                                                    FStarC_TypeChecker_Common.pid
                                                                    =
                                                                    (torig.FStarC_TypeChecker_Common.pid);
                                                                    FStarC_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStarC_TypeChecker_Common.relation
                                                                    =
                                                                    (torig.FStarC_TypeChecker_Common.relation);
                                                                    FStarC_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStarC_TypeChecker_Common.element
                                                                    =
                                                                    (torig.FStarC_TypeChecker_Common.element);
                                                                    FStarC_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (torig.FStarC_TypeChecker_Common.logical_guard);
                                                                    FStarC_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (torig.FStarC_TypeChecker_Common.logical_guard_uvar);
                                                                    FStarC_TypeChecker_Common.reason
                                                                    =
                                                                    (torig.FStarC_TypeChecker_Common.reason);
                                                                    FStarC_TypeChecker_Common.loc
                                                                    =
                                                                    (torig.FStarC_TypeChecker_Common.loc);
                                                                    FStarC_TypeChecker_Common.rank
                                                                    =
                                                                    (torig.FStarC_TypeChecker_Common.rank);
                                                                    FStarC_TypeChecker_Common.logical
                                                                    =
                                                                    (torig.FStarC_TypeChecker_Common.logical)
                                                                    } in
                                                                  ((let uu___19
                                                                    =
                                                                    FStarC_Compiler_Effect.op_Bang
                                                                    dbg_Rel in
                                                                    if
                                                                    uu___19
                                                                    then
                                                                    let uu___20
                                                                    =
                                                                    prob_to_string
                                                                    env1
                                                                    (FStarC_TypeChecker_Common.TProb
                                                                    torig') in
                                                                    FStarC_Compiler_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu___20
                                                                    else ());
                                                                   solve_t
                                                                    torig'
                                                                    wl2))))
                                               | uu___12 ->
                                                   solve_sub_probs env1 wl2)) in
                                       let d =
                                         let uu___9 =
                                           FStarC_TypeChecker_Env.delta_depth_of_term
                                             env head1 in
                                         FStarC_TypeChecker_Common.decr_delta_depth
                                           uu___9 in
                                       let treat_as_injective =
                                         let uu___9 =
                                           let uu___10 =
                                             FStarC_Syntax_Util.un_uinst
                                               head1 in
                                           uu___10.FStarC_Syntax_Syntax.n in
                                         match uu___9 with
                                         | FStarC_Syntax_Syntax.Tm_fvar fv ->
                                             FStarC_TypeChecker_Env.fv_has_attr
                                               env fv
                                               FStarC_Parser_Const.unifier_hint_injective_lid
                                         | uu___10 -> false in
                                       (match d with
                                        | FStar_Pervasives_Native.Some d1
                                            when
                                            wl1.smt_ok &&
                                              (Prims.op_Negation
                                                 treat_as_injective)
                                            ->
                                            try_solve_without_smt_or_else wl1
                                              solve_sub_probs_no_smt
                                              (unfold_and_retry d1)
                                        | uu___9 -> solve_sub_probs env wl1)
                                   | uu___9 ->
                                       let lhs =
                                         force_refinement
                                           (base1, refinement1) in
                                       let rhs =
                                         force_refinement
                                           (base2, refinement2) in
                                       solve_t'
                                         {
                                           FStarC_TypeChecker_Common.pid =
                                             (problem.FStarC_TypeChecker_Common.pid);
                                           FStarC_TypeChecker_Common.lhs =
                                             lhs;
                                           FStarC_TypeChecker_Common.relation
                                             =
                                             (problem.FStarC_TypeChecker_Common.relation);
                                           FStarC_TypeChecker_Common.rhs =
                                             rhs;
                                           FStarC_TypeChecker_Common.element
                                             =
                                             (problem.FStarC_TypeChecker_Common.element);
                                           FStarC_TypeChecker_Common.logical_guard
                                             =
                                             (problem.FStarC_TypeChecker_Common.logical_guard);
                                           FStarC_TypeChecker_Common.logical_guard_uvar
                                             =
                                             (problem.FStarC_TypeChecker_Common.logical_guard_uvar);
                                           FStarC_TypeChecker_Common.reason =
                                             (problem.FStarC_TypeChecker_Common.reason);
                                           FStarC_TypeChecker_Common.loc =
                                             (problem.FStarC_TypeChecker_Common.loc);
                                           FStarC_TypeChecker_Common.rank =
                                             (problem.FStarC_TypeChecker_Common.rank);
                                           FStarC_TypeChecker_Common.logical
                                             =
                                             (problem.FStarC_TypeChecker_Common.logical)
                                         } wl1)))))) in
       let try_match_heuristic orig wl1 s1 s2 t1t2_opt =
         let env = p_env wl1 orig in
         let try_solve_branch scrutinee p =
           let uu___1 = destruct_flex_t scrutinee wl1 in
           match uu___1 with
           | (Flex (_t, uv, _args), wl2) ->
               let uu___2 =
                 FStarC_TypeChecker_PatternUtils.pat_as_exp true true env p in
               (match uu___2 with
                | (xs, pat_term, g_pat_as_exp, uu___3) ->
                    let uu___4 =
                      FStarC_Compiler_List.fold_left
                        (fun uu___5 ->
                           fun x ->
                             match uu___5 with
                             | (subst, wl3) ->
                                 let t_x =
                                   FStarC_Syntax_Subst.subst subst
                                     x.FStarC_Syntax_Syntax.sort in
                                 let uu___6 = copy_uvar uv [] t_x wl3 in
                                 (match uu___6 with
                                  | (uu___7, u, wl4) ->
                                      let subst1 =
                                        (FStarC_Syntax_Syntax.NT (x, u)) ::
                                        subst in
                                      (subst1, wl4))) ([], wl2) xs in
                    (match uu___4 with
                     | (subst, wl3) ->
                         let pat_term1 =
                           FStarC_Syntax_Subst.subst subst pat_term in
                         let uu___5 =
                           let must_tot = false in
                           let scrutinee_t =
                             let uu___6 =
                               let uu___7 =
                                 let uu___8 =
                                   env.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                     env scrutinee must_tot in
                                 FStar_Pervasives_Native.fst uu___8 in
                               FStarC_TypeChecker_Normalize.normalize_refinement
                                 FStarC_TypeChecker_Normalize.whnf_steps env
                                 uu___7 in
                             FStarC_Syntax_Util.unrefine uu___6 in
                           (let uu___7 =
                              FStarC_Compiler_Effect.op_Bang dbg_Rel in
                            if uu___7
                            then
                              let uu___8 =
                                FStarC_Class_Show.show
                                  FStarC_Syntax_Print.showable_term pat_term1 in
                              FStarC_Compiler_Util.print1
                                "Match heuristic, typechecking the pattern term: %s {\n\n"
                                uu___8
                            else ());
                           (let uu___7 =
                              let uu___8 =
                                FStarC_TypeChecker_Env.set_expected_typ env
                                  scrutinee_t in
                              env.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term
                                uu___8 pat_term1 must_tot in
                            match uu___7 with
                            | (pat_term2, pat_term_t, g_pat_term) ->
                                ((let uu___9 =
                                    FStarC_Compiler_Effect.op_Bang dbg_Rel in
                                  if uu___9
                                  then
                                    let uu___10 =
                                      FStarC_Class_Show.show
                                        FStarC_Syntax_Print.showable_term
                                        pat_term2 in
                                    let uu___11 =
                                      FStarC_Class_Show.show
                                        FStarC_Syntax_Print.showable_term
                                        pat_term_t in
                                    FStarC_Compiler_Util.print2
                                      "} Match heuristic, typechecked pattern term to %s and type %s\n"
                                      uu___10 uu___11
                                  else ());
                                 (pat_term2, g_pat_term))) in
                         (match uu___5 with
                          | (pat_term2, g_pat_term) ->
                              let uu___6 =
                                let uu___7 = simplify_guard env g_pat_term in
                                FStarC_TypeChecker_Env.is_trivial_guard_formula
                                  uu___7 in
                              if uu___6
                              then
                                let uu___7 =
                                  new_problem wl3 env scrutinee
                                    FStarC_TypeChecker_Common.EQ pat_term2
                                    FStar_Pervasives_Native.None
                                    scrutinee.FStarC_Syntax_Syntax.pos
                                    "match heuristic" in
                                (match uu___7 with
                                 | (prob, wl4) ->
                                     let wl' =
                                       extend_wl
                                         {
                                           attempting =
                                             [FStarC_TypeChecker_Common.TProb
                                                prob];
                                           wl_deferred =
                                             (Obj.magic
                                                (FStarC_Class_Listlike.empty
                                                   ()
                                                   (Obj.magic
                                                      (FStarC_Compiler_CList.listlike_clist
                                                         ()))));
                                           wl_deferred_to_tac =
                                             (wl4.wl_deferred_to_tac);
                                           ctr = (wl4.ctr);
                                           defer_ok = NoDefer;
                                           smt_ok = false;
                                           umax_heuristic_ok =
                                             (wl4.umax_heuristic_ok);
                                           tcenv = (wl4.tcenv);
                                           wl_implicits =
                                             (Obj.magic
                                                (FStarC_Class_Listlike.empty
                                                   ()
                                                   (Obj.magic
                                                      (FStarC_Compiler_CList.listlike_clist
                                                         ()))));
                                           repr_subcomp_allowed =
                                             (wl4.repr_subcomp_allowed);
                                           typeclass_variables =
                                             (wl4.typeclass_variables)
                                         }
                                         g_pat_term.FStarC_TypeChecker_Common.deferred
                                         g_pat_term.FStarC_TypeChecker_Common.deferred_to_tac
                                         (Obj.magic
                                            (FStarC_Class_Listlike.empty ()
                                               (Obj.magic
                                                  (FStarC_Compiler_CList.listlike_clist
                                                     ())))) in
                                     let tx =
                                       FStarC_Syntax_Unionfind.new_transaction
                                         () in
                                     let uu___8 = solve wl' in
                                     (match uu___8 with
                                      | Success (uu___9, defer_to_tac, imps)
                                          ->
                                          let wl'1 =
                                            {
                                              attempting = [orig];
                                              wl_deferred = (wl'.wl_deferred);
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
                                                (wl'.repr_subcomp_allowed);
                                              typeclass_variables =
                                                (wl'.typeclass_variables)
                                            } in
                                          let uu___10 = solve wl'1 in
                                          (match uu___10 with
                                           | Success
                                               (uu___11, defer_to_tac',
                                                imps')
                                               ->
                                               (FStarC_Syntax_Unionfind.commit
                                                  tx;
                                                (let uu___13 =
                                                   let uu___14 =
                                                     FStarC_Class_Monoid.op_Plus_Plus
                                                       (FStarC_Compiler_CList.monoid_clist
                                                          ()) defer_to_tac
                                                       defer_to_tac' in
                                                   let uu___15 =
                                                     let uu___16 =
                                                       let uu___17 =
                                                         FStarC_Class_Monoid.op_Plus_Plus
                                                           (FStarC_Compiler_CList.monoid_clist
                                                              ()) imps imps' in
                                                       FStarC_Class_Monoid.op_Plus_Plus
                                                         (FStarC_Compiler_CList.monoid_clist
                                                            ()) uu___17
                                                         g_pat_as_exp.FStarC_TypeChecker_Common.implicits in
                                                     FStarC_Class_Monoid.op_Plus_Plus
                                                       (FStarC_Compiler_CList.monoid_clist
                                                          ()) uu___16
                                                       g_pat_term.FStarC_TypeChecker_Common.implicits in
                                                   extend_wl wl4
                                                     (Obj.magic
                                                        (FStarC_Class_Listlike.empty
                                                           ()
                                                           (Obj.magic
                                                              (FStarC_Compiler_CList.listlike_clist
                                                                 ()))))
                                                     uu___14 uu___15 in
                                                 FStar_Pervasives_Native.Some
                                                   uu___13))
                                           | Failed uu___11 ->
                                               (FStarC_Syntax_Unionfind.rollback
                                                  tx;
                                                FStar_Pervasives_Native.None))
                                      | uu___9 ->
                                          (FStarC_Syntax_Unionfind.rollback
                                             tx;
                                           FStar_Pervasives_Native.None)))
                              else FStar_Pervasives_Native.None))) in
         match t1t2_opt with
         | FStar_Pervasives_Native.None ->
             FStar_Pervasives.Inr FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some (t1, t2) ->
             ((let uu___2 = FStarC_Compiler_Effect.op_Bang dbg_Rel in
               if uu___2
               then
                 let uu___3 =
                   FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                     t1 in
                 let uu___4 =
                   FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                     t2 in
                 FStarC_Compiler_Util.print2
                   "Trying match heuristic for %s vs. %s\n" uu___3 uu___4
               else ());
              (let uu___2 =
                 let uu___3 =
                   let uu___4 = FStarC_Syntax_Util.unmeta t1 in (s1, uu___4) in
                 let uu___4 =
                   let uu___5 = FStarC_Syntax_Util.unmeta t2 in (s2, uu___5) in
                 (uu___3, uu___4) in
               match uu___2 with
               | ((uu___3,
                   {
                     FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_match
                       { FStarC_Syntax_Syntax.scrutinee = scrutinee;
                         FStarC_Syntax_Syntax.ret_opt = uu___4;
                         FStarC_Syntax_Syntax.brs = branches;
                         FStarC_Syntax_Syntax.rc_opt1 = uu___5;_};
                     FStarC_Syntax_Syntax.pos = uu___6;
                     FStarC_Syntax_Syntax.vars = uu___7;
                     FStarC_Syntax_Syntax.hash_code = uu___8;_}),
                  (s, t)) ->
                   let uu___9 =
                     let uu___10 = is_flex scrutinee in
                     Prims.op_Negation uu___10 in
                   if uu___9
                   then
                     ((let uu___11 = FStarC_Compiler_Effect.op_Bang dbg_Rel in
                       if uu___11
                       then
                         let uu___12 =
                           FStarC_Class_Show.show
                             FStarC_Syntax_Print.showable_term scrutinee in
                         FStarC_Compiler_Util.print1
                           "match head %s is not a flex term\n" uu___12
                       else ());
                      FStar_Pervasives.Inr FStar_Pervasives_Native.None)
                   else
                     if wl1.defer_ok = DeferAny
                     then
                       ((let uu___12 = FStarC_Compiler_Effect.op_Bang dbg_Rel in
                         if uu___12
                         then
                           FStarC_Compiler_Util.print_string
                             "Deferring ... \n"
                         else ());
                        FStar_Pervasives.Inl "defer")
                     else
                       ((let uu___13 = FStarC_Compiler_Effect.op_Bang dbg_Rel in
                         if uu___13
                         then
                           let uu___14 =
                             FStarC_Class_Show.show
                               FStarC_Syntax_Print.showable_term scrutinee in
                           let uu___15 =
                             FStarC_Class_Show.show
                               FStarC_Syntax_Print.showable_term t in
                           FStarC_Compiler_Util.print2
                             "Heuristic applicable with scrutinee %s and other side = %s\n"
                             uu___14 uu___15
                         else ());
                        (let pat_discriminates uu___13 =
                           match uu___13 with
                           | ({
                                FStarC_Syntax_Syntax.v =
                                  FStarC_Syntax_Syntax.Pat_constant uu___14;
                                FStarC_Syntax_Syntax.p = uu___15;_},
                              FStar_Pervasives_Native.None, uu___16) -> true
                           | ({
                                FStarC_Syntax_Syntax.v =
                                  FStarC_Syntax_Syntax.Pat_cons uu___14;
                                FStarC_Syntax_Syntax.p = uu___15;_},
                              FStar_Pervasives_Native.None, uu___16) -> true
                           | uu___14 -> false in
                         let head_matching_branch =
                           FStarC_Compiler_Util.try_find
                             (fun b ->
                                if pat_discriminates b
                                then
                                  let uu___13 =
                                    FStarC_Syntax_Subst.open_branch b in
                                  match uu___13 with
                                  | (uu___14, uu___15, t') ->
                                      let uu___16 =
                                        head_matches_delta (p_env wl1 orig)
                                          (p_logical orig) wl1.smt_ok s t' in
                                      (match uu___16 with
                                       | (FullMatch, uu___17) -> true
                                       | (HeadMatch uu___17, uu___18) -> true
                                       | uu___17 -> false)
                                else false) branches in
                         match head_matching_branch with
                         | FStar_Pervasives_Native.None ->
                             ((let uu___14 =
                                 FStarC_Compiler_Effect.op_Bang dbg_Rel in
                               if uu___14
                               then
                                 FStarC_Compiler_Util.print_string
                                   "No head_matching branch\n"
                               else ());
                              (let try_branches =
                                 let uu___14 =
                                   FStarC_Compiler_Util.prefix_until
                                     (fun b ->
                                        Prims.op_Negation
                                          (pat_discriminates b)) branches in
                                 match uu___14 with
                                 | FStar_Pervasives_Native.Some
                                     (branches1, uu___15, uu___16) ->
                                     branches1
                                 | uu___15 -> branches in
                               let uu___14 =
                                 FStarC_Compiler_Util.find_map try_branches
                                   (fun b ->
                                      let uu___15 =
                                        FStarC_Syntax_Subst.open_branch b in
                                      match uu___15 with
                                      | (p, uu___16, uu___17) ->
                                          try_solve_branch scrutinee p) in
                               FStar_Pervasives.Inr uu___14))
                         | FStar_Pervasives_Native.Some b ->
                             let uu___13 = FStarC_Syntax_Subst.open_branch b in
                             (match uu___13 with
                              | (p, uu___14, e) ->
                                  ((let uu___16 =
                                      FStarC_Compiler_Effect.op_Bang dbg_Rel in
                                    if uu___16
                                    then
                                      let uu___17 =
                                        FStarC_Class_Show.show
                                          FStarC_Syntax_Print.showable_pat p in
                                      let uu___18 =
                                        FStarC_Class_Show.show
                                          FStarC_Syntax_Print.showable_term e in
                                      FStarC_Compiler_Util.print2
                                        "Found head matching branch %s -> %s\n"
                                        uu___17 uu___18
                                    else ());
                                   (let uu___16 =
                                      try_solve_branch scrutinee p in
                                    FStar_Pervasives.Inr uu___16)))))
               | ((s, t),
                  (uu___3,
                   {
                     FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_match
                       { FStarC_Syntax_Syntax.scrutinee = scrutinee;
                         FStarC_Syntax_Syntax.ret_opt = uu___4;
                         FStarC_Syntax_Syntax.brs = branches;
                         FStarC_Syntax_Syntax.rc_opt1 = uu___5;_};
                     FStarC_Syntax_Syntax.pos = uu___6;
                     FStarC_Syntax_Syntax.vars = uu___7;
                     FStarC_Syntax_Syntax.hash_code = uu___8;_}))
                   ->
                   let uu___9 =
                     let uu___10 = is_flex scrutinee in
                     Prims.op_Negation uu___10 in
                   if uu___9
                   then
                     ((let uu___11 = FStarC_Compiler_Effect.op_Bang dbg_Rel in
                       if uu___11
                       then
                         let uu___12 =
                           FStarC_Class_Show.show
                             FStarC_Syntax_Print.showable_term scrutinee in
                         FStarC_Compiler_Util.print1
                           "match head %s is not a flex term\n" uu___12
                       else ());
                      FStar_Pervasives.Inr FStar_Pervasives_Native.None)
                   else
                     if wl1.defer_ok = DeferAny
                     then
                       ((let uu___12 = FStarC_Compiler_Effect.op_Bang dbg_Rel in
                         if uu___12
                         then
                           FStarC_Compiler_Util.print_string
                             "Deferring ... \n"
                         else ());
                        FStar_Pervasives.Inl "defer")
                     else
                       ((let uu___13 = FStarC_Compiler_Effect.op_Bang dbg_Rel in
                         if uu___13
                         then
                           let uu___14 =
                             FStarC_Class_Show.show
                               FStarC_Syntax_Print.showable_term scrutinee in
                           let uu___15 =
                             FStarC_Class_Show.show
                               FStarC_Syntax_Print.showable_term t in
                           FStarC_Compiler_Util.print2
                             "Heuristic applicable with scrutinee %s and other side = %s\n"
                             uu___14 uu___15
                         else ());
                        (let pat_discriminates uu___13 =
                           match uu___13 with
                           | ({
                                FStarC_Syntax_Syntax.v =
                                  FStarC_Syntax_Syntax.Pat_constant uu___14;
                                FStarC_Syntax_Syntax.p = uu___15;_},
                              FStar_Pervasives_Native.None, uu___16) -> true
                           | ({
                                FStarC_Syntax_Syntax.v =
                                  FStarC_Syntax_Syntax.Pat_cons uu___14;
                                FStarC_Syntax_Syntax.p = uu___15;_},
                              FStar_Pervasives_Native.None, uu___16) -> true
                           | uu___14 -> false in
                         let head_matching_branch =
                           FStarC_Compiler_Util.try_find
                             (fun b ->
                                if pat_discriminates b
                                then
                                  let uu___13 =
                                    FStarC_Syntax_Subst.open_branch b in
                                  match uu___13 with
                                  | (uu___14, uu___15, t') ->
                                      let uu___16 =
                                        head_matches_delta (p_env wl1 orig)
                                          (p_logical orig) wl1.smt_ok s t' in
                                      (match uu___16 with
                                       | (FullMatch, uu___17) -> true
                                       | (HeadMatch uu___17, uu___18) -> true
                                       | uu___17 -> false)
                                else false) branches in
                         match head_matching_branch with
                         | FStar_Pervasives_Native.None ->
                             ((let uu___14 =
                                 FStarC_Compiler_Effect.op_Bang dbg_Rel in
                               if uu___14
                               then
                                 FStarC_Compiler_Util.print_string
                                   "No head_matching branch\n"
                               else ());
                              (let try_branches =
                                 let uu___14 =
                                   FStarC_Compiler_Util.prefix_until
                                     (fun b ->
                                        Prims.op_Negation
                                          (pat_discriminates b)) branches in
                                 match uu___14 with
                                 | FStar_Pervasives_Native.Some
                                     (branches1, uu___15, uu___16) ->
                                     branches1
                                 | uu___15 -> branches in
                               let uu___14 =
                                 FStarC_Compiler_Util.find_map try_branches
                                   (fun b ->
                                      let uu___15 =
                                        FStarC_Syntax_Subst.open_branch b in
                                      match uu___15 with
                                      | (p, uu___16, uu___17) ->
                                          try_solve_branch scrutinee p) in
                               FStar_Pervasives.Inr uu___14))
                         | FStar_Pervasives_Native.Some b ->
                             let uu___13 = FStarC_Syntax_Subst.open_branch b in
                             (match uu___13 with
                              | (p, uu___14, e) ->
                                  ((let uu___16 =
                                      FStarC_Compiler_Effect.op_Bang dbg_Rel in
                                    if uu___16
                                    then
                                      let uu___17 =
                                        FStarC_Class_Show.show
                                          FStarC_Syntax_Print.showable_pat p in
                                      let uu___18 =
                                        FStarC_Class_Show.show
                                          FStarC_Syntax_Print.showable_term e in
                                      FStarC_Compiler_Util.print2
                                        "Found head matching branch %s -> %s\n"
                                        uu___17 uu___18
                                    else ());
                                   (let uu___16 =
                                      try_solve_branch scrutinee p in
                                    FStar_Pervasives.Inr uu___16)))))
               | uu___3 ->
                   ((let uu___5 = FStarC_Compiler_Effect.op_Bang dbg_Rel in
                     if uu___5
                     then
                       let uu___6 =
                         FStarC_Class_Tagged.tag_of
                           FStarC_Syntax_Syntax.tagged_term t1 in
                       let uu___7 =
                         FStarC_Class_Tagged.tag_of
                           FStarC_Syntax_Syntax.tagged_term t2 in
                       FStarC_Compiler_Util.print2
                         "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                         uu___6 uu___7
                     else ());
                    FStar_Pervasives.Inr FStar_Pervasives_Native.None))) in
       let rigid_rigid_delta torig wl1 head1 head2 t1 t2 =
         let orig = FStarC_TypeChecker_Common.TProb torig in
         (let uu___2 = FStarC_Compiler_Effect.op_Bang dbg_RelDelta in
          if uu___2
          then
            let uu___3 =
              FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term t1 in
            let uu___4 =
              FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term t2 in
            let uu___5 =
              FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t1 in
            let uu___6 =
              FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t2 in
            FStarC_Compiler_Util.print4
              "rigid_rigid_delta of %s-%s (%s, %s)\n" uu___3 uu___4 uu___5
              uu___6
          else ());
         (let uu___2 =
            head_matches_delta (p_env wl1 orig) (p_logical orig) wl1.smt_ok
              t1 t2 in
          match uu___2 with
          | (m, o) ->
              (match (m, o) with
               | (MisMatch uu___3, uu___4) ->
                   let try_reveal_hide t11 t21 =
                     let payload_of_hide_reveal h args =
                       match ((h.FStarC_Syntax_Syntax.n), args) with
                       | (FStarC_Syntax_Syntax.Tm_uinst (uu___5, u::[]),
                          (ty, FStar_Pervasives_Native.Some
                           { FStarC_Syntax_Syntax.aqual_implicit = true;
                             FStarC_Syntax_Syntax.aqual_attributes = uu___6;_})::
                          (t, uu___7)::[]) ->
                           FStar_Pervasives_Native.Some (u, ty, t)
                       | uu___5 -> FStar_Pervasives_Native.None in
                     let is_reveal_or_hide t =
                       let uu___5 = FStarC_Syntax_Util.head_and_args t in
                       match uu___5 with
                       | (h, args) ->
                           let uu___6 =
                             FStarC_Syntax_Util.is_fvar
                               FStarC_Parser_Const.reveal h in
                           if uu___6
                           then
                             let uu___7 = payload_of_hide_reveal h args in
                             (match uu___7 with
                              | FStar_Pervasives_Native.None ->
                                  FStar_Pervasives_Native.None
                              | FStar_Pervasives_Native.Some t3 ->
                                  FStar_Pervasives_Native.Some (Reveal t3))
                           else
                             (let uu___8 =
                                FStarC_Syntax_Util.is_fvar
                                  FStarC_Parser_Const.hide h in
                              if uu___8
                              then
                                let uu___9 = payload_of_hide_reveal h args in
                                match uu___9 with
                                | FStar_Pervasives_Native.None ->
                                    FStar_Pervasives_Native.None
                                | FStar_Pervasives_Native.Some t3 ->
                                    FStar_Pervasives_Native.Some (Hide t3)
                              else FStar_Pervasives_Native.None) in
                     let mk_fv_app lid u args r =
                       let fv =
                         FStarC_TypeChecker_Env.fvar_of_nonqual_lid wl1.tcenv
                           lid in
                       let head = FStarC_Syntax_Syntax.mk_Tm_uinst fv [u] in
                       FStarC_Syntax_Syntax.mk_Tm_app head args r in
                     let uu___5 =
                       let uu___6 = is_reveal_or_hide t11 in
                       let uu___7 = is_reveal_or_hide t21 in (uu___6, uu___7) in
                     match uu___5 with
                     | (FStar_Pervasives_Native.Some (Reveal (u, ty, lhs)),
                        FStar_Pervasives_Native.None) when is_flex lhs ->
                         let rhs =
                           let uu___6 =
                             let uu___7 =
                               let uu___8 =
                                 FStarC_Syntax_Syntax.as_aqual_implicit true in
                               (ty, uu___8) in
                             [uu___7; (t21, FStar_Pervasives_Native.None)] in
                           mk_fv_app FStarC_Parser_Const.hide u uu___6
                             t21.FStarC_Syntax_Syntax.pos in
                         FStar_Pervasives_Native.Some (lhs, rhs)
                     | (FStar_Pervasives_Native.None,
                        FStar_Pervasives_Native.Some (Reveal (u, ty, rhs)))
                         when is_flex rhs ->
                         let lhs =
                           let uu___6 =
                             let uu___7 =
                               let uu___8 =
                                 FStarC_Syntax_Syntax.as_aqual_implicit true in
                               (ty, uu___8) in
                             [uu___7; (t11, FStar_Pervasives_Native.None)] in
                           mk_fv_app FStarC_Parser_Const.hide u uu___6
                             t11.FStarC_Syntax_Syntax.pos in
                         FStar_Pervasives_Native.Some (lhs, rhs)
                     | (FStar_Pervasives_Native.Some (Hide (u, ty, lhs)),
                        FStar_Pervasives_Native.None) ->
                         let rhs =
                           let uu___6 =
                             let uu___7 =
                               let uu___8 =
                                 FStarC_Syntax_Syntax.as_aqual_implicit true in
                               (ty, uu___8) in
                             [uu___7; (t21, FStar_Pervasives_Native.None)] in
                           mk_fv_app FStarC_Parser_Const.reveal u uu___6
                             t21.FStarC_Syntax_Syntax.pos in
                         FStar_Pervasives_Native.Some (lhs, rhs)
                     | (FStar_Pervasives_Native.None,
                        FStar_Pervasives_Native.Some (Hide (u, ty, rhs))) ->
                         let lhs =
                           let uu___6 =
                             let uu___7 =
                               let uu___8 =
                                 FStarC_Syntax_Syntax.as_aqual_implicit true in
                               (ty, uu___8) in
                             [uu___7; (t11, FStar_Pervasives_Native.None)] in
                           mk_fv_app FStarC_Parser_Const.reveal u uu___6
                             t11.FStarC_Syntax_Syntax.pos in
                         FStar_Pervasives_Native.Some (lhs, rhs)
                     | uu___6 -> FStar_Pervasives_Native.None in
                   let uu___5 = try_match_heuristic orig wl1 t1 t2 o in
                   (match uu___5 with
                    | FStar_Pervasives.Inl _defer_ok ->
                        let uu___6 =
                          FStarC_Thunk.mkv "delaying match heuristic" in
                        giveup_or_defer1 orig
                          FStarC_TypeChecker_Common.Deferred_delay_match_heuristic
                          uu___6
                    | FStar_Pervasives.Inr (FStar_Pervasives_Native.Some wl2)
                        -> solve wl2
                    | FStar_Pervasives.Inr (FStar_Pervasives_Native.None) ->
                        let uu___6 = try_reveal_hide t1 t2 in
                        (match uu___6 with
                         | FStar_Pervasives_Native.Some (t1', t2') ->
                             solve_t
                               {
                                 FStarC_TypeChecker_Common.pid =
                                   (problem.FStarC_TypeChecker_Common.pid);
                                 FStarC_TypeChecker_Common.lhs = t1';
                                 FStarC_TypeChecker_Common.relation =
                                   (problem.FStarC_TypeChecker_Common.relation);
                                 FStarC_TypeChecker_Common.rhs = t2';
                                 FStarC_TypeChecker_Common.element =
                                   (problem.FStarC_TypeChecker_Common.element);
                                 FStarC_TypeChecker_Common.logical_guard =
                                   (problem.FStarC_TypeChecker_Common.logical_guard);
                                 FStarC_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (problem.FStarC_TypeChecker_Common.logical_guard_uvar);
                                 FStarC_TypeChecker_Common.reason =
                                   (problem.FStarC_TypeChecker_Common.reason);
                                 FStarC_TypeChecker_Common.loc =
                                   (problem.FStarC_TypeChecker_Common.loc);
                                 FStarC_TypeChecker_Common.rank =
                                   (problem.FStarC_TypeChecker_Common.rank);
                                 FStarC_TypeChecker_Common.logical =
                                   (problem.FStarC_TypeChecker_Common.logical)
                               } wl1
                         | FStar_Pervasives_Native.None ->
                             let uu___7 =
                               ((may_relate wl1.tcenv
                                   problem.FStarC_TypeChecker_Common.relation
                                   head1)
                                  ||
                                  (may_relate wl1.tcenv
                                     problem.FStarC_TypeChecker_Common.relation
                                     head2))
                                 && wl1.smt_ok in
                             if uu___7
                             then
                               let uu___8 = guard_of_prob wl1 problem t1 t2 in
                               (match uu___8 with
                                | (guard, wl2) ->
                                    let uu___9 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl2 in
                                    solve uu___9)
                             else
                               (let uu___9 =
                                  mklstr
                                    (fun uu___10 ->
                                       let uu___11 =
                                         FStarC_Class_Show.show
                                           FStarC_Syntax_Print.showable_term
                                           head1 in
                                       let uu___12 =
                                         let uu___13 =
                                           FStarC_TypeChecker_Env.delta_depth_of_term
                                             wl1.tcenv head1 in
                                         FStarC_Class_Show.show
                                           FStarC_Syntax_Syntax.showable_delta_depth
                                           uu___13 in
                                       let uu___13 =
                                         FStarC_Class_Show.show
                                           FStarC_Syntax_Print.showable_term
                                           head2 in
                                       let uu___14 =
                                         let uu___15 =
                                           FStarC_TypeChecker_Env.delta_depth_of_term
                                             wl1.tcenv head2 in
                                         FStarC_Class_Show.show
                                           FStarC_Syntax_Syntax.showable_delta_depth
                                           uu___15 in
                                       FStarC_Compiler_Util.format4
                                         "head mismatch (%s (%s) vs %s (%s))"
                                         uu___11 uu___12 uu___13 uu___14) in
                                giveup wl1 uu___9 orig)))
               | (HeadMatch (true), uu___3) when
                   problem.FStarC_TypeChecker_Common.relation <>
                     FStarC_TypeChecker_Common.EQ
                   ->
                   if wl1.smt_ok
                   then
                     let uu___4 = guard_of_prob wl1 problem t1 t2 in
                     (match uu___4 with
                      | (guard, wl2) ->
                          let uu___5 =
                            solve_prob orig
                              (FStar_Pervasives_Native.Some guard) [] wl2 in
                          solve uu___5)
                   else
                     (let uu___5 =
                        mklstr
                          (fun uu___6 ->
                             let uu___7 =
                               FStarC_Class_Show.show
                                 FStarC_Syntax_Print.showable_term t1 in
                             let uu___8 =
                               FStarC_Class_Show.show
                                 FStarC_Syntax_Print.showable_term t2 in
                             FStarC_Compiler_Util.format2
                               "head mismatch for subtyping (%s vs %s)"
                               uu___7 uu___8) in
                      giveup wl1 uu___5 orig)
               | (uu___3, FStar_Pervasives_Native.Some (t11, t21)) ->
                   solve_t
                     {
                       FStarC_TypeChecker_Common.pid =
                         (problem.FStarC_TypeChecker_Common.pid);
                       FStarC_TypeChecker_Common.lhs = t11;
                       FStarC_TypeChecker_Common.relation =
                         (problem.FStarC_TypeChecker_Common.relation);
                       FStarC_TypeChecker_Common.rhs = t21;
                       FStarC_TypeChecker_Common.element =
                         (problem.FStarC_TypeChecker_Common.element);
                       FStarC_TypeChecker_Common.logical_guard =
                         (problem.FStarC_TypeChecker_Common.logical_guard);
                       FStarC_TypeChecker_Common.logical_guard_uvar =
                         (problem.FStarC_TypeChecker_Common.logical_guard_uvar);
                       FStarC_TypeChecker_Common.reason =
                         (problem.FStarC_TypeChecker_Common.reason);
                       FStarC_TypeChecker_Common.loc =
                         (problem.FStarC_TypeChecker_Common.loc);
                       FStarC_TypeChecker_Common.rank =
                         (problem.FStarC_TypeChecker_Common.rank);
                       FStarC_TypeChecker_Common.logical =
                         (problem.FStarC_TypeChecker_Common.logical)
                     } wl1
               | (HeadMatch need_unif, FStar_Pervasives_Native.None) ->
                   rigid_heads_match need_unif torig wl1 t1 t2
               | (FullMatch, FStar_Pervasives_Native.None) ->
                   rigid_heads_match false torig wl1 t1 t2)) in
       let orig = FStarC_TypeChecker_Common.TProb problem in
       def_check_prob "solve_t'.2" orig;
       (let uu___2 =
          FStarC_Compiler_Util.physical_equality
            problem.FStarC_TypeChecker_Common.lhs
            problem.FStarC_TypeChecker_Common.rhs in
        if uu___2
        then
          let uu___3 = solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve uu___3
        else
          (let t1 = problem.FStarC_TypeChecker_Common.lhs in
           let t2 = problem.FStarC_TypeChecker_Common.rhs in
           (let uu___5 =
              let uu___6 = p_scope orig in
              FStarC_Compiler_List.map
                (fun b -> b.FStarC_Syntax_Syntax.binder_bv) uu___6 in
            FStarC_Defensive.def_check_scoped
              FStarC_Class_Binders.hasBinders_list_bv
              FStarC_Class_Binders.hasNames_term
              FStarC_Syntax_Print.pretty_term (p_loc orig) "ref.t1" uu___5 t1);
           (let uu___6 =
              let uu___7 = p_scope orig in
              FStarC_Compiler_List.map
                (fun b -> b.FStarC_Syntax_Syntax.binder_bv) uu___7 in
            FStarC_Defensive.def_check_scoped
              FStarC_Class_Binders.hasBinders_list_bv
              FStarC_Class_Binders.hasNames_term
              FStarC_Syntax_Print.pretty_term (p_loc orig) "ref.t2" uu___6 t2);
           (let uu___7 = FStarC_Compiler_Effect.op_Bang dbg_Rel in
            if uu___7
            then
              let uu___8 =
                FStarC_Compiler_Util.string_of_int
                  problem.FStarC_TypeChecker_Common.pid in
              let uu___9 =
                let uu___10 =
                  FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term
                    t1 in
                let uu___11 =
                  let uu___12 =
                    FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                      t1 in
                  Prims.strcat "::" uu___12 in
                Prims.strcat uu___10 uu___11 in
              let uu___10 =
                let uu___11 =
                  FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term
                    t2 in
                let uu___12 =
                  let uu___13 =
                    FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                      t2 in
                  Prims.strcat "::" uu___13 in
                Prims.strcat uu___11 uu___12 in
              let uu___11 =
                FStarC_Class_Show.show FStarC_Class_Show.showable_nat
                  (FStarC_Compiler_List.length wl.attempting) in
              FStarC_Compiler_Util.print5
                "Attempting %s (%s vs %s); rel = (%s); number of problems in wl = %s\n"
                uu___8 uu___9 uu___10
                (rel_to_string problem.FStarC_TypeChecker_Common.relation)
                uu___11
            else ());
           (match ((t1.FStarC_Syntax_Syntax.n), (t2.FStarC_Syntax_Syntax.n))
            with
            | (FStarC_Syntax_Syntax.Tm_delayed uu___7, uu___8) ->
                failwith "Impossible: terms were not compressed"
            | (uu___7, FStarC_Syntax_Syntax.Tm_delayed uu___8) ->
                failwith "Impossible: terms were not compressed"
            | (FStarC_Syntax_Syntax.Tm_ascribed uu___7, uu___8) ->
                let uu___9 =
                  let uu___10 = FStarC_Syntax_Util.unascribe t1 in
                  {
                    FStarC_TypeChecker_Common.pid =
                      (problem.FStarC_TypeChecker_Common.pid);
                    FStarC_TypeChecker_Common.lhs = uu___10;
                    FStarC_TypeChecker_Common.relation =
                      (problem.FStarC_TypeChecker_Common.relation);
                    FStarC_TypeChecker_Common.rhs =
                      (problem.FStarC_TypeChecker_Common.rhs);
                    FStarC_TypeChecker_Common.element =
                      (problem.FStarC_TypeChecker_Common.element);
                    FStarC_TypeChecker_Common.logical_guard =
                      (problem.FStarC_TypeChecker_Common.logical_guard);
                    FStarC_TypeChecker_Common.logical_guard_uvar =
                      (problem.FStarC_TypeChecker_Common.logical_guard_uvar);
                    FStarC_TypeChecker_Common.reason =
                      (problem.FStarC_TypeChecker_Common.reason);
                    FStarC_TypeChecker_Common.loc =
                      (problem.FStarC_TypeChecker_Common.loc);
                    FStarC_TypeChecker_Common.rank =
                      (problem.FStarC_TypeChecker_Common.rank);
                    FStarC_TypeChecker_Common.logical =
                      (problem.FStarC_TypeChecker_Common.logical)
                  } in
                solve_t' uu___9 wl
            | (FStarC_Syntax_Syntax.Tm_meta uu___7, uu___8) ->
                let uu___9 =
                  let uu___10 = FStarC_Syntax_Util.unmeta t1 in
                  {
                    FStarC_TypeChecker_Common.pid =
                      (problem.FStarC_TypeChecker_Common.pid);
                    FStarC_TypeChecker_Common.lhs = uu___10;
                    FStarC_TypeChecker_Common.relation =
                      (problem.FStarC_TypeChecker_Common.relation);
                    FStarC_TypeChecker_Common.rhs =
                      (problem.FStarC_TypeChecker_Common.rhs);
                    FStarC_TypeChecker_Common.element =
                      (problem.FStarC_TypeChecker_Common.element);
                    FStarC_TypeChecker_Common.logical_guard =
                      (problem.FStarC_TypeChecker_Common.logical_guard);
                    FStarC_TypeChecker_Common.logical_guard_uvar =
                      (problem.FStarC_TypeChecker_Common.logical_guard_uvar);
                    FStarC_TypeChecker_Common.reason =
                      (problem.FStarC_TypeChecker_Common.reason);
                    FStarC_TypeChecker_Common.loc =
                      (problem.FStarC_TypeChecker_Common.loc);
                    FStarC_TypeChecker_Common.rank =
                      (problem.FStarC_TypeChecker_Common.rank);
                    FStarC_TypeChecker_Common.logical =
                      (problem.FStarC_TypeChecker_Common.logical)
                  } in
                solve_t' uu___9 wl
            | (uu___7, FStarC_Syntax_Syntax.Tm_ascribed uu___8) ->
                let uu___9 =
                  let uu___10 = FStarC_Syntax_Util.unascribe t2 in
                  {
                    FStarC_TypeChecker_Common.pid =
                      (problem.FStarC_TypeChecker_Common.pid);
                    FStarC_TypeChecker_Common.lhs =
                      (problem.FStarC_TypeChecker_Common.lhs);
                    FStarC_TypeChecker_Common.relation =
                      (problem.FStarC_TypeChecker_Common.relation);
                    FStarC_TypeChecker_Common.rhs = uu___10;
                    FStarC_TypeChecker_Common.element =
                      (problem.FStarC_TypeChecker_Common.element);
                    FStarC_TypeChecker_Common.logical_guard =
                      (problem.FStarC_TypeChecker_Common.logical_guard);
                    FStarC_TypeChecker_Common.logical_guard_uvar =
                      (problem.FStarC_TypeChecker_Common.logical_guard_uvar);
                    FStarC_TypeChecker_Common.reason =
                      (problem.FStarC_TypeChecker_Common.reason);
                    FStarC_TypeChecker_Common.loc =
                      (problem.FStarC_TypeChecker_Common.loc);
                    FStarC_TypeChecker_Common.rank =
                      (problem.FStarC_TypeChecker_Common.rank);
                    FStarC_TypeChecker_Common.logical =
                      (problem.FStarC_TypeChecker_Common.logical)
                  } in
                solve_t' uu___9 wl
            | (uu___7, FStarC_Syntax_Syntax.Tm_meta uu___8) ->
                let uu___9 =
                  let uu___10 = FStarC_Syntax_Util.unmeta t2 in
                  {
                    FStarC_TypeChecker_Common.pid =
                      (problem.FStarC_TypeChecker_Common.pid);
                    FStarC_TypeChecker_Common.lhs =
                      (problem.FStarC_TypeChecker_Common.lhs);
                    FStarC_TypeChecker_Common.relation =
                      (problem.FStarC_TypeChecker_Common.relation);
                    FStarC_TypeChecker_Common.rhs = uu___10;
                    FStarC_TypeChecker_Common.element =
                      (problem.FStarC_TypeChecker_Common.element);
                    FStarC_TypeChecker_Common.logical_guard =
                      (problem.FStarC_TypeChecker_Common.logical_guard);
                    FStarC_TypeChecker_Common.logical_guard_uvar =
                      (problem.FStarC_TypeChecker_Common.logical_guard_uvar);
                    FStarC_TypeChecker_Common.reason =
                      (problem.FStarC_TypeChecker_Common.reason);
                    FStarC_TypeChecker_Common.loc =
                      (problem.FStarC_TypeChecker_Common.loc);
                    FStarC_TypeChecker_Common.rank =
                      (problem.FStarC_TypeChecker_Common.rank);
                    FStarC_TypeChecker_Common.logical =
                      (problem.FStarC_TypeChecker_Common.logical)
                  } in
                solve_t' uu___9 wl
            | (FStarC_Syntax_Syntax.Tm_quoted (t11, uu___7),
               FStarC_Syntax_Syntax.Tm_quoted (t21, uu___8)) ->
                let uu___9 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl in
                solve uu___9
            | (FStarC_Syntax_Syntax.Tm_bvar uu___7, uu___8) ->
                failwith
                  "Only locally nameless! We should never see a de Bruijn variable"
            | (uu___7, FStarC_Syntax_Syntax.Tm_bvar uu___8) ->
                failwith
                  "Only locally nameless! We should never see a de Bruijn variable"
            | (FStarC_Syntax_Syntax.Tm_type u1, FStarC_Syntax_Syntax.Tm_type
               u2) -> solve_one_universe_eq orig u1 u2 wl
            | (FStarC_Syntax_Syntax.Tm_arrow
               { FStarC_Syntax_Syntax.bs1 = bs1;
                 FStarC_Syntax_Syntax.comp = c1;_},
               FStarC_Syntax_Syntax.Tm_arrow
               { FStarC_Syntax_Syntax.bs1 = bs2;
                 FStarC_Syntax_Syntax.comp = c2;_})
                ->
                let mk_c c uu___7 =
                  match uu___7 with
                  | [] -> c
                  | bs ->
                      let uu___8 =
                        FStarC_Syntax_Syntax.mk
                          (FStarC_Syntax_Syntax.Tm_arrow
                             {
                               FStarC_Syntax_Syntax.bs1 = bs;
                               FStarC_Syntax_Syntax.comp = c
                             }) c.FStarC_Syntax_Syntax.pos in
                      FStarC_Syntax_Syntax.mk_Total uu___8 in
                let uu___7 =
                  match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                (match uu___7 with
                 | ((bs11, c11), (bs21, c21)) ->
                     solve_binders bs11 bs21 orig wl
                       (fun wl1 ->
                          fun scope ->
                            fun subst ->
                              let c12 =
                                FStarC_Syntax_Subst.subst_comp subst c11 in
                              let c22 =
                                FStarC_Syntax_Subst.subst_comp subst c21 in
                              let rel =
                                let uu___8 =
                                  FStarC_Options.use_eq_at_higher_order () in
                                if uu___8
                                then FStarC_TypeChecker_Common.EQ
                                else
                                  problem.FStarC_TypeChecker_Common.relation in
                              mk_c_problem wl1 scope orig c12 rel c22
                                FStar_Pervasives_Native.None
                                "function co-domain"))
            | (FStarC_Syntax_Syntax.Tm_abs
               { FStarC_Syntax_Syntax.bs = bs1;
                 FStarC_Syntax_Syntax.body = tbody1;
                 FStarC_Syntax_Syntax.rc_opt = lopt1;_},
               FStarC_Syntax_Syntax.Tm_abs
               { FStarC_Syntax_Syntax.bs = bs2;
                 FStarC_Syntax_Syntax.body = tbody2;
                 FStarC_Syntax_Syntax.rc_opt = lopt2;_})
                ->
                let mk_t t l uu___7 =
                  match uu___7 with
                  | [] -> t
                  | bs ->
                      FStarC_Syntax_Syntax.mk
                        (FStarC_Syntax_Syntax.Tm_abs
                           {
                             FStarC_Syntax_Syntax.bs = bs;
                             FStarC_Syntax_Syntax.body = t;
                             FStarC_Syntax_Syntax.rc_opt = l
                           }) t.FStarC_Syntax_Syntax.pos in
                let uu___7 =
                  match_num_binders (bs1, (mk_t tbody1 lopt1))
                    (bs2, (mk_t tbody2 lopt2)) in
                (match uu___7 with
                 | ((bs11, tbody11), (bs21, tbody21)) ->
                     solve_binders bs11 bs21 orig wl
                       (fun wl1 ->
                          fun scope ->
                            fun subst ->
                              let uu___8 =
                                FStarC_Syntax_Subst.subst subst tbody11 in
                              let uu___9 =
                                FStarC_Syntax_Subst.subst subst tbody21 in
                              mk_t_problem wl1 scope orig uu___8
                                problem.FStarC_TypeChecker_Common.relation
                                uu___9 FStar_Pervasives_Native.None
                                "lambda co-domain"))
            | (FStarC_Syntax_Syntax.Tm_refine
               { FStarC_Syntax_Syntax.b = x1;
                 FStarC_Syntax_Syntax.phi = phi1;_},
               FStarC_Syntax_Syntax.Tm_refine
               { FStarC_Syntax_Syntax.b = x2;
                 FStarC_Syntax_Syntax.phi = phi2;_})
                ->
                let env = p_env wl (FStarC_TypeChecker_Common.TProb problem) in
                let uu___7 =
                  let uu___8 =
                    head_matches_delta env false wl.smt_ok
                      x1.FStarC_Syntax_Syntax.sort
                      x2.FStarC_Syntax_Syntax.sort in
                  match uu___8 with
                  | (FullMatch, FStar_Pervasives_Native.Some (t11, t21)) ->
                      ({
                         FStarC_Syntax_Syntax.ppname =
                           (x1.FStarC_Syntax_Syntax.ppname);
                         FStarC_Syntax_Syntax.index =
                           (x1.FStarC_Syntax_Syntax.index);
                         FStarC_Syntax_Syntax.sort = t11
                       },
                        {
                          FStarC_Syntax_Syntax.ppname =
                            (x2.FStarC_Syntax_Syntax.ppname);
                          FStarC_Syntax_Syntax.index =
                            (x2.FStarC_Syntax_Syntax.index);
                          FStarC_Syntax_Syntax.sort = t21
                        })
                  | (HeadMatch uu___9, FStar_Pervasives_Native.Some
                     (t11, t21)) ->
                      ({
                         FStarC_Syntax_Syntax.ppname =
                           (x1.FStarC_Syntax_Syntax.ppname);
                         FStarC_Syntax_Syntax.index =
                           (x1.FStarC_Syntax_Syntax.index);
                         FStarC_Syntax_Syntax.sort = t11
                       },
                        {
                          FStarC_Syntax_Syntax.ppname =
                            (x2.FStarC_Syntax_Syntax.ppname);
                          FStarC_Syntax_Syntax.index =
                            (x2.FStarC_Syntax_Syntax.index);
                          FStarC_Syntax_Syntax.sort = t21
                        })
                  | uu___9 -> (x1, x2) in
                (match uu___7 with
                 | (x11, x21) ->
                     let t11 =
                       FStarC_Syntax_Syntax.mk
                         (FStarC_Syntax_Syntax.Tm_refine
                            {
                              FStarC_Syntax_Syntax.b = x11;
                              FStarC_Syntax_Syntax.phi = phi1
                            }) t1.FStarC_Syntax_Syntax.pos in
                     let t21 =
                       FStarC_Syntax_Syntax.mk
                         (FStarC_Syntax_Syntax.Tm_refine
                            {
                              FStarC_Syntax_Syntax.b = x21;
                              FStarC_Syntax_Syntax.phi = phi2
                            }) t2.FStarC_Syntax_Syntax.pos in
                     let uu___8 = as_refinement false env t11 in
                     (match uu___8 with
                      | (x12, phi11) ->
                          let uu___9 = as_refinement false env t21 in
                          (match uu___9 with
                           | (x22, phi21) ->
                               ((let uu___11 =
                                   FStarC_Compiler_Effect.op_Bang dbg_Rel in
                                 if uu___11
                                 then
                                   ((let uu___13 =
                                       FStarC_Class_Show.show
                                         FStarC_Syntax_Print.showable_bv x12 in
                                     let uu___14 =
                                       FStarC_Class_Show.show
                                         FStarC_Syntax_Print.showable_term
                                         x12.FStarC_Syntax_Syntax.sort in
                                     let uu___15 =
                                       FStarC_Class_Show.show
                                         FStarC_Syntax_Print.showable_term
                                         phi11 in
                                     FStarC_Compiler_Util.print3
                                       "ref1 = (%s):(%s){%s}\n" uu___13
                                       uu___14 uu___15);
                                    (let uu___13 =
                                       FStarC_Class_Show.show
                                         FStarC_Syntax_Print.showable_bv x22 in
                                     let uu___14 =
                                       FStarC_Class_Show.show
                                         FStarC_Syntax_Print.showable_term
                                         x22.FStarC_Syntax_Syntax.sort in
                                     let uu___15 =
                                       FStarC_Class_Show.show
                                         FStarC_Syntax_Print.showable_term
                                         phi21 in
                                     FStarC_Compiler_Util.print3
                                       "ref2 = (%s):(%s){%s}\n" uu___13
                                       uu___14 uu___15))
                                 else ());
                                (let uu___11 =
                                   mk_t_problem wl [] orig
                                     x12.FStarC_Syntax_Syntax.sort
                                     problem.FStarC_TypeChecker_Common.relation
                                     x22.FStarC_Syntax_Syntax.sort
                                     problem.FStarC_TypeChecker_Common.element
                                     "refinement base type" in
                                 match uu___11 with
                                 | (base_prob, wl1) ->
                                     let x13 =
                                       FStarC_Syntax_Syntax.freshen_bv x12 in
                                     let subst =
                                       [FStarC_Syntax_Syntax.DB
                                          (Prims.int_zero, x13)] in
                                     let phi12 =
                                       FStarC_Syntax_Subst.subst subst phi11 in
                                     let phi22 =
                                       FStarC_Syntax_Subst.subst subst phi21 in
                                     let mk_imp imp phi13 phi23 =
                                       let uu___12 = imp phi13 phi23 in
                                       guard_on_element wl1 problem x13
                                         uu___12 in
                                     let fallback uu___12 =
                                       let impl =
                                         if
                                           problem.FStarC_TypeChecker_Common.relation
                                             = FStarC_TypeChecker_Common.EQ
                                         then
                                           mk_imp FStarC_Syntax_Util.mk_iff
                                             phi12 phi22
                                         else
                                           mk_imp FStarC_Syntax_Util.mk_imp
                                             phi12 phi22 in
                                       let guard =
                                         FStarC_Syntax_Util.mk_conj
                                           (p_guard base_prob) impl in
                                       (let uu___14 =
                                          let uu___15 = p_scope orig in
                                          FStarC_Compiler_List.map
                                            (fun b ->
                                               b.FStarC_Syntax_Syntax.binder_bv)
                                            uu___15 in
                                        FStarC_Defensive.def_check_scoped
                                          FStarC_Class_Binders.hasBinders_list_bv
                                          FStarC_Class_Binders.hasNames_term
                                          FStarC_Syntax_Print.pretty_term
                                          (p_loc orig) "ref.1" uu___14
                                          (p_guard base_prob));
                                       (let uu___15 =
                                          let uu___16 = p_scope orig in
                                          FStarC_Compiler_List.map
                                            (fun b ->
                                               b.FStarC_Syntax_Syntax.binder_bv)
                                            uu___16 in
                                        FStarC_Defensive.def_check_scoped
                                          FStarC_Class_Binders.hasBinders_list_bv
                                          FStarC_Class_Binders.hasNames_term
                                          FStarC_Syntax_Print.pretty_term
                                          (p_loc orig) "ref.2" uu___15 impl);
                                       (let wl2 =
                                          solve_prob orig
                                            (FStar_Pervasives_Native.Some
                                               guard) [] wl1 in
                                        let uu___15 = attempt [base_prob] wl2 in
                                        solve uu___15) in
                                     let has_uvars =
                                       (let uu___12 =
                                          let uu___13 =
                                            FStarC_Syntax_Free.uvars phi12 in
                                          FStarC_Class_Setlike.is_empty ()
                                            (Obj.magic
                                               (FStarC_Compiler_FlatSet.setlike_flat_set
                                                  FStarC_Syntax_Free.ord_ctx_uvar))
                                            (Obj.magic uu___13) in
                                        Prims.op_Negation uu___12) ||
                                         (let uu___12 =
                                            let uu___13 =
                                              FStarC_Syntax_Free.uvars phi22 in
                                            FStarC_Class_Setlike.is_empty ()
                                              (Obj.magic
                                                 (FStarC_Compiler_FlatSet.setlike_flat_set
                                                    FStarC_Syntax_Free.ord_ctx_uvar))
                                              (Obj.magic uu___13) in
                                          Prims.op_Negation uu___12) in
                                     if
                                       (problem.FStarC_TypeChecker_Common.relation
                                          = FStarC_TypeChecker_Common.EQ)
                                         ||
                                         ((Prims.op_Negation
                                             env.FStarC_TypeChecker_Env.uvar_subtyping)
                                            && has_uvars)
                                     then
                                       let uu___12 =
                                         let uu___13 =
                                           let uu___14 =
                                             FStarC_Syntax_Syntax.mk_binder
                                               x13 in
                                           [uu___14] in
                                         mk_t_problem wl1 uu___13 orig phi12
                                           FStarC_TypeChecker_Common.EQ phi22
                                           FStar_Pervasives_Native.None
                                           "refinement formula" in
                                       (match uu___12 with
                                        | (ref_prob, wl2) ->
                                            let ref_prob1 =
                                              set_logical true ref_prob in
                                            let tx =
                                              FStarC_Syntax_Unionfind.new_transaction
                                                () in
                                            let uu___13 =
                                              solve
                                                {
                                                  attempting = [ref_prob1];
                                                  wl_deferred =
                                                    (Obj.magic
                                                       (FStarC_Class_Listlike.empty
                                                          ()
                                                          (Obj.magic
                                                             (FStarC_Compiler_CList.listlike_clist
                                                                ()))));
                                                  wl_deferred_to_tac =
                                                    (wl2.wl_deferred_to_tac);
                                                  ctr = (wl2.ctr);
                                                  defer_ok = NoDefer;
                                                  smt_ok = (wl2.smt_ok);
                                                  umax_heuristic_ok =
                                                    (wl2.umax_heuristic_ok);
                                                  tcenv = (wl2.tcenv);
                                                  wl_implicits =
                                                    (Obj.magic
                                                       (FStarC_Class_Listlike.empty
                                                          ()
                                                          (Obj.magic
                                                             (FStarC_Compiler_CList.listlike_clist
                                                                ()))));
                                                  repr_subcomp_allowed =
                                                    (wl2.repr_subcomp_allowed);
                                                  typeclass_variables =
                                                    (wl2.typeclass_variables)
                                                } in
                                            (match uu___13 with
                                             | Failed (prob, msg) ->
                                                 (FStarC_Syntax_Unionfind.rollback
                                                    tx;
                                                  if
                                                    (((Prims.op_Negation
                                                         env.FStarC_TypeChecker_Env.uvar_subtyping)
                                                        && has_uvars)
                                                       ||
                                                       (Prims.op_Negation
                                                          wl2.smt_ok))
                                                      &&
                                                      (Prims.op_Negation
                                                         env.FStarC_TypeChecker_Env.unif_allow_ref_guards)
                                                  then giveup wl2 msg prob
                                                  else fallback ())
                                             | Success
                                                 (uu___14, defer_to_tac,
                                                  imps)
                                                 ->
                                                 (FStarC_Syntax_Unionfind.commit
                                                    tx;
                                                  (let guard =
                                                     let uu___16 =
                                                       guard_on_element wl2
                                                         problem x13
                                                         (p_guard ref_prob1) in
                                                     FStarC_Syntax_Util.mk_conj
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
                                                       smt_ok = (wl3.smt_ok);
                                                       umax_heuristic_ok =
                                                         (wl3.umax_heuristic_ok);
                                                       tcenv = (wl3.tcenv);
                                                       wl_implicits =
                                                         (wl3.wl_implicits);
                                                       repr_subcomp_allowed =
                                                         (wl3.repr_subcomp_allowed);
                                                       typeclass_variables =
                                                         (wl3.typeclass_variables)
                                                     } in
                                                   let wl5 =
                                                     extend_wl wl4
                                                       (Obj.magic
                                                          (FStarC_Class_Listlike.empty
                                                             ()
                                                             (Obj.magic
                                                                (FStarC_Compiler_CList.listlike_clist
                                                                   ()))))
                                                       defer_to_tac imps in
                                                   let uu___16 =
                                                     attempt [base_prob] wl5 in
                                                   solve uu___16))))
                                     else fallback ())))))
            | (FStarC_Syntax_Syntax.Tm_uvar uu___7,
               FStarC_Syntax_Syntax.Tm_uvar uu___8) ->
                let env = p_env wl (FStarC_TypeChecker_Common.TProb problem) in
                let uu___9 = ensure_no_uvar_subst env t1 wl in
                (match uu___9 with
                 | (t11, wl1) ->
                     let t21 = FStarC_Syntax_Util.canon_app t2 in
                     let uu___10 = ensure_no_uvar_subst env t21 wl1 in
                     (match uu___10 with
                      | (t22, wl2) ->
                          let f1 = destruct_flex_t' t11 in
                          let f2 = destruct_flex_t' t22 in
                          solve_t_flex_flex env orig wl2 f1 f2))
            | (FStarC_Syntax_Syntax.Tm_app
               {
                 FStarC_Syntax_Syntax.hd =
                   {
                     FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_uvar
                       uu___7;
                     FStarC_Syntax_Syntax.pos = uu___8;
                     FStarC_Syntax_Syntax.vars = uu___9;
                     FStarC_Syntax_Syntax.hash_code = uu___10;_};
                 FStarC_Syntax_Syntax.args = uu___11;_},
               FStarC_Syntax_Syntax.Tm_uvar uu___12) ->
                let env = p_env wl (FStarC_TypeChecker_Common.TProb problem) in
                let uu___13 = ensure_no_uvar_subst env t1 wl in
                (match uu___13 with
                 | (t11, wl1) ->
                     let t21 = FStarC_Syntax_Util.canon_app t2 in
                     let uu___14 = ensure_no_uvar_subst env t21 wl1 in
                     (match uu___14 with
                      | (t22, wl2) ->
                          let f1 = destruct_flex_t' t11 in
                          let f2 = destruct_flex_t' t22 in
                          solve_t_flex_flex env orig wl2 f1 f2))
            | (FStarC_Syntax_Syntax.Tm_uvar uu___7,
               FStarC_Syntax_Syntax.Tm_app
               {
                 FStarC_Syntax_Syntax.hd =
                   {
                     FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_uvar
                       uu___8;
                     FStarC_Syntax_Syntax.pos = uu___9;
                     FStarC_Syntax_Syntax.vars = uu___10;
                     FStarC_Syntax_Syntax.hash_code = uu___11;_};
                 FStarC_Syntax_Syntax.args = uu___12;_})
                ->
                let env = p_env wl (FStarC_TypeChecker_Common.TProb problem) in
                let uu___13 = ensure_no_uvar_subst env t1 wl in
                (match uu___13 with
                 | (t11, wl1) ->
                     let t21 = FStarC_Syntax_Util.canon_app t2 in
                     let uu___14 = ensure_no_uvar_subst env t21 wl1 in
                     (match uu___14 with
                      | (t22, wl2) ->
                          let f1 = destruct_flex_t' t11 in
                          let f2 = destruct_flex_t' t22 in
                          solve_t_flex_flex env orig wl2 f1 f2))
            | (FStarC_Syntax_Syntax.Tm_app
               {
                 FStarC_Syntax_Syntax.hd =
                   {
                     FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_uvar
                       uu___7;
                     FStarC_Syntax_Syntax.pos = uu___8;
                     FStarC_Syntax_Syntax.vars = uu___9;
                     FStarC_Syntax_Syntax.hash_code = uu___10;_};
                 FStarC_Syntax_Syntax.args = uu___11;_},
               FStarC_Syntax_Syntax.Tm_app
               {
                 FStarC_Syntax_Syntax.hd =
                   {
                     FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_uvar
                       uu___12;
                     FStarC_Syntax_Syntax.pos = uu___13;
                     FStarC_Syntax_Syntax.vars = uu___14;
                     FStarC_Syntax_Syntax.hash_code = uu___15;_};
                 FStarC_Syntax_Syntax.args = uu___16;_})
                ->
                let env = p_env wl (FStarC_TypeChecker_Common.TProb problem) in
                let uu___17 = ensure_no_uvar_subst env t1 wl in
                (match uu___17 with
                 | (t11, wl1) ->
                     let t21 = FStarC_Syntax_Util.canon_app t2 in
                     let uu___18 = ensure_no_uvar_subst env t21 wl1 in
                     (match uu___18 with
                      | (t22, wl2) ->
                          let f1 = destruct_flex_t' t11 in
                          let f2 = destruct_flex_t' t22 in
                          solve_t_flex_flex env orig wl2 f1 f2))
            | (FStarC_Syntax_Syntax.Tm_uvar uu___7, uu___8) when
                problem.FStarC_TypeChecker_Common.relation =
                  FStarC_TypeChecker_Common.EQ
                ->
                let uu___9 = destruct_flex_t t1 wl in
                (match uu___9 with
                 | (f1, wl1) -> solve_t_flex_rigid_eq orig wl1 f1 t2)
            | (FStarC_Syntax_Syntax.Tm_app
               {
                 FStarC_Syntax_Syntax.hd =
                   {
                     FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_uvar
                       uu___7;
                     FStarC_Syntax_Syntax.pos = uu___8;
                     FStarC_Syntax_Syntax.vars = uu___9;
                     FStarC_Syntax_Syntax.hash_code = uu___10;_};
                 FStarC_Syntax_Syntax.args = uu___11;_},
               uu___12) when
                problem.FStarC_TypeChecker_Common.relation =
                  FStarC_TypeChecker_Common.EQ
                ->
                let uu___13 = destruct_flex_t t1 wl in
                (match uu___13 with
                 | (f1, wl1) -> solve_t_flex_rigid_eq orig wl1 f1 t2)
            | (uu___7, FStarC_Syntax_Syntax.Tm_uvar uu___8) when
                problem.FStarC_TypeChecker_Common.relation =
                  FStarC_TypeChecker_Common.EQ
                -> solve_t' (invert problem) wl
            | (uu___7, FStarC_Syntax_Syntax.Tm_app
               {
                 FStarC_Syntax_Syntax.hd =
                   {
                     FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_uvar
                       uu___8;
                     FStarC_Syntax_Syntax.pos = uu___9;
                     FStarC_Syntax_Syntax.vars = uu___10;
                     FStarC_Syntax_Syntax.hash_code = uu___11;_};
                 FStarC_Syntax_Syntax.args = uu___12;_})
                when
                problem.FStarC_TypeChecker_Common.relation =
                  FStarC_TypeChecker_Common.EQ
                -> solve_t' (invert problem) wl
            | (FStarC_Syntax_Syntax.Tm_uvar uu___7,
               FStarC_Syntax_Syntax.Tm_arrow uu___8) ->
                solve_t'
                  {
                    FStarC_TypeChecker_Common.pid =
                      (problem.FStarC_TypeChecker_Common.pid);
                    FStarC_TypeChecker_Common.lhs =
                      (problem.FStarC_TypeChecker_Common.lhs);
                    FStarC_TypeChecker_Common.relation =
                      FStarC_TypeChecker_Common.EQ;
                    FStarC_TypeChecker_Common.rhs =
                      (problem.FStarC_TypeChecker_Common.rhs);
                    FStarC_TypeChecker_Common.element =
                      (problem.FStarC_TypeChecker_Common.element);
                    FStarC_TypeChecker_Common.logical_guard =
                      (problem.FStarC_TypeChecker_Common.logical_guard);
                    FStarC_TypeChecker_Common.logical_guard_uvar =
                      (problem.FStarC_TypeChecker_Common.logical_guard_uvar);
                    FStarC_TypeChecker_Common.reason =
                      (problem.FStarC_TypeChecker_Common.reason);
                    FStarC_TypeChecker_Common.loc =
                      (problem.FStarC_TypeChecker_Common.loc);
                    FStarC_TypeChecker_Common.rank =
                      (problem.FStarC_TypeChecker_Common.rank);
                    FStarC_TypeChecker_Common.logical =
                      (problem.FStarC_TypeChecker_Common.logical)
                  } wl
            | (FStarC_Syntax_Syntax.Tm_app
               {
                 FStarC_Syntax_Syntax.hd =
                   {
                     FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_uvar
                       uu___7;
                     FStarC_Syntax_Syntax.pos = uu___8;
                     FStarC_Syntax_Syntax.vars = uu___9;
                     FStarC_Syntax_Syntax.hash_code = uu___10;_};
                 FStarC_Syntax_Syntax.args = uu___11;_},
               FStarC_Syntax_Syntax.Tm_arrow uu___12) ->
                solve_t'
                  {
                    FStarC_TypeChecker_Common.pid =
                      (problem.FStarC_TypeChecker_Common.pid);
                    FStarC_TypeChecker_Common.lhs =
                      (problem.FStarC_TypeChecker_Common.lhs);
                    FStarC_TypeChecker_Common.relation =
                      FStarC_TypeChecker_Common.EQ;
                    FStarC_TypeChecker_Common.rhs =
                      (problem.FStarC_TypeChecker_Common.rhs);
                    FStarC_TypeChecker_Common.element =
                      (problem.FStarC_TypeChecker_Common.element);
                    FStarC_TypeChecker_Common.logical_guard =
                      (problem.FStarC_TypeChecker_Common.logical_guard);
                    FStarC_TypeChecker_Common.logical_guard_uvar =
                      (problem.FStarC_TypeChecker_Common.logical_guard_uvar);
                    FStarC_TypeChecker_Common.reason =
                      (problem.FStarC_TypeChecker_Common.reason);
                    FStarC_TypeChecker_Common.loc =
                      (problem.FStarC_TypeChecker_Common.loc);
                    FStarC_TypeChecker_Common.rank =
                      (problem.FStarC_TypeChecker_Common.rank);
                    FStarC_TypeChecker_Common.logical =
                      (problem.FStarC_TypeChecker_Common.logical)
                  } wl
            | (uu___7, FStarC_Syntax_Syntax.Tm_uvar uu___8) ->
                let uu___9 =
                  attempt [FStarC_TypeChecker_Common.TProb problem] wl in
                solve uu___9
            | (uu___7, FStarC_Syntax_Syntax.Tm_app
               {
                 FStarC_Syntax_Syntax.hd =
                   {
                     FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_uvar
                       uu___8;
                     FStarC_Syntax_Syntax.pos = uu___9;
                     FStarC_Syntax_Syntax.vars = uu___10;
                     FStarC_Syntax_Syntax.hash_code = uu___11;_};
                 FStarC_Syntax_Syntax.args = uu___12;_})
                ->
                let uu___13 =
                  attempt [FStarC_TypeChecker_Common.TProb problem] wl in
                solve uu___13
            | (FStarC_Syntax_Syntax.Tm_uvar uu___7, uu___8) ->
                let uu___9 =
                  attempt [FStarC_TypeChecker_Common.TProb problem] wl in
                solve uu___9
            | (FStarC_Syntax_Syntax.Tm_app
               {
                 FStarC_Syntax_Syntax.hd =
                   {
                     FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_uvar
                       uu___7;
                     FStarC_Syntax_Syntax.pos = uu___8;
                     FStarC_Syntax_Syntax.vars = uu___9;
                     FStarC_Syntax_Syntax.hash_code = uu___10;_};
                 FStarC_Syntax_Syntax.args = uu___11;_},
               uu___12) ->
                let uu___13 =
                  attempt [FStarC_TypeChecker_Common.TProb problem] wl in
                solve uu___13
            | (FStarC_Syntax_Syntax.Tm_abs uu___7, uu___8) ->
                let is_abs t =
                  match t.FStarC_Syntax_Syntax.n with
                  | FStarC_Syntax_Syntax.Tm_abs uu___9 ->
                      FStar_Pervasives.Inl t
                  | uu___9 -> FStar_Pervasives.Inr t in
                let env = p_env wl orig in
                (match ((is_abs t1), (is_abs t2)) with
                 | (FStar_Pervasives.Inl t_abs, FStar_Pervasives.Inr not_abs)
                     ->
                     let uu___9 =
                       (is_flex not_abs) &&
                         ((p_rel orig) = FStarC_TypeChecker_Common.EQ) in
                     if uu___9
                     then
                       let uu___10 = destruct_flex_t not_abs wl in
                       (match uu___10 with
                        | (flex, wl1) ->
                            solve_t_flex_rigid_eq orig wl1 flex t_abs)
                     else
                       (let uu___11 =
                          head_matches_delta env false wl.smt_ok not_abs
                            t_abs in
                        match uu___11 with
                        | (HeadMatch uu___12, FStar_Pervasives_Native.Some
                           (not_abs', uu___13)) ->
                            solve_t
                              {
                                FStarC_TypeChecker_Common.pid =
                                  (problem.FStarC_TypeChecker_Common.pid);
                                FStarC_TypeChecker_Common.lhs = not_abs';
                                FStarC_TypeChecker_Common.relation =
                                  (problem.FStarC_TypeChecker_Common.relation);
                                FStarC_TypeChecker_Common.rhs = t_abs;
                                FStarC_TypeChecker_Common.element =
                                  (problem.FStarC_TypeChecker_Common.element);
                                FStarC_TypeChecker_Common.logical_guard =
                                  (problem.FStarC_TypeChecker_Common.logical_guard);
                                FStarC_TypeChecker_Common.logical_guard_uvar
                                  =
                                  (problem.FStarC_TypeChecker_Common.logical_guard_uvar);
                                FStarC_TypeChecker_Common.reason =
                                  (problem.FStarC_TypeChecker_Common.reason);
                                FStarC_TypeChecker_Common.loc =
                                  (problem.FStarC_TypeChecker_Common.loc);
                                FStarC_TypeChecker_Common.rank =
                                  (problem.FStarC_TypeChecker_Common.rank);
                                FStarC_TypeChecker_Common.logical =
                                  (problem.FStarC_TypeChecker_Common.logical)
                              } wl
                        | uu___12 ->
                            let uu___13 =
                              FStarC_Syntax_Util.head_and_args not_abs in
                            (match uu___13 with
                             | (head, uu___14) ->
                                 let uu___15 =
                                   wl.smt_ok &&
                                     (may_relate wl.tcenv (p_rel orig) head) in
                                 if uu___15
                                 then
                                   let uu___16 = mk_eq2 wl orig t_abs not_abs in
                                   (match uu___16 with
                                    | (g, wl1) ->
                                        let uu___17 =
                                          solve_prob orig
                                            (FStar_Pervasives_Native.Some g)
                                            [] wl1 in
                                        solve uu___17)
                                 else
                                   (let uu___17 =
                                      FStarC_Thunk.mkv
                                        "head tag mismatch: RHS is an abstraction" in
                                    giveup wl uu___17 orig)))
                 | (FStar_Pervasives.Inr not_abs, FStar_Pervasives.Inl t_abs)
                     ->
                     let uu___9 =
                       (is_flex not_abs) &&
                         ((p_rel orig) = FStarC_TypeChecker_Common.EQ) in
                     if uu___9
                     then
                       let uu___10 = destruct_flex_t not_abs wl in
                       (match uu___10 with
                        | (flex, wl1) ->
                            solve_t_flex_rigid_eq orig wl1 flex t_abs)
                     else
                       (let uu___11 =
                          head_matches_delta env false wl.smt_ok not_abs
                            t_abs in
                        match uu___11 with
                        | (HeadMatch uu___12, FStar_Pervasives_Native.Some
                           (not_abs', uu___13)) ->
                            solve_t
                              {
                                FStarC_TypeChecker_Common.pid =
                                  (problem.FStarC_TypeChecker_Common.pid);
                                FStarC_TypeChecker_Common.lhs = not_abs';
                                FStarC_TypeChecker_Common.relation =
                                  (problem.FStarC_TypeChecker_Common.relation);
                                FStarC_TypeChecker_Common.rhs = t_abs;
                                FStarC_TypeChecker_Common.element =
                                  (problem.FStarC_TypeChecker_Common.element);
                                FStarC_TypeChecker_Common.logical_guard =
                                  (problem.FStarC_TypeChecker_Common.logical_guard);
                                FStarC_TypeChecker_Common.logical_guard_uvar
                                  =
                                  (problem.FStarC_TypeChecker_Common.logical_guard_uvar);
                                FStarC_TypeChecker_Common.reason =
                                  (problem.FStarC_TypeChecker_Common.reason);
                                FStarC_TypeChecker_Common.loc =
                                  (problem.FStarC_TypeChecker_Common.loc);
                                FStarC_TypeChecker_Common.rank =
                                  (problem.FStarC_TypeChecker_Common.rank);
                                FStarC_TypeChecker_Common.logical =
                                  (problem.FStarC_TypeChecker_Common.logical)
                              } wl
                        | uu___12 ->
                            let uu___13 =
                              FStarC_Syntax_Util.head_and_args not_abs in
                            (match uu___13 with
                             | (head, uu___14) ->
                                 let uu___15 =
                                   wl.smt_ok &&
                                     (may_relate wl.tcenv (p_rel orig) head) in
                                 if uu___15
                                 then
                                   let uu___16 = mk_eq2 wl orig t_abs not_abs in
                                   (match uu___16 with
                                    | (g, wl1) ->
                                        let uu___17 =
                                          solve_prob orig
                                            (FStar_Pervasives_Native.Some g)
                                            [] wl1 in
                                        solve uu___17)
                                 else
                                   (let uu___17 =
                                      FStarC_Thunk.mkv
                                        "head tag mismatch: RHS is an abstraction" in
                                    giveup wl uu___17 orig)))
                 | uu___9 ->
                     failwith
                       "Impossible: at least one side is an abstraction")
            | (uu___7, FStarC_Syntax_Syntax.Tm_abs uu___8) ->
                let is_abs t =
                  match t.FStarC_Syntax_Syntax.n with
                  | FStarC_Syntax_Syntax.Tm_abs uu___9 ->
                      FStar_Pervasives.Inl t
                  | uu___9 -> FStar_Pervasives.Inr t in
                let env = p_env wl orig in
                (match ((is_abs t1), (is_abs t2)) with
                 | (FStar_Pervasives.Inl t_abs, FStar_Pervasives.Inr not_abs)
                     ->
                     let uu___9 =
                       (is_flex not_abs) &&
                         ((p_rel orig) = FStarC_TypeChecker_Common.EQ) in
                     if uu___9
                     then
                       let uu___10 = destruct_flex_t not_abs wl in
                       (match uu___10 with
                        | (flex, wl1) ->
                            solve_t_flex_rigid_eq orig wl1 flex t_abs)
                     else
                       (let uu___11 =
                          head_matches_delta env false wl.smt_ok not_abs
                            t_abs in
                        match uu___11 with
                        | (HeadMatch uu___12, FStar_Pervasives_Native.Some
                           (not_abs', uu___13)) ->
                            solve_t
                              {
                                FStarC_TypeChecker_Common.pid =
                                  (problem.FStarC_TypeChecker_Common.pid);
                                FStarC_TypeChecker_Common.lhs = not_abs';
                                FStarC_TypeChecker_Common.relation =
                                  (problem.FStarC_TypeChecker_Common.relation);
                                FStarC_TypeChecker_Common.rhs = t_abs;
                                FStarC_TypeChecker_Common.element =
                                  (problem.FStarC_TypeChecker_Common.element);
                                FStarC_TypeChecker_Common.logical_guard =
                                  (problem.FStarC_TypeChecker_Common.logical_guard);
                                FStarC_TypeChecker_Common.logical_guard_uvar
                                  =
                                  (problem.FStarC_TypeChecker_Common.logical_guard_uvar);
                                FStarC_TypeChecker_Common.reason =
                                  (problem.FStarC_TypeChecker_Common.reason);
                                FStarC_TypeChecker_Common.loc =
                                  (problem.FStarC_TypeChecker_Common.loc);
                                FStarC_TypeChecker_Common.rank =
                                  (problem.FStarC_TypeChecker_Common.rank);
                                FStarC_TypeChecker_Common.logical =
                                  (problem.FStarC_TypeChecker_Common.logical)
                              } wl
                        | uu___12 ->
                            let uu___13 =
                              FStarC_Syntax_Util.head_and_args not_abs in
                            (match uu___13 with
                             | (head, uu___14) ->
                                 let uu___15 =
                                   wl.smt_ok &&
                                     (may_relate wl.tcenv (p_rel orig) head) in
                                 if uu___15
                                 then
                                   let uu___16 = mk_eq2 wl orig t_abs not_abs in
                                   (match uu___16 with
                                    | (g, wl1) ->
                                        let uu___17 =
                                          solve_prob orig
                                            (FStar_Pervasives_Native.Some g)
                                            [] wl1 in
                                        solve uu___17)
                                 else
                                   (let uu___17 =
                                      FStarC_Thunk.mkv
                                        "head tag mismatch: RHS is an abstraction" in
                                    giveup wl uu___17 orig)))
                 | (FStar_Pervasives.Inr not_abs, FStar_Pervasives.Inl t_abs)
                     ->
                     let uu___9 =
                       (is_flex not_abs) &&
                         ((p_rel orig) = FStarC_TypeChecker_Common.EQ) in
                     if uu___9
                     then
                       let uu___10 = destruct_flex_t not_abs wl in
                       (match uu___10 with
                        | (flex, wl1) ->
                            solve_t_flex_rigid_eq orig wl1 flex t_abs)
                     else
                       (let uu___11 =
                          head_matches_delta env false wl.smt_ok not_abs
                            t_abs in
                        match uu___11 with
                        | (HeadMatch uu___12, FStar_Pervasives_Native.Some
                           (not_abs', uu___13)) ->
                            solve_t
                              {
                                FStarC_TypeChecker_Common.pid =
                                  (problem.FStarC_TypeChecker_Common.pid);
                                FStarC_TypeChecker_Common.lhs = not_abs';
                                FStarC_TypeChecker_Common.relation =
                                  (problem.FStarC_TypeChecker_Common.relation);
                                FStarC_TypeChecker_Common.rhs = t_abs;
                                FStarC_TypeChecker_Common.element =
                                  (problem.FStarC_TypeChecker_Common.element);
                                FStarC_TypeChecker_Common.logical_guard =
                                  (problem.FStarC_TypeChecker_Common.logical_guard);
                                FStarC_TypeChecker_Common.logical_guard_uvar
                                  =
                                  (problem.FStarC_TypeChecker_Common.logical_guard_uvar);
                                FStarC_TypeChecker_Common.reason =
                                  (problem.FStarC_TypeChecker_Common.reason);
                                FStarC_TypeChecker_Common.loc =
                                  (problem.FStarC_TypeChecker_Common.loc);
                                FStarC_TypeChecker_Common.rank =
                                  (problem.FStarC_TypeChecker_Common.rank);
                                FStarC_TypeChecker_Common.logical =
                                  (problem.FStarC_TypeChecker_Common.logical)
                              } wl
                        | uu___12 ->
                            let uu___13 =
                              FStarC_Syntax_Util.head_and_args not_abs in
                            (match uu___13 with
                             | (head, uu___14) ->
                                 let uu___15 =
                                   wl.smt_ok &&
                                     (may_relate wl.tcenv (p_rel orig) head) in
                                 if uu___15
                                 then
                                   let uu___16 = mk_eq2 wl orig t_abs not_abs in
                                   (match uu___16 with
                                    | (g, wl1) ->
                                        let uu___17 =
                                          solve_prob orig
                                            (FStar_Pervasives_Native.Some g)
                                            [] wl1 in
                                        solve uu___17)
                                 else
                                   (let uu___17 =
                                      FStarC_Thunk.mkv
                                        "head tag mismatch: RHS is an abstraction" in
                                    giveup wl uu___17 orig)))
                 | uu___9 ->
                     failwith
                       "Impossible: at least one side is an abstraction")
            | (FStarC_Syntax_Syntax.Tm_refine uu___7, uu___8) ->
                let t21 =
                  let uu___9 = base_and_refinement (p_env wl orig) t2 in
                  force_refinement uu___9 in
                solve_t'
                  {
                    FStarC_TypeChecker_Common.pid =
                      (problem.FStarC_TypeChecker_Common.pid);
                    FStarC_TypeChecker_Common.lhs =
                      (problem.FStarC_TypeChecker_Common.lhs);
                    FStarC_TypeChecker_Common.relation =
                      (problem.FStarC_TypeChecker_Common.relation);
                    FStarC_TypeChecker_Common.rhs = t21;
                    FStarC_TypeChecker_Common.element =
                      (problem.FStarC_TypeChecker_Common.element);
                    FStarC_TypeChecker_Common.logical_guard =
                      (problem.FStarC_TypeChecker_Common.logical_guard);
                    FStarC_TypeChecker_Common.logical_guard_uvar =
                      (problem.FStarC_TypeChecker_Common.logical_guard_uvar);
                    FStarC_TypeChecker_Common.reason =
                      (problem.FStarC_TypeChecker_Common.reason);
                    FStarC_TypeChecker_Common.loc =
                      (problem.FStarC_TypeChecker_Common.loc);
                    FStarC_TypeChecker_Common.rank =
                      (problem.FStarC_TypeChecker_Common.rank);
                    FStarC_TypeChecker_Common.logical =
                      (problem.FStarC_TypeChecker_Common.logical)
                  } wl
            | (uu___7, FStarC_Syntax_Syntax.Tm_refine uu___8) ->
                let t11 =
                  let uu___9 = base_and_refinement (p_env wl orig) t1 in
                  force_refinement uu___9 in
                solve_t'
                  {
                    FStarC_TypeChecker_Common.pid =
                      (problem.FStarC_TypeChecker_Common.pid);
                    FStarC_TypeChecker_Common.lhs = t11;
                    FStarC_TypeChecker_Common.relation =
                      (problem.FStarC_TypeChecker_Common.relation);
                    FStarC_TypeChecker_Common.rhs =
                      (problem.FStarC_TypeChecker_Common.rhs);
                    FStarC_TypeChecker_Common.element =
                      (problem.FStarC_TypeChecker_Common.element);
                    FStarC_TypeChecker_Common.logical_guard =
                      (problem.FStarC_TypeChecker_Common.logical_guard);
                    FStarC_TypeChecker_Common.logical_guard_uvar =
                      (problem.FStarC_TypeChecker_Common.logical_guard_uvar);
                    FStarC_TypeChecker_Common.reason =
                      (problem.FStarC_TypeChecker_Common.reason);
                    FStarC_TypeChecker_Common.loc =
                      (problem.FStarC_TypeChecker_Common.loc);
                    FStarC_TypeChecker_Common.rank =
                      (problem.FStarC_TypeChecker_Common.rank);
                    FStarC_TypeChecker_Common.logical =
                      (problem.FStarC_TypeChecker_Common.logical)
                  } wl
            | (FStarC_Syntax_Syntax.Tm_match
               { FStarC_Syntax_Syntax.scrutinee = s1;
                 FStarC_Syntax_Syntax.ret_opt = uu___7;
                 FStarC_Syntax_Syntax.brs = brs1;
                 FStarC_Syntax_Syntax.rc_opt1 = uu___8;_},
               FStarC_Syntax_Syntax.Tm_match
               { FStarC_Syntax_Syntax.scrutinee = s2;
                 FStarC_Syntax_Syntax.ret_opt = uu___9;
                 FStarC_Syntax_Syntax.brs = brs2;
                 FStarC_Syntax_Syntax.rc_opt1 = uu___10;_})
                ->
                let by_smt uu___11 =
                  let uu___12 = guard_of_prob wl problem t1 t2 in
                  match uu___12 with
                  | (guard, wl1) ->
                      let uu___13 =
                        solve_prob orig (FStar_Pervasives_Native.Some guard)
                          [] wl1 in
                      solve uu___13 in
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
                                    FStarC_Syntax_Syntax.eq_pat p1 p2 in
                                  Prims.op_Negation uu___16 in
                                if uu___15
                                then FStar_Pervasives_Native.None
                                else
                                  (let uu___17 =
                                     FStarC_Syntax_Subst.open_branch' br1 in
                                   match uu___17 with
                                   | ((p11, w11, e1), s) ->
                                       let uu___18 = br2 in
                                       (match uu___18 with
                                        | (p21, w21, e2) ->
                                            let w22 =
                                              FStarC_Compiler_Util.map_opt
                                                w21
                                                (FStarC_Syntax_Subst.subst s) in
                                            let e21 =
                                              FStarC_Syntax_Subst.subst s e2 in
                                            let scope =
                                              let uu___19 =
                                                FStarC_Syntax_Syntax.pat_bvs
                                                  p11 in
                                              FStarC_Compiler_List.map
                                                FStarC_Syntax_Syntax.mk_binder
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
                                                      FStarC_TypeChecker_Common.EQ
                                                      w23
                                                      FStar_Pervasives_Native.None
                                                      "when clause" in
                                                  (match uu___20 with
                                                   | (p, wl2) ->
                                                       FStar_Pervasives_Native.Some
                                                         ([(scope, p)], wl2)) in
                                            FStarC_Compiler_Util.bind_opt
                                              uu___19
                                              (fun uu___20 ->
                                                 match uu___20 with
                                                 | (wprobs, wl2) ->
                                                     let uu___21 =
                                                       mk_t_problem wl2 scope
                                                         orig e1
                                                         FStarC_TypeChecker_Common.EQ
                                                         e21
                                                         FStar_Pervasives_Native.None
                                                         "branch body" in
                                                     (match uu___21 with
                                                      | (prob, wl3) ->
                                                          ((let uu___23 =
                                                              FStarC_Compiler_Effect.op_Bang
                                                                dbg_Rel in
                                                            if uu___23
                                                            then
                                                              let uu___24 =
                                                                prob_to_string'
                                                                  wl3 prob in
                                                              let uu___25 =
                                                                FStarC_Class_Show.show
                                                                  (FStarC_Class_Show.show_list
                                                                    FStarC_Syntax_Print.showable_binder)
                                                                  scope in
                                                              FStarC_Compiler_Util.print2
                                                                "Created problem for branches %s with scope %s\n"
                                                                uu___24
                                                                uu___25
                                                            else ());
                                                           (let uu___23 =
                                                              solve_branches
                                                                wl3 rs1 rs2 in
                                                            FStarC_Compiler_Util.bind_opt
                                                              uu___23
                                                              (fun uu___24 ->
                                                                 match uu___24
                                                                 with
                                                                 | (r, wl4)
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (((scope,
                                                                    prob) ::
                                                                    (FStarC_Compiler_List.op_At
                                                                    wprobs r)),
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
                          FStarC_Thunk.mkv "Tm_match branches don't match" in
                        giveup wl uu___13 orig)
                 | FStar_Pervasives_Native.Some (sub_probs, wl1) ->
                     let uu___12 =
                       mk_t_problem wl1 [] orig s1
                         FStarC_TypeChecker_Common.EQ s2
                         FStar_Pervasives_Native.None "match scrutinee" in
                     (match uu___12 with
                      | (sc_prob, wl2) ->
                          let sub_probs1 = ([], sc_prob) :: sub_probs in
                          let formula =
                            let uu___13 =
                              FStarC_Compiler_List.map
                                (fun uu___14 ->
                                   match uu___14 with
                                   | (scope, p) ->
                                       FStarC_TypeChecker_Env.close_forall
                                         (p_env wl2 orig) scope (p_guard p))
                                sub_probs1 in
                            FStarC_Syntax_Util.mk_conj_l uu___13 in
                          let tx = FStarC_Syntax_Unionfind.new_transaction () in
                          let wl3 =
                            solve_prob orig
                              (FStar_Pervasives_Native.Some formula) [] wl2 in
                          let uu___13 =
                            let uu___14 =
                              let uu___15 =
                                FStarC_Compiler_List.map
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
                                  umax_heuristic_ok = (wl3.umax_heuristic_ok);
                                  tcenv = (wl3.tcenv);
                                  wl_implicits = (wl3.wl_implicits);
                                  repr_subcomp_allowed =
                                    (wl3.repr_subcomp_allowed);
                                  typeclass_variables =
                                    (wl3.typeclass_variables)
                                } in
                            solve uu___14 in
                          (match uu___13 with
                           | Success (ds, ds', imp) ->
                               (FStarC_Syntax_Unionfind.commit tx;
                                Success (ds, ds', imp))
                           | Failed uu___14 ->
                               (FStarC_Syntax_Unionfind.rollback tx;
                                if wl3.smt_ok
                                then by_smt ()
                                else
                                  (let uu___17 =
                                     FStarC_Thunk.mkv
                                       "Could not unify matches without SMT" in
                                   giveup wl3 uu___17 orig)))))
            | (FStarC_Syntax_Syntax.Tm_match uu___7, uu___8) ->
                let head1 =
                  let uu___9 = FStarC_Syntax_Util.head_and_args t1 in
                  FStar_Pervasives_Native.fst uu___9 in
                let head2 =
                  let uu___9 = FStarC_Syntax_Util.head_and_args t2 in
                  FStar_Pervasives_Native.fst uu___9 in
                ((let uu___10 = FStarC_Compiler_Effect.op_Bang dbg_Rel in
                  if uu___10
                  then
                    let uu___11 =
                      let uu___12 =
                        FStarC_Class_Show.show FStarC_Class_Show.showable_int
                          problem.FStarC_TypeChecker_Common.pid in
                      let uu___13 =
                        let uu___14 =
                          FStarC_Class_Show.show
                            FStarC_Class_Show.showable_bool wl.smt_ok in
                        let uu___15 =
                          let uu___16 =
                            FStarC_Class_Show.show
                              FStarC_Syntax_Print.showable_term head1 in
                          let uu___17 =
                            let uu___18 =
                              let uu___19 =
                                FStarC_TypeChecker_Env.is_interpreted
                                  wl.tcenv head1 in
                              FStarC_Class_Show.show
                                FStarC_Class_Show.showable_bool uu___19 in
                            let uu___19 =
                              let uu___20 =
                                let uu___21 = no_free_uvars t1 in
                                FStarC_Class_Show.show
                                  FStarC_Class_Show.showable_bool uu___21 in
                              let uu___21 =
                                let uu___22 =
                                  FStarC_Class_Show.show
                                    FStarC_Syntax_Print.showable_term head2 in
                                let uu___23 =
                                  let uu___24 =
                                    let uu___25 =
                                      FStarC_TypeChecker_Env.is_interpreted
                                        wl.tcenv head2 in
                                    FStarC_Class_Show.show
                                      FStarC_Class_Show.showable_bool uu___25 in
                                  let uu___25 =
                                    let uu___26 =
                                      let uu___27 = no_free_uvars t2 in
                                      FStarC_Class_Show.show
                                        FStarC_Class_Show.showable_bool
                                        uu___27 in
                                    [uu___26] in
                                  uu___24 :: uu___25 in
                                uu___22 :: uu___23 in
                              uu___20 :: uu___21 in
                            uu___18 :: uu___19 in
                          uu___16 :: uu___17 in
                        uu___14 :: uu___15 in
                      uu___12 :: uu___13 in
                    FStarC_Compiler_Util.print
                      ">> (%s) (smtok=%s)\n>>> head1 = %s [interpreted=%s; no_free_uvars=%s]\n>>> head2 = %s [interpreted=%s; no_free_uvars=%s]\n"
                      uu___11
                  else ());
                 (let equal t11 t21 =
                    let env = p_env wl orig in
                    let r =
                      FStarC_TypeChecker_TermEqAndSimplify.eq_tm env t11 t21 in
                    match r with
                    | FStarC_TypeChecker_TermEqAndSimplify.Equal -> true
                    | FStarC_TypeChecker_TermEqAndSimplify.NotEqual -> false
                    | FStarC_TypeChecker_TermEqAndSimplify.Unknown ->
                        let steps =
                          [FStarC_TypeChecker_Env.UnfoldUntil
                             FStarC_Syntax_Syntax.delta_constant;
                          FStarC_TypeChecker_Env.Primops;
                          FStarC_TypeChecker_Env.Beta;
                          FStarC_TypeChecker_Env.Eager_unfolding;
                          FStarC_TypeChecker_Env.Iota] in
                        let t12 =
                          norm_with_steps
                            "FStarC.TypeChecker.Rel.norm_with_steps.2" steps
                            env t11 in
                        let t22 =
                          norm_with_steps
                            "FStarC.TypeChecker.Rel.norm_with_steps.3" steps
                            env t21 in
                        let uu___10 =
                          FStarC_TypeChecker_TermEqAndSimplify.eq_tm env t12
                            t22 in
                        uu___10 = FStarC_TypeChecker_TermEqAndSimplify.Equal in
                  let uu___10 =
                    ((FStarC_TypeChecker_Env.is_interpreted wl.tcenv head1)
                       ||
                       (FStarC_TypeChecker_Env.is_interpreted wl.tcenv head2))
                      &&
                      (problem.FStarC_TypeChecker_Common.relation =
                         FStarC_TypeChecker_Common.EQ) in
                  if uu___10
                  then
                    let solve_with_smt uu___11 =
                      let uu___12 =
                        let uu___13 = equal t1 t2 in
                        if uu___13
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu___15 = mk_eq2 wl orig t1 t2 in
                           match uu___15 with
                           | (g, wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1)) in
                      match uu___12 with
                      | (guard, wl1) ->
                          let uu___13 = solve_prob orig guard [] wl1 in
                          solve uu___13 in
                    let uu___11 = (no_free_uvars t1) && (no_free_uvars t2) in
                    (if uu___11
                     then
                       let uu___12 =
                         (Prims.op_Negation wl.smt_ok) ||
                           (FStarC_Options.ml_ish ()) in
                       (if uu___12
                        then
                          let uu___13 = equal t1 t2 in
                          (if uu___13
                           then
                             let uu___14 =
                               solve_prob orig FStar_Pervasives_Native.None
                                 [] wl in
                             solve uu___14
                           else
                             rigid_rigid_delta problem wl head1 head2 t1 t2)
                        else solve_with_smt ())
                     else
                       (let uu___13 =
                          (Prims.op_Negation wl.smt_ok) ||
                            (FStarC_Options.ml_ish ()) in
                        if uu___13
                        then rigid_rigid_delta problem wl head1 head2 t1 t2
                        else
                          try_solve_then_or_else wl
                            (fun wl_empty ->
                               rigid_rigid_delta problem wl_empty head1 head2
                                 t1 t2) (fun wl1 -> solve wl1)
                            (fun uu___15 -> solve_with_smt ())))
                  else rigid_rigid_delta problem wl head1 head2 t1 t2))
            | (FStarC_Syntax_Syntax.Tm_uinst uu___7, uu___8) ->
                let head1 =
                  let uu___9 = FStarC_Syntax_Util.head_and_args t1 in
                  FStar_Pervasives_Native.fst uu___9 in
                let head2 =
                  let uu___9 = FStarC_Syntax_Util.head_and_args t2 in
                  FStar_Pervasives_Native.fst uu___9 in
                ((let uu___10 = FStarC_Compiler_Effect.op_Bang dbg_Rel in
                  if uu___10
                  then
                    let uu___11 =
                      let uu___12 =
                        FStarC_Class_Show.show FStarC_Class_Show.showable_int
                          problem.FStarC_TypeChecker_Common.pid in
                      let uu___13 =
                        let uu___14 =
                          FStarC_Class_Show.show
                            FStarC_Class_Show.showable_bool wl.smt_ok in
                        let uu___15 =
                          let uu___16 =
                            FStarC_Class_Show.show
                              FStarC_Syntax_Print.showable_term head1 in
                          let uu___17 =
                            let uu___18 =
                              let uu___19 =
                                FStarC_TypeChecker_Env.is_interpreted
                                  wl.tcenv head1 in
                              FStarC_Class_Show.show
                                FStarC_Class_Show.showable_bool uu___19 in
                            let uu___19 =
                              let uu___20 =
                                let uu___21 = no_free_uvars t1 in
                                FStarC_Class_Show.show
                                  FStarC_Class_Show.showable_bool uu___21 in
                              let uu___21 =
                                let uu___22 =
                                  FStarC_Class_Show.show
                                    FStarC_Syntax_Print.showable_term head2 in
                                let uu___23 =
                                  let uu___24 =
                                    let uu___25 =
                                      FStarC_TypeChecker_Env.is_interpreted
                                        wl.tcenv head2 in
                                    FStarC_Class_Show.show
                                      FStarC_Class_Show.showable_bool uu___25 in
                                  let uu___25 =
                                    let uu___26 =
                                      let uu___27 = no_free_uvars t2 in
                                      FStarC_Class_Show.show
                                        FStarC_Class_Show.showable_bool
                                        uu___27 in
                                    [uu___26] in
                                  uu___24 :: uu___25 in
                                uu___22 :: uu___23 in
                              uu___20 :: uu___21 in
                            uu___18 :: uu___19 in
                          uu___16 :: uu___17 in
                        uu___14 :: uu___15 in
                      uu___12 :: uu___13 in
                    FStarC_Compiler_Util.print
                      ">> (%s) (smtok=%s)\n>>> head1 = %s [interpreted=%s; no_free_uvars=%s]\n>>> head2 = %s [interpreted=%s; no_free_uvars=%s]\n"
                      uu___11
                  else ());
                 (let equal t11 t21 =
                    let env = p_env wl orig in
                    let r =
                      FStarC_TypeChecker_TermEqAndSimplify.eq_tm env t11 t21 in
                    match r with
                    | FStarC_TypeChecker_TermEqAndSimplify.Equal -> true
                    | FStarC_TypeChecker_TermEqAndSimplify.NotEqual -> false
                    | FStarC_TypeChecker_TermEqAndSimplify.Unknown ->
                        let steps =
                          [FStarC_TypeChecker_Env.UnfoldUntil
                             FStarC_Syntax_Syntax.delta_constant;
                          FStarC_TypeChecker_Env.Primops;
                          FStarC_TypeChecker_Env.Beta;
                          FStarC_TypeChecker_Env.Eager_unfolding;
                          FStarC_TypeChecker_Env.Iota] in
                        let t12 =
                          norm_with_steps
                            "FStarC.TypeChecker.Rel.norm_with_steps.2" steps
                            env t11 in
                        let t22 =
                          norm_with_steps
                            "FStarC.TypeChecker.Rel.norm_with_steps.3" steps
                            env t21 in
                        let uu___10 =
                          FStarC_TypeChecker_TermEqAndSimplify.eq_tm env t12
                            t22 in
                        uu___10 = FStarC_TypeChecker_TermEqAndSimplify.Equal in
                  let uu___10 =
                    ((FStarC_TypeChecker_Env.is_interpreted wl.tcenv head1)
                       ||
                       (FStarC_TypeChecker_Env.is_interpreted wl.tcenv head2))
                      &&
                      (problem.FStarC_TypeChecker_Common.relation =
                         FStarC_TypeChecker_Common.EQ) in
                  if uu___10
                  then
                    let solve_with_smt uu___11 =
                      let uu___12 =
                        let uu___13 = equal t1 t2 in
                        if uu___13
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu___15 = mk_eq2 wl orig t1 t2 in
                           match uu___15 with
                           | (g, wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1)) in
                      match uu___12 with
                      | (guard, wl1) ->
                          let uu___13 = solve_prob orig guard [] wl1 in
                          solve uu___13 in
                    let uu___11 = (no_free_uvars t1) && (no_free_uvars t2) in
                    (if uu___11
                     then
                       let uu___12 =
                         (Prims.op_Negation wl.smt_ok) ||
                           (FStarC_Options.ml_ish ()) in
                       (if uu___12
                        then
                          let uu___13 = equal t1 t2 in
                          (if uu___13
                           then
                             let uu___14 =
                               solve_prob orig FStar_Pervasives_Native.None
                                 [] wl in
                             solve uu___14
                           else
                             rigid_rigid_delta problem wl head1 head2 t1 t2)
                        else solve_with_smt ())
                     else
                       (let uu___13 =
                          (Prims.op_Negation wl.smt_ok) ||
                            (FStarC_Options.ml_ish ()) in
                        if uu___13
                        then rigid_rigid_delta problem wl head1 head2 t1 t2
                        else
                          try_solve_then_or_else wl
                            (fun wl_empty ->
                               rigid_rigid_delta problem wl_empty head1 head2
                                 t1 t2) (fun wl1 -> solve wl1)
                            (fun uu___15 -> solve_with_smt ())))
                  else rigid_rigid_delta problem wl head1 head2 t1 t2))
            | (FStarC_Syntax_Syntax.Tm_name uu___7, uu___8) ->
                let head1 =
                  let uu___9 = FStarC_Syntax_Util.head_and_args t1 in
                  FStar_Pervasives_Native.fst uu___9 in
                let head2 =
                  let uu___9 = FStarC_Syntax_Util.head_and_args t2 in
                  FStar_Pervasives_Native.fst uu___9 in
                ((let uu___10 = FStarC_Compiler_Effect.op_Bang dbg_Rel in
                  if uu___10
                  then
                    let uu___11 =
                      let uu___12 =
                        FStarC_Class_Show.show FStarC_Class_Show.showable_int
                          problem.FStarC_TypeChecker_Common.pid in
                      let uu___13 =
                        let uu___14 =
                          FStarC_Class_Show.show
                            FStarC_Class_Show.showable_bool wl.smt_ok in
                        let uu___15 =
                          let uu___16 =
                            FStarC_Class_Show.show
                              FStarC_Syntax_Print.showable_term head1 in
                          let uu___17 =
                            let uu___18 =
                              let uu___19 =
                                FStarC_TypeChecker_Env.is_interpreted
                                  wl.tcenv head1 in
                              FStarC_Class_Show.show
                                FStarC_Class_Show.showable_bool uu___19 in
                            let uu___19 =
                              let uu___20 =
                                let uu___21 = no_free_uvars t1 in
                                FStarC_Class_Show.show
                                  FStarC_Class_Show.showable_bool uu___21 in
                              let uu___21 =
                                let uu___22 =
                                  FStarC_Class_Show.show
                                    FStarC_Syntax_Print.showable_term head2 in
                                let uu___23 =
                                  let uu___24 =
                                    let uu___25 =
                                      FStarC_TypeChecker_Env.is_interpreted
                                        wl.tcenv head2 in
                                    FStarC_Class_Show.show
                                      FStarC_Class_Show.showable_bool uu___25 in
                                  let uu___25 =
                                    let uu___26 =
                                      let uu___27 = no_free_uvars t2 in
                                      FStarC_Class_Show.show
                                        FStarC_Class_Show.showable_bool
                                        uu___27 in
                                    [uu___26] in
                                  uu___24 :: uu___25 in
                                uu___22 :: uu___23 in
                              uu___20 :: uu___21 in
                            uu___18 :: uu___19 in
                          uu___16 :: uu___17 in
                        uu___14 :: uu___15 in
                      uu___12 :: uu___13 in
                    FStarC_Compiler_Util.print
                      ">> (%s) (smtok=%s)\n>>> head1 = %s [interpreted=%s; no_free_uvars=%s]\n>>> head2 = %s [interpreted=%s; no_free_uvars=%s]\n"
                      uu___11
                  else ());
                 (let equal t11 t21 =
                    let env = p_env wl orig in
                    let r =
                      FStarC_TypeChecker_TermEqAndSimplify.eq_tm env t11 t21 in
                    match r with
                    | FStarC_TypeChecker_TermEqAndSimplify.Equal -> true
                    | FStarC_TypeChecker_TermEqAndSimplify.NotEqual -> false
                    | FStarC_TypeChecker_TermEqAndSimplify.Unknown ->
                        let steps =
                          [FStarC_TypeChecker_Env.UnfoldUntil
                             FStarC_Syntax_Syntax.delta_constant;
                          FStarC_TypeChecker_Env.Primops;
                          FStarC_TypeChecker_Env.Beta;
                          FStarC_TypeChecker_Env.Eager_unfolding;
                          FStarC_TypeChecker_Env.Iota] in
                        let t12 =
                          norm_with_steps
                            "FStarC.TypeChecker.Rel.norm_with_steps.2" steps
                            env t11 in
                        let t22 =
                          norm_with_steps
                            "FStarC.TypeChecker.Rel.norm_with_steps.3" steps
                            env t21 in
                        let uu___10 =
                          FStarC_TypeChecker_TermEqAndSimplify.eq_tm env t12
                            t22 in
                        uu___10 = FStarC_TypeChecker_TermEqAndSimplify.Equal in
                  let uu___10 =
                    ((FStarC_TypeChecker_Env.is_interpreted wl.tcenv head1)
                       ||
                       (FStarC_TypeChecker_Env.is_interpreted wl.tcenv head2))
                      &&
                      (problem.FStarC_TypeChecker_Common.relation =
                         FStarC_TypeChecker_Common.EQ) in
                  if uu___10
                  then
                    let solve_with_smt uu___11 =
                      let uu___12 =
                        let uu___13 = equal t1 t2 in
                        if uu___13
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu___15 = mk_eq2 wl orig t1 t2 in
                           match uu___15 with
                           | (g, wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1)) in
                      match uu___12 with
                      | (guard, wl1) ->
                          let uu___13 = solve_prob orig guard [] wl1 in
                          solve uu___13 in
                    let uu___11 = (no_free_uvars t1) && (no_free_uvars t2) in
                    (if uu___11
                     then
                       let uu___12 =
                         (Prims.op_Negation wl.smt_ok) ||
                           (FStarC_Options.ml_ish ()) in
                       (if uu___12
                        then
                          let uu___13 = equal t1 t2 in
                          (if uu___13
                           then
                             let uu___14 =
                               solve_prob orig FStar_Pervasives_Native.None
                                 [] wl in
                             solve uu___14
                           else
                             rigid_rigid_delta problem wl head1 head2 t1 t2)
                        else solve_with_smt ())
                     else
                       (let uu___13 =
                          (Prims.op_Negation wl.smt_ok) ||
                            (FStarC_Options.ml_ish ()) in
                        if uu___13
                        then rigid_rigid_delta problem wl head1 head2 t1 t2
                        else
                          try_solve_then_or_else wl
                            (fun wl_empty ->
                               rigid_rigid_delta problem wl_empty head1 head2
                                 t1 t2) (fun wl1 -> solve wl1)
                            (fun uu___15 -> solve_with_smt ())))
                  else rigid_rigid_delta problem wl head1 head2 t1 t2))
            | (FStarC_Syntax_Syntax.Tm_constant uu___7, uu___8) ->
                let head1 =
                  let uu___9 = FStarC_Syntax_Util.head_and_args t1 in
                  FStar_Pervasives_Native.fst uu___9 in
                let head2 =
                  let uu___9 = FStarC_Syntax_Util.head_and_args t2 in
                  FStar_Pervasives_Native.fst uu___9 in
                ((let uu___10 = FStarC_Compiler_Effect.op_Bang dbg_Rel in
                  if uu___10
                  then
                    let uu___11 =
                      let uu___12 =
                        FStarC_Class_Show.show FStarC_Class_Show.showable_int
                          problem.FStarC_TypeChecker_Common.pid in
                      let uu___13 =
                        let uu___14 =
                          FStarC_Class_Show.show
                            FStarC_Class_Show.showable_bool wl.smt_ok in
                        let uu___15 =
                          let uu___16 =
                            FStarC_Class_Show.show
                              FStarC_Syntax_Print.showable_term head1 in
                          let uu___17 =
                            let uu___18 =
                              let uu___19 =
                                FStarC_TypeChecker_Env.is_interpreted
                                  wl.tcenv head1 in
                              FStarC_Class_Show.show
                                FStarC_Class_Show.showable_bool uu___19 in
                            let uu___19 =
                              let uu___20 =
                                let uu___21 = no_free_uvars t1 in
                                FStarC_Class_Show.show
                                  FStarC_Class_Show.showable_bool uu___21 in
                              let uu___21 =
                                let uu___22 =
                                  FStarC_Class_Show.show
                                    FStarC_Syntax_Print.showable_term head2 in
                                let uu___23 =
                                  let uu___24 =
                                    let uu___25 =
                                      FStarC_TypeChecker_Env.is_interpreted
                                        wl.tcenv head2 in
                                    FStarC_Class_Show.show
                                      FStarC_Class_Show.showable_bool uu___25 in
                                  let uu___25 =
                                    let uu___26 =
                                      let uu___27 = no_free_uvars t2 in
                                      FStarC_Class_Show.show
                                        FStarC_Class_Show.showable_bool
                                        uu___27 in
                                    [uu___26] in
                                  uu___24 :: uu___25 in
                                uu___22 :: uu___23 in
                              uu___20 :: uu___21 in
                            uu___18 :: uu___19 in
                          uu___16 :: uu___17 in
                        uu___14 :: uu___15 in
                      uu___12 :: uu___13 in
                    FStarC_Compiler_Util.print
                      ">> (%s) (smtok=%s)\n>>> head1 = %s [interpreted=%s; no_free_uvars=%s]\n>>> head2 = %s [interpreted=%s; no_free_uvars=%s]\n"
                      uu___11
                  else ());
                 (let equal t11 t21 =
                    let env = p_env wl orig in
                    let r =
                      FStarC_TypeChecker_TermEqAndSimplify.eq_tm env t11 t21 in
                    match r with
                    | FStarC_TypeChecker_TermEqAndSimplify.Equal -> true
                    | FStarC_TypeChecker_TermEqAndSimplify.NotEqual -> false
                    | FStarC_TypeChecker_TermEqAndSimplify.Unknown ->
                        let steps =
                          [FStarC_TypeChecker_Env.UnfoldUntil
                             FStarC_Syntax_Syntax.delta_constant;
                          FStarC_TypeChecker_Env.Primops;
                          FStarC_TypeChecker_Env.Beta;
                          FStarC_TypeChecker_Env.Eager_unfolding;
                          FStarC_TypeChecker_Env.Iota] in
                        let t12 =
                          norm_with_steps
                            "FStarC.TypeChecker.Rel.norm_with_steps.2" steps
                            env t11 in
                        let t22 =
                          norm_with_steps
                            "FStarC.TypeChecker.Rel.norm_with_steps.3" steps
                            env t21 in
                        let uu___10 =
                          FStarC_TypeChecker_TermEqAndSimplify.eq_tm env t12
                            t22 in
                        uu___10 = FStarC_TypeChecker_TermEqAndSimplify.Equal in
                  let uu___10 =
                    ((FStarC_TypeChecker_Env.is_interpreted wl.tcenv head1)
                       ||
                       (FStarC_TypeChecker_Env.is_interpreted wl.tcenv head2))
                      &&
                      (problem.FStarC_TypeChecker_Common.relation =
                         FStarC_TypeChecker_Common.EQ) in
                  if uu___10
                  then
                    let solve_with_smt uu___11 =
                      let uu___12 =
                        let uu___13 = equal t1 t2 in
                        if uu___13
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu___15 = mk_eq2 wl orig t1 t2 in
                           match uu___15 with
                           | (g, wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1)) in
                      match uu___12 with
                      | (guard, wl1) ->
                          let uu___13 = solve_prob orig guard [] wl1 in
                          solve uu___13 in
                    let uu___11 = (no_free_uvars t1) && (no_free_uvars t2) in
                    (if uu___11
                     then
                       let uu___12 =
                         (Prims.op_Negation wl.smt_ok) ||
                           (FStarC_Options.ml_ish ()) in
                       (if uu___12
                        then
                          let uu___13 = equal t1 t2 in
                          (if uu___13
                           then
                             let uu___14 =
                               solve_prob orig FStar_Pervasives_Native.None
                                 [] wl in
                             solve uu___14
                           else
                             rigid_rigid_delta problem wl head1 head2 t1 t2)
                        else solve_with_smt ())
                     else
                       (let uu___13 =
                          (Prims.op_Negation wl.smt_ok) ||
                            (FStarC_Options.ml_ish ()) in
                        if uu___13
                        then rigid_rigid_delta problem wl head1 head2 t1 t2
                        else
                          try_solve_then_or_else wl
                            (fun wl_empty ->
                               rigid_rigid_delta problem wl_empty head1 head2
                                 t1 t2) (fun wl1 -> solve wl1)
                            (fun uu___15 -> solve_with_smt ())))
                  else rigid_rigid_delta problem wl head1 head2 t1 t2))
            | (FStarC_Syntax_Syntax.Tm_fvar uu___7, uu___8) ->
                let head1 =
                  let uu___9 = FStarC_Syntax_Util.head_and_args t1 in
                  FStar_Pervasives_Native.fst uu___9 in
                let head2 =
                  let uu___9 = FStarC_Syntax_Util.head_and_args t2 in
                  FStar_Pervasives_Native.fst uu___9 in
                ((let uu___10 = FStarC_Compiler_Effect.op_Bang dbg_Rel in
                  if uu___10
                  then
                    let uu___11 =
                      let uu___12 =
                        FStarC_Class_Show.show FStarC_Class_Show.showable_int
                          problem.FStarC_TypeChecker_Common.pid in
                      let uu___13 =
                        let uu___14 =
                          FStarC_Class_Show.show
                            FStarC_Class_Show.showable_bool wl.smt_ok in
                        let uu___15 =
                          let uu___16 =
                            FStarC_Class_Show.show
                              FStarC_Syntax_Print.showable_term head1 in
                          let uu___17 =
                            let uu___18 =
                              let uu___19 =
                                FStarC_TypeChecker_Env.is_interpreted
                                  wl.tcenv head1 in
                              FStarC_Class_Show.show
                                FStarC_Class_Show.showable_bool uu___19 in
                            let uu___19 =
                              let uu___20 =
                                let uu___21 = no_free_uvars t1 in
                                FStarC_Class_Show.show
                                  FStarC_Class_Show.showable_bool uu___21 in
                              let uu___21 =
                                let uu___22 =
                                  FStarC_Class_Show.show
                                    FStarC_Syntax_Print.showable_term head2 in
                                let uu___23 =
                                  let uu___24 =
                                    let uu___25 =
                                      FStarC_TypeChecker_Env.is_interpreted
                                        wl.tcenv head2 in
                                    FStarC_Class_Show.show
                                      FStarC_Class_Show.showable_bool uu___25 in
                                  let uu___25 =
                                    let uu___26 =
                                      let uu___27 = no_free_uvars t2 in
                                      FStarC_Class_Show.show
                                        FStarC_Class_Show.showable_bool
                                        uu___27 in
                                    [uu___26] in
                                  uu___24 :: uu___25 in
                                uu___22 :: uu___23 in
                              uu___20 :: uu___21 in
                            uu___18 :: uu___19 in
                          uu___16 :: uu___17 in
                        uu___14 :: uu___15 in
                      uu___12 :: uu___13 in
                    FStarC_Compiler_Util.print
                      ">> (%s) (smtok=%s)\n>>> head1 = %s [interpreted=%s; no_free_uvars=%s]\n>>> head2 = %s [interpreted=%s; no_free_uvars=%s]\n"
                      uu___11
                  else ());
                 (let equal t11 t21 =
                    let env = p_env wl orig in
                    let r =
                      FStarC_TypeChecker_TermEqAndSimplify.eq_tm env t11 t21 in
                    match r with
                    | FStarC_TypeChecker_TermEqAndSimplify.Equal -> true
                    | FStarC_TypeChecker_TermEqAndSimplify.NotEqual -> false
                    | FStarC_TypeChecker_TermEqAndSimplify.Unknown ->
                        let steps =
                          [FStarC_TypeChecker_Env.UnfoldUntil
                             FStarC_Syntax_Syntax.delta_constant;
                          FStarC_TypeChecker_Env.Primops;
                          FStarC_TypeChecker_Env.Beta;
                          FStarC_TypeChecker_Env.Eager_unfolding;
                          FStarC_TypeChecker_Env.Iota] in
                        let t12 =
                          norm_with_steps
                            "FStarC.TypeChecker.Rel.norm_with_steps.2" steps
                            env t11 in
                        let t22 =
                          norm_with_steps
                            "FStarC.TypeChecker.Rel.norm_with_steps.3" steps
                            env t21 in
                        let uu___10 =
                          FStarC_TypeChecker_TermEqAndSimplify.eq_tm env t12
                            t22 in
                        uu___10 = FStarC_TypeChecker_TermEqAndSimplify.Equal in
                  let uu___10 =
                    ((FStarC_TypeChecker_Env.is_interpreted wl.tcenv head1)
                       ||
                       (FStarC_TypeChecker_Env.is_interpreted wl.tcenv head2))
                      &&
                      (problem.FStarC_TypeChecker_Common.relation =
                         FStarC_TypeChecker_Common.EQ) in
                  if uu___10
                  then
                    let solve_with_smt uu___11 =
                      let uu___12 =
                        let uu___13 = equal t1 t2 in
                        if uu___13
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu___15 = mk_eq2 wl orig t1 t2 in
                           match uu___15 with
                           | (g, wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1)) in
                      match uu___12 with
                      | (guard, wl1) ->
                          let uu___13 = solve_prob orig guard [] wl1 in
                          solve uu___13 in
                    let uu___11 = (no_free_uvars t1) && (no_free_uvars t2) in
                    (if uu___11
                     then
                       let uu___12 =
                         (Prims.op_Negation wl.smt_ok) ||
                           (FStarC_Options.ml_ish ()) in
                       (if uu___12
                        then
                          let uu___13 = equal t1 t2 in
                          (if uu___13
                           then
                             let uu___14 =
                               solve_prob orig FStar_Pervasives_Native.None
                                 [] wl in
                             solve uu___14
                           else
                             rigid_rigid_delta problem wl head1 head2 t1 t2)
                        else solve_with_smt ())
                     else
                       (let uu___13 =
                          (Prims.op_Negation wl.smt_ok) ||
                            (FStarC_Options.ml_ish ()) in
                        if uu___13
                        then rigid_rigid_delta problem wl head1 head2 t1 t2
                        else
                          try_solve_then_or_else wl
                            (fun wl_empty ->
                               rigid_rigid_delta problem wl_empty head1 head2
                                 t1 t2) (fun wl1 -> solve wl1)
                            (fun uu___15 -> solve_with_smt ())))
                  else rigid_rigid_delta problem wl head1 head2 t1 t2))
            | (FStarC_Syntax_Syntax.Tm_app uu___7, uu___8) ->
                let head1 =
                  let uu___9 = FStarC_Syntax_Util.head_and_args t1 in
                  FStar_Pervasives_Native.fst uu___9 in
                let head2 =
                  let uu___9 = FStarC_Syntax_Util.head_and_args t2 in
                  FStar_Pervasives_Native.fst uu___9 in
                ((let uu___10 = FStarC_Compiler_Effect.op_Bang dbg_Rel in
                  if uu___10
                  then
                    let uu___11 =
                      let uu___12 =
                        FStarC_Class_Show.show FStarC_Class_Show.showable_int
                          problem.FStarC_TypeChecker_Common.pid in
                      let uu___13 =
                        let uu___14 =
                          FStarC_Class_Show.show
                            FStarC_Class_Show.showable_bool wl.smt_ok in
                        let uu___15 =
                          let uu___16 =
                            FStarC_Class_Show.show
                              FStarC_Syntax_Print.showable_term head1 in
                          let uu___17 =
                            let uu___18 =
                              let uu___19 =
                                FStarC_TypeChecker_Env.is_interpreted
                                  wl.tcenv head1 in
                              FStarC_Class_Show.show
                                FStarC_Class_Show.showable_bool uu___19 in
                            let uu___19 =
                              let uu___20 =
                                let uu___21 = no_free_uvars t1 in
                                FStarC_Class_Show.show
                                  FStarC_Class_Show.showable_bool uu___21 in
                              let uu___21 =
                                let uu___22 =
                                  FStarC_Class_Show.show
                                    FStarC_Syntax_Print.showable_term head2 in
                                let uu___23 =
                                  let uu___24 =
                                    let uu___25 =
                                      FStarC_TypeChecker_Env.is_interpreted
                                        wl.tcenv head2 in
                                    FStarC_Class_Show.show
                                      FStarC_Class_Show.showable_bool uu___25 in
                                  let uu___25 =
                                    let uu___26 =
                                      let uu___27 = no_free_uvars t2 in
                                      FStarC_Class_Show.show
                                        FStarC_Class_Show.showable_bool
                                        uu___27 in
                                    [uu___26] in
                                  uu___24 :: uu___25 in
                                uu___22 :: uu___23 in
                              uu___20 :: uu___21 in
                            uu___18 :: uu___19 in
                          uu___16 :: uu___17 in
                        uu___14 :: uu___15 in
                      uu___12 :: uu___13 in
                    FStarC_Compiler_Util.print
                      ">> (%s) (smtok=%s)\n>>> head1 = %s [interpreted=%s; no_free_uvars=%s]\n>>> head2 = %s [interpreted=%s; no_free_uvars=%s]\n"
                      uu___11
                  else ());
                 (let equal t11 t21 =
                    let env = p_env wl orig in
                    let r =
                      FStarC_TypeChecker_TermEqAndSimplify.eq_tm env t11 t21 in
                    match r with
                    | FStarC_TypeChecker_TermEqAndSimplify.Equal -> true
                    | FStarC_TypeChecker_TermEqAndSimplify.NotEqual -> false
                    | FStarC_TypeChecker_TermEqAndSimplify.Unknown ->
                        let steps =
                          [FStarC_TypeChecker_Env.UnfoldUntil
                             FStarC_Syntax_Syntax.delta_constant;
                          FStarC_TypeChecker_Env.Primops;
                          FStarC_TypeChecker_Env.Beta;
                          FStarC_TypeChecker_Env.Eager_unfolding;
                          FStarC_TypeChecker_Env.Iota] in
                        let t12 =
                          norm_with_steps
                            "FStarC.TypeChecker.Rel.norm_with_steps.2" steps
                            env t11 in
                        let t22 =
                          norm_with_steps
                            "FStarC.TypeChecker.Rel.norm_with_steps.3" steps
                            env t21 in
                        let uu___10 =
                          FStarC_TypeChecker_TermEqAndSimplify.eq_tm env t12
                            t22 in
                        uu___10 = FStarC_TypeChecker_TermEqAndSimplify.Equal in
                  let uu___10 =
                    ((FStarC_TypeChecker_Env.is_interpreted wl.tcenv head1)
                       ||
                       (FStarC_TypeChecker_Env.is_interpreted wl.tcenv head2))
                      &&
                      (problem.FStarC_TypeChecker_Common.relation =
                         FStarC_TypeChecker_Common.EQ) in
                  if uu___10
                  then
                    let solve_with_smt uu___11 =
                      let uu___12 =
                        let uu___13 = equal t1 t2 in
                        if uu___13
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu___15 = mk_eq2 wl orig t1 t2 in
                           match uu___15 with
                           | (g, wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1)) in
                      match uu___12 with
                      | (guard, wl1) ->
                          let uu___13 = solve_prob orig guard [] wl1 in
                          solve uu___13 in
                    let uu___11 = (no_free_uvars t1) && (no_free_uvars t2) in
                    (if uu___11
                     then
                       let uu___12 =
                         (Prims.op_Negation wl.smt_ok) ||
                           (FStarC_Options.ml_ish ()) in
                       (if uu___12
                        then
                          let uu___13 = equal t1 t2 in
                          (if uu___13
                           then
                             let uu___14 =
                               solve_prob orig FStar_Pervasives_Native.None
                                 [] wl in
                             solve uu___14
                           else
                             rigid_rigid_delta problem wl head1 head2 t1 t2)
                        else solve_with_smt ())
                     else
                       (let uu___13 =
                          (Prims.op_Negation wl.smt_ok) ||
                            (FStarC_Options.ml_ish ()) in
                        if uu___13
                        then rigid_rigid_delta problem wl head1 head2 t1 t2
                        else
                          try_solve_then_or_else wl
                            (fun wl_empty ->
                               rigid_rigid_delta problem wl_empty head1 head2
                                 t1 t2) (fun wl1 -> solve wl1)
                            (fun uu___15 -> solve_with_smt ())))
                  else rigid_rigid_delta problem wl head1 head2 t1 t2))
            | (uu___7, FStarC_Syntax_Syntax.Tm_match uu___8) ->
                let head1 =
                  let uu___9 = FStarC_Syntax_Util.head_and_args t1 in
                  FStar_Pervasives_Native.fst uu___9 in
                let head2 =
                  let uu___9 = FStarC_Syntax_Util.head_and_args t2 in
                  FStar_Pervasives_Native.fst uu___9 in
                ((let uu___10 = FStarC_Compiler_Effect.op_Bang dbg_Rel in
                  if uu___10
                  then
                    let uu___11 =
                      let uu___12 =
                        FStarC_Class_Show.show FStarC_Class_Show.showable_int
                          problem.FStarC_TypeChecker_Common.pid in
                      let uu___13 =
                        let uu___14 =
                          FStarC_Class_Show.show
                            FStarC_Class_Show.showable_bool wl.smt_ok in
                        let uu___15 =
                          let uu___16 =
                            FStarC_Class_Show.show
                              FStarC_Syntax_Print.showable_term head1 in
                          let uu___17 =
                            let uu___18 =
                              let uu___19 =
                                FStarC_TypeChecker_Env.is_interpreted
                                  wl.tcenv head1 in
                              FStarC_Class_Show.show
                                FStarC_Class_Show.showable_bool uu___19 in
                            let uu___19 =
                              let uu___20 =
                                let uu___21 = no_free_uvars t1 in
                                FStarC_Class_Show.show
                                  FStarC_Class_Show.showable_bool uu___21 in
                              let uu___21 =
                                let uu___22 =
                                  FStarC_Class_Show.show
                                    FStarC_Syntax_Print.showable_term head2 in
                                let uu___23 =
                                  let uu___24 =
                                    let uu___25 =
                                      FStarC_TypeChecker_Env.is_interpreted
                                        wl.tcenv head2 in
                                    FStarC_Class_Show.show
                                      FStarC_Class_Show.showable_bool uu___25 in
                                  let uu___25 =
                                    let uu___26 =
                                      let uu___27 = no_free_uvars t2 in
                                      FStarC_Class_Show.show
                                        FStarC_Class_Show.showable_bool
                                        uu___27 in
                                    [uu___26] in
                                  uu___24 :: uu___25 in
                                uu___22 :: uu___23 in
                              uu___20 :: uu___21 in
                            uu___18 :: uu___19 in
                          uu___16 :: uu___17 in
                        uu___14 :: uu___15 in
                      uu___12 :: uu___13 in
                    FStarC_Compiler_Util.print
                      ">> (%s) (smtok=%s)\n>>> head1 = %s [interpreted=%s; no_free_uvars=%s]\n>>> head2 = %s [interpreted=%s; no_free_uvars=%s]\n"
                      uu___11
                  else ());
                 (let equal t11 t21 =
                    let env = p_env wl orig in
                    let r =
                      FStarC_TypeChecker_TermEqAndSimplify.eq_tm env t11 t21 in
                    match r with
                    | FStarC_TypeChecker_TermEqAndSimplify.Equal -> true
                    | FStarC_TypeChecker_TermEqAndSimplify.NotEqual -> false
                    | FStarC_TypeChecker_TermEqAndSimplify.Unknown ->
                        let steps =
                          [FStarC_TypeChecker_Env.UnfoldUntil
                             FStarC_Syntax_Syntax.delta_constant;
                          FStarC_TypeChecker_Env.Primops;
                          FStarC_TypeChecker_Env.Beta;
                          FStarC_TypeChecker_Env.Eager_unfolding;
                          FStarC_TypeChecker_Env.Iota] in
                        let t12 =
                          norm_with_steps
                            "FStarC.TypeChecker.Rel.norm_with_steps.2" steps
                            env t11 in
                        let t22 =
                          norm_with_steps
                            "FStarC.TypeChecker.Rel.norm_with_steps.3" steps
                            env t21 in
                        let uu___10 =
                          FStarC_TypeChecker_TermEqAndSimplify.eq_tm env t12
                            t22 in
                        uu___10 = FStarC_TypeChecker_TermEqAndSimplify.Equal in
                  let uu___10 =
                    ((FStarC_TypeChecker_Env.is_interpreted wl.tcenv head1)
                       ||
                       (FStarC_TypeChecker_Env.is_interpreted wl.tcenv head2))
                      &&
                      (problem.FStarC_TypeChecker_Common.relation =
                         FStarC_TypeChecker_Common.EQ) in
                  if uu___10
                  then
                    let solve_with_smt uu___11 =
                      let uu___12 =
                        let uu___13 = equal t1 t2 in
                        if uu___13
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu___15 = mk_eq2 wl orig t1 t2 in
                           match uu___15 with
                           | (g, wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1)) in
                      match uu___12 with
                      | (guard, wl1) ->
                          let uu___13 = solve_prob orig guard [] wl1 in
                          solve uu___13 in
                    let uu___11 = (no_free_uvars t1) && (no_free_uvars t2) in
                    (if uu___11
                     then
                       let uu___12 =
                         (Prims.op_Negation wl.smt_ok) ||
                           (FStarC_Options.ml_ish ()) in
                       (if uu___12
                        then
                          let uu___13 = equal t1 t2 in
                          (if uu___13
                           then
                             let uu___14 =
                               solve_prob orig FStar_Pervasives_Native.None
                                 [] wl in
                             solve uu___14
                           else
                             rigid_rigid_delta problem wl head1 head2 t1 t2)
                        else solve_with_smt ())
                     else
                       (let uu___13 =
                          (Prims.op_Negation wl.smt_ok) ||
                            (FStarC_Options.ml_ish ()) in
                        if uu___13
                        then rigid_rigid_delta problem wl head1 head2 t1 t2
                        else
                          try_solve_then_or_else wl
                            (fun wl_empty ->
                               rigid_rigid_delta problem wl_empty head1 head2
                                 t1 t2) (fun wl1 -> solve wl1)
                            (fun uu___15 -> solve_with_smt ())))
                  else rigid_rigid_delta problem wl head1 head2 t1 t2))
            | (uu___7, FStarC_Syntax_Syntax.Tm_uinst uu___8) ->
                let head1 =
                  let uu___9 = FStarC_Syntax_Util.head_and_args t1 in
                  FStar_Pervasives_Native.fst uu___9 in
                let head2 =
                  let uu___9 = FStarC_Syntax_Util.head_and_args t2 in
                  FStar_Pervasives_Native.fst uu___9 in
                ((let uu___10 = FStarC_Compiler_Effect.op_Bang dbg_Rel in
                  if uu___10
                  then
                    let uu___11 =
                      let uu___12 =
                        FStarC_Class_Show.show FStarC_Class_Show.showable_int
                          problem.FStarC_TypeChecker_Common.pid in
                      let uu___13 =
                        let uu___14 =
                          FStarC_Class_Show.show
                            FStarC_Class_Show.showable_bool wl.smt_ok in
                        let uu___15 =
                          let uu___16 =
                            FStarC_Class_Show.show
                              FStarC_Syntax_Print.showable_term head1 in
                          let uu___17 =
                            let uu___18 =
                              let uu___19 =
                                FStarC_TypeChecker_Env.is_interpreted
                                  wl.tcenv head1 in
                              FStarC_Class_Show.show
                                FStarC_Class_Show.showable_bool uu___19 in
                            let uu___19 =
                              let uu___20 =
                                let uu___21 = no_free_uvars t1 in
                                FStarC_Class_Show.show
                                  FStarC_Class_Show.showable_bool uu___21 in
                              let uu___21 =
                                let uu___22 =
                                  FStarC_Class_Show.show
                                    FStarC_Syntax_Print.showable_term head2 in
                                let uu___23 =
                                  let uu___24 =
                                    let uu___25 =
                                      FStarC_TypeChecker_Env.is_interpreted
                                        wl.tcenv head2 in
                                    FStarC_Class_Show.show
                                      FStarC_Class_Show.showable_bool uu___25 in
                                  let uu___25 =
                                    let uu___26 =
                                      let uu___27 = no_free_uvars t2 in
                                      FStarC_Class_Show.show
                                        FStarC_Class_Show.showable_bool
                                        uu___27 in
                                    [uu___26] in
                                  uu___24 :: uu___25 in
                                uu___22 :: uu___23 in
                              uu___20 :: uu___21 in
                            uu___18 :: uu___19 in
                          uu___16 :: uu___17 in
                        uu___14 :: uu___15 in
                      uu___12 :: uu___13 in
                    FStarC_Compiler_Util.print
                      ">> (%s) (smtok=%s)\n>>> head1 = %s [interpreted=%s; no_free_uvars=%s]\n>>> head2 = %s [interpreted=%s; no_free_uvars=%s]\n"
                      uu___11
                  else ());
                 (let equal t11 t21 =
                    let env = p_env wl orig in
                    let r =
                      FStarC_TypeChecker_TermEqAndSimplify.eq_tm env t11 t21 in
                    match r with
                    | FStarC_TypeChecker_TermEqAndSimplify.Equal -> true
                    | FStarC_TypeChecker_TermEqAndSimplify.NotEqual -> false
                    | FStarC_TypeChecker_TermEqAndSimplify.Unknown ->
                        let steps =
                          [FStarC_TypeChecker_Env.UnfoldUntil
                             FStarC_Syntax_Syntax.delta_constant;
                          FStarC_TypeChecker_Env.Primops;
                          FStarC_TypeChecker_Env.Beta;
                          FStarC_TypeChecker_Env.Eager_unfolding;
                          FStarC_TypeChecker_Env.Iota] in
                        let t12 =
                          norm_with_steps
                            "FStarC.TypeChecker.Rel.norm_with_steps.2" steps
                            env t11 in
                        let t22 =
                          norm_with_steps
                            "FStarC.TypeChecker.Rel.norm_with_steps.3" steps
                            env t21 in
                        let uu___10 =
                          FStarC_TypeChecker_TermEqAndSimplify.eq_tm env t12
                            t22 in
                        uu___10 = FStarC_TypeChecker_TermEqAndSimplify.Equal in
                  let uu___10 =
                    ((FStarC_TypeChecker_Env.is_interpreted wl.tcenv head1)
                       ||
                       (FStarC_TypeChecker_Env.is_interpreted wl.tcenv head2))
                      &&
                      (problem.FStarC_TypeChecker_Common.relation =
                         FStarC_TypeChecker_Common.EQ) in
                  if uu___10
                  then
                    let solve_with_smt uu___11 =
                      let uu___12 =
                        let uu___13 = equal t1 t2 in
                        if uu___13
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu___15 = mk_eq2 wl orig t1 t2 in
                           match uu___15 with
                           | (g, wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1)) in
                      match uu___12 with
                      | (guard, wl1) ->
                          let uu___13 = solve_prob orig guard [] wl1 in
                          solve uu___13 in
                    let uu___11 = (no_free_uvars t1) && (no_free_uvars t2) in
                    (if uu___11
                     then
                       let uu___12 =
                         (Prims.op_Negation wl.smt_ok) ||
                           (FStarC_Options.ml_ish ()) in
                       (if uu___12
                        then
                          let uu___13 = equal t1 t2 in
                          (if uu___13
                           then
                             let uu___14 =
                               solve_prob orig FStar_Pervasives_Native.None
                                 [] wl in
                             solve uu___14
                           else
                             rigid_rigid_delta problem wl head1 head2 t1 t2)
                        else solve_with_smt ())
                     else
                       (let uu___13 =
                          (Prims.op_Negation wl.smt_ok) ||
                            (FStarC_Options.ml_ish ()) in
                        if uu___13
                        then rigid_rigid_delta problem wl head1 head2 t1 t2
                        else
                          try_solve_then_or_else wl
                            (fun wl_empty ->
                               rigid_rigid_delta problem wl_empty head1 head2
                                 t1 t2) (fun wl1 -> solve wl1)
                            (fun uu___15 -> solve_with_smt ())))
                  else rigid_rigid_delta problem wl head1 head2 t1 t2))
            | (uu___7, FStarC_Syntax_Syntax.Tm_name uu___8) ->
                let head1 =
                  let uu___9 = FStarC_Syntax_Util.head_and_args t1 in
                  FStar_Pervasives_Native.fst uu___9 in
                let head2 =
                  let uu___9 = FStarC_Syntax_Util.head_and_args t2 in
                  FStar_Pervasives_Native.fst uu___9 in
                ((let uu___10 = FStarC_Compiler_Effect.op_Bang dbg_Rel in
                  if uu___10
                  then
                    let uu___11 =
                      let uu___12 =
                        FStarC_Class_Show.show FStarC_Class_Show.showable_int
                          problem.FStarC_TypeChecker_Common.pid in
                      let uu___13 =
                        let uu___14 =
                          FStarC_Class_Show.show
                            FStarC_Class_Show.showable_bool wl.smt_ok in
                        let uu___15 =
                          let uu___16 =
                            FStarC_Class_Show.show
                              FStarC_Syntax_Print.showable_term head1 in
                          let uu___17 =
                            let uu___18 =
                              let uu___19 =
                                FStarC_TypeChecker_Env.is_interpreted
                                  wl.tcenv head1 in
                              FStarC_Class_Show.show
                                FStarC_Class_Show.showable_bool uu___19 in
                            let uu___19 =
                              let uu___20 =
                                let uu___21 = no_free_uvars t1 in
                                FStarC_Class_Show.show
                                  FStarC_Class_Show.showable_bool uu___21 in
                              let uu___21 =
                                let uu___22 =
                                  FStarC_Class_Show.show
                                    FStarC_Syntax_Print.showable_term head2 in
                                let uu___23 =
                                  let uu___24 =
                                    let uu___25 =
                                      FStarC_TypeChecker_Env.is_interpreted
                                        wl.tcenv head2 in
                                    FStarC_Class_Show.show
                                      FStarC_Class_Show.showable_bool uu___25 in
                                  let uu___25 =
                                    let uu___26 =
                                      let uu___27 = no_free_uvars t2 in
                                      FStarC_Class_Show.show
                                        FStarC_Class_Show.showable_bool
                                        uu___27 in
                                    [uu___26] in
                                  uu___24 :: uu___25 in
                                uu___22 :: uu___23 in
                              uu___20 :: uu___21 in
                            uu___18 :: uu___19 in
                          uu___16 :: uu___17 in
                        uu___14 :: uu___15 in
                      uu___12 :: uu___13 in
                    FStarC_Compiler_Util.print
                      ">> (%s) (smtok=%s)\n>>> head1 = %s [interpreted=%s; no_free_uvars=%s]\n>>> head2 = %s [interpreted=%s; no_free_uvars=%s]\n"
                      uu___11
                  else ());
                 (let equal t11 t21 =
                    let env = p_env wl orig in
                    let r =
                      FStarC_TypeChecker_TermEqAndSimplify.eq_tm env t11 t21 in
                    match r with
                    | FStarC_TypeChecker_TermEqAndSimplify.Equal -> true
                    | FStarC_TypeChecker_TermEqAndSimplify.NotEqual -> false
                    | FStarC_TypeChecker_TermEqAndSimplify.Unknown ->
                        let steps =
                          [FStarC_TypeChecker_Env.UnfoldUntil
                             FStarC_Syntax_Syntax.delta_constant;
                          FStarC_TypeChecker_Env.Primops;
                          FStarC_TypeChecker_Env.Beta;
                          FStarC_TypeChecker_Env.Eager_unfolding;
                          FStarC_TypeChecker_Env.Iota] in
                        let t12 =
                          norm_with_steps
                            "FStarC.TypeChecker.Rel.norm_with_steps.2" steps
                            env t11 in
                        let t22 =
                          norm_with_steps
                            "FStarC.TypeChecker.Rel.norm_with_steps.3" steps
                            env t21 in
                        let uu___10 =
                          FStarC_TypeChecker_TermEqAndSimplify.eq_tm env t12
                            t22 in
                        uu___10 = FStarC_TypeChecker_TermEqAndSimplify.Equal in
                  let uu___10 =
                    ((FStarC_TypeChecker_Env.is_interpreted wl.tcenv head1)
                       ||
                       (FStarC_TypeChecker_Env.is_interpreted wl.tcenv head2))
                      &&
                      (problem.FStarC_TypeChecker_Common.relation =
                         FStarC_TypeChecker_Common.EQ) in
                  if uu___10
                  then
                    let solve_with_smt uu___11 =
                      let uu___12 =
                        let uu___13 = equal t1 t2 in
                        if uu___13
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu___15 = mk_eq2 wl orig t1 t2 in
                           match uu___15 with
                           | (g, wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1)) in
                      match uu___12 with
                      | (guard, wl1) ->
                          let uu___13 = solve_prob orig guard [] wl1 in
                          solve uu___13 in
                    let uu___11 = (no_free_uvars t1) && (no_free_uvars t2) in
                    (if uu___11
                     then
                       let uu___12 =
                         (Prims.op_Negation wl.smt_ok) ||
                           (FStarC_Options.ml_ish ()) in
                       (if uu___12
                        then
                          let uu___13 = equal t1 t2 in
                          (if uu___13
                           then
                             let uu___14 =
                               solve_prob orig FStar_Pervasives_Native.None
                                 [] wl in
                             solve uu___14
                           else
                             rigid_rigid_delta problem wl head1 head2 t1 t2)
                        else solve_with_smt ())
                     else
                       (let uu___13 =
                          (Prims.op_Negation wl.smt_ok) ||
                            (FStarC_Options.ml_ish ()) in
                        if uu___13
                        then rigid_rigid_delta problem wl head1 head2 t1 t2
                        else
                          try_solve_then_or_else wl
                            (fun wl_empty ->
                               rigid_rigid_delta problem wl_empty head1 head2
                                 t1 t2) (fun wl1 -> solve wl1)
                            (fun uu___15 -> solve_with_smt ())))
                  else rigid_rigid_delta problem wl head1 head2 t1 t2))
            | (uu___7, FStarC_Syntax_Syntax.Tm_constant uu___8) ->
                let head1 =
                  let uu___9 = FStarC_Syntax_Util.head_and_args t1 in
                  FStar_Pervasives_Native.fst uu___9 in
                let head2 =
                  let uu___9 = FStarC_Syntax_Util.head_and_args t2 in
                  FStar_Pervasives_Native.fst uu___9 in
                ((let uu___10 = FStarC_Compiler_Effect.op_Bang dbg_Rel in
                  if uu___10
                  then
                    let uu___11 =
                      let uu___12 =
                        FStarC_Class_Show.show FStarC_Class_Show.showable_int
                          problem.FStarC_TypeChecker_Common.pid in
                      let uu___13 =
                        let uu___14 =
                          FStarC_Class_Show.show
                            FStarC_Class_Show.showable_bool wl.smt_ok in
                        let uu___15 =
                          let uu___16 =
                            FStarC_Class_Show.show
                              FStarC_Syntax_Print.showable_term head1 in
                          let uu___17 =
                            let uu___18 =
                              let uu___19 =
                                FStarC_TypeChecker_Env.is_interpreted
                                  wl.tcenv head1 in
                              FStarC_Class_Show.show
                                FStarC_Class_Show.showable_bool uu___19 in
                            let uu___19 =
                              let uu___20 =
                                let uu___21 = no_free_uvars t1 in
                                FStarC_Class_Show.show
                                  FStarC_Class_Show.showable_bool uu___21 in
                              let uu___21 =
                                let uu___22 =
                                  FStarC_Class_Show.show
                                    FStarC_Syntax_Print.showable_term head2 in
                                let uu___23 =
                                  let uu___24 =
                                    let uu___25 =
                                      FStarC_TypeChecker_Env.is_interpreted
                                        wl.tcenv head2 in
                                    FStarC_Class_Show.show
                                      FStarC_Class_Show.showable_bool uu___25 in
                                  let uu___25 =
                                    let uu___26 =
                                      let uu___27 = no_free_uvars t2 in
                                      FStarC_Class_Show.show
                                        FStarC_Class_Show.showable_bool
                                        uu___27 in
                                    [uu___26] in
                                  uu___24 :: uu___25 in
                                uu___22 :: uu___23 in
                              uu___20 :: uu___21 in
                            uu___18 :: uu___19 in
                          uu___16 :: uu___17 in
                        uu___14 :: uu___15 in
                      uu___12 :: uu___13 in
                    FStarC_Compiler_Util.print
                      ">> (%s) (smtok=%s)\n>>> head1 = %s [interpreted=%s; no_free_uvars=%s]\n>>> head2 = %s [interpreted=%s; no_free_uvars=%s]\n"
                      uu___11
                  else ());
                 (let equal t11 t21 =
                    let env = p_env wl orig in
                    let r =
                      FStarC_TypeChecker_TermEqAndSimplify.eq_tm env t11 t21 in
                    match r with
                    | FStarC_TypeChecker_TermEqAndSimplify.Equal -> true
                    | FStarC_TypeChecker_TermEqAndSimplify.NotEqual -> false
                    | FStarC_TypeChecker_TermEqAndSimplify.Unknown ->
                        let steps =
                          [FStarC_TypeChecker_Env.UnfoldUntil
                             FStarC_Syntax_Syntax.delta_constant;
                          FStarC_TypeChecker_Env.Primops;
                          FStarC_TypeChecker_Env.Beta;
                          FStarC_TypeChecker_Env.Eager_unfolding;
                          FStarC_TypeChecker_Env.Iota] in
                        let t12 =
                          norm_with_steps
                            "FStarC.TypeChecker.Rel.norm_with_steps.2" steps
                            env t11 in
                        let t22 =
                          norm_with_steps
                            "FStarC.TypeChecker.Rel.norm_with_steps.3" steps
                            env t21 in
                        let uu___10 =
                          FStarC_TypeChecker_TermEqAndSimplify.eq_tm env t12
                            t22 in
                        uu___10 = FStarC_TypeChecker_TermEqAndSimplify.Equal in
                  let uu___10 =
                    ((FStarC_TypeChecker_Env.is_interpreted wl.tcenv head1)
                       ||
                       (FStarC_TypeChecker_Env.is_interpreted wl.tcenv head2))
                      &&
                      (problem.FStarC_TypeChecker_Common.relation =
                         FStarC_TypeChecker_Common.EQ) in
                  if uu___10
                  then
                    let solve_with_smt uu___11 =
                      let uu___12 =
                        let uu___13 = equal t1 t2 in
                        if uu___13
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu___15 = mk_eq2 wl orig t1 t2 in
                           match uu___15 with
                           | (g, wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1)) in
                      match uu___12 with
                      | (guard, wl1) ->
                          let uu___13 = solve_prob orig guard [] wl1 in
                          solve uu___13 in
                    let uu___11 = (no_free_uvars t1) && (no_free_uvars t2) in
                    (if uu___11
                     then
                       let uu___12 =
                         (Prims.op_Negation wl.smt_ok) ||
                           (FStarC_Options.ml_ish ()) in
                       (if uu___12
                        then
                          let uu___13 = equal t1 t2 in
                          (if uu___13
                           then
                             let uu___14 =
                               solve_prob orig FStar_Pervasives_Native.None
                                 [] wl in
                             solve uu___14
                           else
                             rigid_rigid_delta problem wl head1 head2 t1 t2)
                        else solve_with_smt ())
                     else
                       (let uu___13 =
                          (Prims.op_Negation wl.smt_ok) ||
                            (FStarC_Options.ml_ish ()) in
                        if uu___13
                        then rigid_rigid_delta problem wl head1 head2 t1 t2
                        else
                          try_solve_then_or_else wl
                            (fun wl_empty ->
                               rigid_rigid_delta problem wl_empty head1 head2
                                 t1 t2) (fun wl1 -> solve wl1)
                            (fun uu___15 -> solve_with_smt ())))
                  else rigid_rigid_delta problem wl head1 head2 t1 t2))
            | (uu___7, FStarC_Syntax_Syntax.Tm_fvar uu___8) ->
                let head1 =
                  let uu___9 = FStarC_Syntax_Util.head_and_args t1 in
                  FStar_Pervasives_Native.fst uu___9 in
                let head2 =
                  let uu___9 = FStarC_Syntax_Util.head_and_args t2 in
                  FStar_Pervasives_Native.fst uu___9 in
                ((let uu___10 = FStarC_Compiler_Effect.op_Bang dbg_Rel in
                  if uu___10
                  then
                    let uu___11 =
                      let uu___12 =
                        FStarC_Class_Show.show FStarC_Class_Show.showable_int
                          problem.FStarC_TypeChecker_Common.pid in
                      let uu___13 =
                        let uu___14 =
                          FStarC_Class_Show.show
                            FStarC_Class_Show.showable_bool wl.smt_ok in
                        let uu___15 =
                          let uu___16 =
                            FStarC_Class_Show.show
                              FStarC_Syntax_Print.showable_term head1 in
                          let uu___17 =
                            let uu___18 =
                              let uu___19 =
                                FStarC_TypeChecker_Env.is_interpreted
                                  wl.tcenv head1 in
                              FStarC_Class_Show.show
                                FStarC_Class_Show.showable_bool uu___19 in
                            let uu___19 =
                              let uu___20 =
                                let uu___21 = no_free_uvars t1 in
                                FStarC_Class_Show.show
                                  FStarC_Class_Show.showable_bool uu___21 in
                              let uu___21 =
                                let uu___22 =
                                  FStarC_Class_Show.show
                                    FStarC_Syntax_Print.showable_term head2 in
                                let uu___23 =
                                  let uu___24 =
                                    let uu___25 =
                                      FStarC_TypeChecker_Env.is_interpreted
                                        wl.tcenv head2 in
                                    FStarC_Class_Show.show
                                      FStarC_Class_Show.showable_bool uu___25 in
                                  let uu___25 =
                                    let uu___26 =
                                      let uu___27 = no_free_uvars t2 in
                                      FStarC_Class_Show.show
                                        FStarC_Class_Show.showable_bool
                                        uu___27 in
                                    [uu___26] in
                                  uu___24 :: uu___25 in
                                uu___22 :: uu___23 in
                              uu___20 :: uu___21 in
                            uu___18 :: uu___19 in
                          uu___16 :: uu___17 in
                        uu___14 :: uu___15 in
                      uu___12 :: uu___13 in
                    FStarC_Compiler_Util.print
                      ">> (%s) (smtok=%s)\n>>> head1 = %s [interpreted=%s; no_free_uvars=%s]\n>>> head2 = %s [interpreted=%s; no_free_uvars=%s]\n"
                      uu___11
                  else ());
                 (let equal t11 t21 =
                    let env = p_env wl orig in
                    let r =
                      FStarC_TypeChecker_TermEqAndSimplify.eq_tm env t11 t21 in
                    match r with
                    | FStarC_TypeChecker_TermEqAndSimplify.Equal -> true
                    | FStarC_TypeChecker_TermEqAndSimplify.NotEqual -> false
                    | FStarC_TypeChecker_TermEqAndSimplify.Unknown ->
                        let steps =
                          [FStarC_TypeChecker_Env.UnfoldUntil
                             FStarC_Syntax_Syntax.delta_constant;
                          FStarC_TypeChecker_Env.Primops;
                          FStarC_TypeChecker_Env.Beta;
                          FStarC_TypeChecker_Env.Eager_unfolding;
                          FStarC_TypeChecker_Env.Iota] in
                        let t12 =
                          norm_with_steps
                            "FStarC.TypeChecker.Rel.norm_with_steps.2" steps
                            env t11 in
                        let t22 =
                          norm_with_steps
                            "FStarC.TypeChecker.Rel.norm_with_steps.3" steps
                            env t21 in
                        let uu___10 =
                          FStarC_TypeChecker_TermEqAndSimplify.eq_tm env t12
                            t22 in
                        uu___10 = FStarC_TypeChecker_TermEqAndSimplify.Equal in
                  let uu___10 =
                    ((FStarC_TypeChecker_Env.is_interpreted wl.tcenv head1)
                       ||
                       (FStarC_TypeChecker_Env.is_interpreted wl.tcenv head2))
                      &&
                      (problem.FStarC_TypeChecker_Common.relation =
                         FStarC_TypeChecker_Common.EQ) in
                  if uu___10
                  then
                    let solve_with_smt uu___11 =
                      let uu___12 =
                        let uu___13 = equal t1 t2 in
                        if uu___13
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu___15 = mk_eq2 wl orig t1 t2 in
                           match uu___15 with
                           | (g, wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1)) in
                      match uu___12 with
                      | (guard, wl1) ->
                          let uu___13 = solve_prob orig guard [] wl1 in
                          solve uu___13 in
                    let uu___11 = (no_free_uvars t1) && (no_free_uvars t2) in
                    (if uu___11
                     then
                       let uu___12 =
                         (Prims.op_Negation wl.smt_ok) ||
                           (FStarC_Options.ml_ish ()) in
                       (if uu___12
                        then
                          let uu___13 = equal t1 t2 in
                          (if uu___13
                           then
                             let uu___14 =
                               solve_prob orig FStar_Pervasives_Native.None
                                 [] wl in
                             solve uu___14
                           else
                             rigid_rigid_delta problem wl head1 head2 t1 t2)
                        else solve_with_smt ())
                     else
                       (let uu___13 =
                          (Prims.op_Negation wl.smt_ok) ||
                            (FStarC_Options.ml_ish ()) in
                        if uu___13
                        then rigid_rigid_delta problem wl head1 head2 t1 t2
                        else
                          try_solve_then_or_else wl
                            (fun wl_empty ->
                               rigid_rigid_delta problem wl_empty head1 head2
                                 t1 t2) (fun wl1 -> solve wl1)
                            (fun uu___15 -> solve_with_smt ())))
                  else rigid_rigid_delta problem wl head1 head2 t1 t2))
            | (uu___7, FStarC_Syntax_Syntax.Tm_app uu___8) ->
                let head1 =
                  let uu___9 = FStarC_Syntax_Util.head_and_args t1 in
                  FStar_Pervasives_Native.fst uu___9 in
                let head2 =
                  let uu___9 = FStarC_Syntax_Util.head_and_args t2 in
                  FStar_Pervasives_Native.fst uu___9 in
                ((let uu___10 = FStarC_Compiler_Effect.op_Bang dbg_Rel in
                  if uu___10
                  then
                    let uu___11 =
                      let uu___12 =
                        FStarC_Class_Show.show FStarC_Class_Show.showable_int
                          problem.FStarC_TypeChecker_Common.pid in
                      let uu___13 =
                        let uu___14 =
                          FStarC_Class_Show.show
                            FStarC_Class_Show.showable_bool wl.smt_ok in
                        let uu___15 =
                          let uu___16 =
                            FStarC_Class_Show.show
                              FStarC_Syntax_Print.showable_term head1 in
                          let uu___17 =
                            let uu___18 =
                              let uu___19 =
                                FStarC_TypeChecker_Env.is_interpreted
                                  wl.tcenv head1 in
                              FStarC_Class_Show.show
                                FStarC_Class_Show.showable_bool uu___19 in
                            let uu___19 =
                              let uu___20 =
                                let uu___21 = no_free_uvars t1 in
                                FStarC_Class_Show.show
                                  FStarC_Class_Show.showable_bool uu___21 in
                              let uu___21 =
                                let uu___22 =
                                  FStarC_Class_Show.show
                                    FStarC_Syntax_Print.showable_term head2 in
                                let uu___23 =
                                  let uu___24 =
                                    let uu___25 =
                                      FStarC_TypeChecker_Env.is_interpreted
                                        wl.tcenv head2 in
                                    FStarC_Class_Show.show
                                      FStarC_Class_Show.showable_bool uu___25 in
                                  let uu___25 =
                                    let uu___26 =
                                      let uu___27 = no_free_uvars t2 in
                                      FStarC_Class_Show.show
                                        FStarC_Class_Show.showable_bool
                                        uu___27 in
                                    [uu___26] in
                                  uu___24 :: uu___25 in
                                uu___22 :: uu___23 in
                              uu___20 :: uu___21 in
                            uu___18 :: uu___19 in
                          uu___16 :: uu___17 in
                        uu___14 :: uu___15 in
                      uu___12 :: uu___13 in
                    FStarC_Compiler_Util.print
                      ">> (%s) (smtok=%s)\n>>> head1 = %s [interpreted=%s; no_free_uvars=%s]\n>>> head2 = %s [interpreted=%s; no_free_uvars=%s]\n"
                      uu___11
                  else ());
                 (let equal t11 t21 =
                    let env = p_env wl orig in
                    let r =
                      FStarC_TypeChecker_TermEqAndSimplify.eq_tm env t11 t21 in
                    match r with
                    | FStarC_TypeChecker_TermEqAndSimplify.Equal -> true
                    | FStarC_TypeChecker_TermEqAndSimplify.NotEqual -> false
                    | FStarC_TypeChecker_TermEqAndSimplify.Unknown ->
                        let steps =
                          [FStarC_TypeChecker_Env.UnfoldUntil
                             FStarC_Syntax_Syntax.delta_constant;
                          FStarC_TypeChecker_Env.Primops;
                          FStarC_TypeChecker_Env.Beta;
                          FStarC_TypeChecker_Env.Eager_unfolding;
                          FStarC_TypeChecker_Env.Iota] in
                        let t12 =
                          norm_with_steps
                            "FStarC.TypeChecker.Rel.norm_with_steps.2" steps
                            env t11 in
                        let t22 =
                          norm_with_steps
                            "FStarC.TypeChecker.Rel.norm_with_steps.3" steps
                            env t21 in
                        let uu___10 =
                          FStarC_TypeChecker_TermEqAndSimplify.eq_tm env t12
                            t22 in
                        uu___10 = FStarC_TypeChecker_TermEqAndSimplify.Equal in
                  let uu___10 =
                    ((FStarC_TypeChecker_Env.is_interpreted wl.tcenv head1)
                       ||
                       (FStarC_TypeChecker_Env.is_interpreted wl.tcenv head2))
                      &&
                      (problem.FStarC_TypeChecker_Common.relation =
                         FStarC_TypeChecker_Common.EQ) in
                  if uu___10
                  then
                    let solve_with_smt uu___11 =
                      let uu___12 =
                        let uu___13 = equal t1 t2 in
                        if uu___13
                        then (FStar_Pervasives_Native.None, wl)
                        else
                          (let uu___15 = mk_eq2 wl orig t1 t2 in
                           match uu___15 with
                           | (g, wl1) ->
                               ((FStar_Pervasives_Native.Some g), wl1)) in
                      match uu___12 with
                      | (guard, wl1) ->
                          let uu___13 = solve_prob orig guard [] wl1 in
                          solve uu___13 in
                    let uu___11 = (no_free_uvars t1) && (no_free_uvars t2) in
                    (if uu___11
                     then
                       let uu___12 =
                         (Prims.op_Negation wl.smt_ok) ||
                           (FStarC_Options.ml_ish ()) in
                       (if uu___12
                        then
                          let uu___13 = equal t1 t2 in
                          (if uu___13
                           then
                             let uu___14 =
                               solve_prob orig FStar_Pervasives_Native.None
                                 [] wl in
                             solve uu___14
                           else
                             rigid_rigid_delta problem wl head1 head2 t1 t2)
                        else solve_with_smt ())
                     else
                       (let uu___13 =
                          (Prims.op_Negation wl.smt_ok) ||
                            (FStarC_Options.ml_ish ()) in
                        if uu___13
                        then rigid_rigid_delta problem wl head1 head2 t1 t2
                        else
                          try_solve_then_or_else wl
                            (fun wl_empty ->
                               rigid_rigid_delta problem wl_empty head1 head2
                                 t1 t2) (fun wl1 -> solve wl1)
                            (fun uu___15 -> solve_with_smt ())))
                  else rigid_rigid_delta problem wl head1 head2 t1 t2))
            | (FStarC_Syntax_Syntax.Tm_let uu___7,
               FStarC_Syntax_Syntax.Tm_let uu___8) ->
                let uu___9 = FStarC_Syntax_Util.term_eq t1 t2 in
                if uu___9
                then
                  let uu___10 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl in
                  solve uu___10
                else
                  (let uu___11 = FStarC_Thunk.mkv "Tm_let mismatch" in
                   giveup wl uu___11 orig)
            | (FStarC_Syntax_Syntax.Tm_let uu___7, uu___8) ->
                let uu___9 =
                  let uu___10 =
                    FStarC_Class_Tagged.tag_of
                      FStarC_Syntax_Syntax.tagged_term t1 in
                  let uu___11 =
                    FStarC_Class_Tagged.tag_of
                      FStarC_Syntax_Syntax.tagged_term t2 in
                  let uu___12 =
                    FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                      t1 in
                  let uu___13 =
                    FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                      t2 in
                  FStarC_Compiler_Util.format4
                    "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                    uu___10 uu___11 uu___12 uu___13 in
                FStarC_Errors.raise_error
                  (FStarC_Syntax_Syntax.has_range_syntax ()) t1
                  FStarC_Errors_Codes.Fatal_UnificationNotWellFormed ()
                  (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                  (Obj.magic uu___9)
            | (uu___7, FStarC_Syntax_Syntax.Tm_let uu___8) ->
                let uu___9 =
                  let uu___10 =
                    FStarC_Class_Tagged.tag_of
                      FStarC_Syntax_Syntax.tagged_term t1 in
                  let uu___11 =
                    FStarC_Class_Tagged.tag_of
                      FStarC_Syntax_Syntax.tagged_term t2 in
                  let uu___12 =
                    FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                      t1 in
                  let uu___13 =
                    FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                      t2 in
                  FStarC_Compiler_Util.format4
                    "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                    uu___10 uu___11 uu___12 uu___13 in
                FStarC_Errors.raise_error
                  (FStarC_Syntax_Syntax.has_range_syntax ()) t1
                  FStarC_Errors_Codes.Fatal_UnificationNotWellFormed ()
                  (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                  (Obj.magic uu___9)
            | (FStarC_Syntax_Syntax.Tm_lazy li1, FStarC_Syntax_Syntax.Tm_lazy
               li2) when
                (FStarC_Class_Deq.op_Equals_Question
                   FStarC_Syntax_Syntax.deq_lazy_kind
                   li1.FStarC_Syntax_Syntax.lkind
                   li2.FStarC_Syntax_Syntax.lkind)
                  && (lazy_complete_repr li1.FStarC_Syntax_Syntax.lkind)
                ->
                let uu___7 =
                  let uu___8 = FStarC_Syntax_Util.unfold_lazy li1 in
                  let uu___9 = FStarC_Syntax_Util.unfold_lazy li2 in
                  {
                    FStarC_TypeChecker_Common.pid =
                      (problem.FStarC_TypeChecker_Common.pid);
                    FStarC_TypeChecker_Common.lhs = uu___8;
                    FStarC_TypeChecker_Common.relation =
                      (problem.FStarC_TypeChecker_Common.relation);
                    FStarC_TypeChecker_Common.rhs = uu___9;
                    FStarC_TypeChecker_Common.element =
                      (problem.FStarC_TypeChecker_Common.element);
                    FStarC_TypeChecker_Common.logical_guard =
                      (problem.FStarC_TypeChecker_Common.logical_guard);
                    FStarC_TypeChecker_Common.logical_guard_uvar =
                      (problem.FStarC_TypeChecker_Common.logical_guard_uvar);
                    FStarC_TypeChecker_Common.reason =
                      (problem.FStarC_TypeChecker_Common.reason);
                    FStarC_TypeChecker_Common.loc =
                      (problem.FStarC_TypeChecker_Common.loc);
                    FStarC_TypeChecker_Common.rank =
                      (problem.FStarC_TypeChecker_Common.rank);
                    FStarC_TypeChecker_Common.logical =
                      (problem.FStarC_TypeChecker_Common.logical)
                  } in
                solve_t' uu___7 wl
            | uu___7 ->
                let uu___8 =
                  FStarC_Thunk.mk
                    (fun uu___9 ->
                       let uu___10 =
                         let uu___11 =
                           FStarC_Class_Tagged.tag_of
                             FStarC_Syntax_Syntax.tagged_term t1 in
                         let uu___12 =
                           let uu___13 =
                             FStarC_Class_Tagged.tag_of
                               FStarC_Syntax_Syntax.tagged_term t2 in
                           Prims.strcat " vs " uu___13 in
                         Prims.strcat uu___11 uu___12 in
                       Prims.strcat "head tag mismatch: " uu___10) in
                giveup wl uu___8 orig))))
and (solve_c :
  FStarC_Syntax_Syntax.comp FStarC_TypeChecker_Common.problem ->
    worklist -> solution)
  =
  fun problem ->
    fun wl ->
      let c1 = problem.FStarC_TypeChecker_Common.lhs in
      let c2 = problem.FStarC_TypeChecker_Common.rhs in
      let orig = FStarC_TypeChecker_Common.CProb problem in
      let env = p_env wl orig in
      let sub_prob wl1 t1 rel t2 reason =
        mk_t_problem wl1 [] orig t1 rel t2 FStar_Pervasives_Native.None
          reason in
      let solve_eq c1_comp c2_comp g_lift =
        (let uu___1 = FStarC_Compiler_Effect.op_Bang dbg_EQ in
         if uu___1
         then
           let uu___2 =
             let uu___3 = FStarC_Syntax_Syntax.mk_Comp c1_comp in
             FStarC_Class_Show.show FStarC_Syntax_Print.showable_comp uu___3 in
           let uu___3 =
             let uu___4 = FStarC_Syntax_Syntax.mk_Comp c2_comp in
             FStarC_Class_Show.show FStarC_Syntax_Print.showable_comp uu___4 in
           FStarC_Compiler_Util.print2
             "solve_c is using an equality constraint (%s vs %s)\n" uu___2
             uu___3
         else ());
        (let uu___1 =
           let uu___2 =
             FStarC_Ident.lid_equals c1_comp.FStarC_Syntax_Syntax.effect_name
               c2_comp.FStarC_Syntax_Syntax.effect_name in
           Prims.op_Negation uu___2 in
         if uu___1
         then
           let uu___2 =
             mklstr
               (fun uu___3 ->
                  let uu___4 =
                    FStarC_Class_Show.show FStarC_Ident.showable_lident
                      c1_comp.FStarC_Syntax_Syntax.effect_name in
                  let uu___5 =
                    FStarC_Class_Show.show FStarC_Ident.showable_lident
                      c2_comp.FStarC_Syntax_Syntax.effect_name in
                  FStarC_Compiler_Util.format2
                    "incompatible effects: %s <> %s" uu___4 uu___5) in
           giveup wl uu___2 orig
         else
           if
             (FStarC_Compiler_List.length
                c1_comp.FStarC_Syntax_Syntax.effect_args)
               <>
               (FStarC_Compiler_List.length
                  c2_comp.FStarC_Syntax_Syntax.effect_args)
           then
             (let uu___3 =
                mklstr
                  (fun uu___4 ->
                     let uu___5 =
                       FStarC_Class_Show.show
                         (FStarC_Class_Show.show_list
                            (FStarC_Class_Show.show_tuple2
                               FStarC_Syntax_Print.showable_term
                               FStarC_Syntax_Print.showable_aqual))
                         c1_comp.FStarC_Syntax_Syntax.effect_args in
                     let uu___6 =
                       FStarC_Class_Show.show
                         (FStarC_Class_Show.show_list
                            (FStarC_Class_Show.show_tuple2
                               FStarC_Syntax_Print.showable_term
                               FStarC_Syntax_Print.showable_aqual))
                         c2_comp.FStarC_Syntax_Syntax.effect_args in
                     FStarC_Compiler_Util.format2
                       "incompatible effect arguments: %s <> %s" uu___5
                       uu___6) in
              giveup wl uu___3 orig)
           else
             (let uu___4 =
                FStarC_Compiler_List.fold_left2
                  (fun uu___5 ->
                     fun u1 ->
                       fun u2 ->
                         match uu___5 with
                         | (univ_sub_probs, wl1) ->
                             let uu___6 =
                               let uu___7 =
                                 FStarC_Syntax_Syntax.mk
                                   (FStarC_Syntax_Syntax.Tm_type u1)
                                   FStarC_Compiler_Range_Type.dummyRange in
                               let uu___8 =
                                 FStarC_Syntax_Syntax.mk
                                   (FStarC_Syntax_Syntax.Tm_type u2)
                                   FStarC_Compiler_Range_Type.dummyRange in
                               sub_prob wl1 uu___7
                                 FStarC_TypeChecker_Common.EQ uu___8
                                 "effect universes" in
                             (match uu___6 with
                              | (p, wl2) ->
                                  let uu___7 =
                                    let uu___8 =
                                      Obj.magic
                                        (FStarC_Class_Listlike.cons ()
                                           (Obj.magic
                                              (FStarC_Compiler_CList.listlike_clist
                                                 ())) p
                                           (FStarC_Class_Listlike.empty ()
                                              (Obj.magic
                                                 (FStarC_Compiler_CList.listlike_clist
                                                    ())))) in
                                    FStarC_Class_Monoid.op_Plus_Plus
                                      (FStarC_Compiler_CList.monoid_clist ())
                                      univ_sub_probs uu___8 in
                                  (uu___7, wl2)))
                  ((Obj.magic
                      (FStarC_Class_Listlike.empty ()
                         (Obj.magic (FStarC_Compiler_CList.listlike_clist ())))),
                    wl) c1_comp.FStarC_Syntax_Syntax.comp_univs
                  c2_comp.FStarC_Syntax_Syntax.comp_univs in
              match uu___4 with
              | (univ_sub_probs, wl1) ->
                  let uu___5 =
                    sub_prob wl1 c1_comp.FStarC_Syntax_Syntax.result_typ
                      FStarC_TypeChecker_Common.EQ
                      c2_comp.FStarC_Syntax_Syntax.result_typ
                      "effect ret type" in
                  (match uu___5 with
                   | (ret_sub_prob, wl2) ->
                       let uu___6 =
                         FStarC_Compiler_List.fold_right2
                           (fun uu___7 ->
                              fun uu___8 ->
                                fun uu___9 ->
                                  match (uu___7, uu___8, uu___9) with
                                  | ((a1, uu___10), (a2, uu___11),
                                     (arg_sub_probs, wl3)) ->
                                      let uu___12 =
                                        sub_prob wl3 a1
                                          FStarC_TypeChecker_Common.EQ a2
                                          "effect arg" in
                                      (match uu___12 with
                                       | (p, wl4) ->
                                           let uu___13 =
                                             Obj.magic
                                               (FStarC_Class_Listlike.cons ()
                                                  (Obj.magic
                                                     (FStarC_Compiler_CList.listlike_clist
                                                        ())) p
                                                  (Obj.magic arg_sub_probs)) in
                                           (uu___13, wl4)))
                           c1_comp.FStarC_Syntax_Syntax.effect_args
                           c2_comp.FStarC_Syntax_Syntax.effect_args
                           ((Obj.magic
                               (FStarC_Class_Listlike.empty ()
                                  (Obj.magic
                                     (FStarC_Compiler_CList.listlike_clist ())))),
                             wl2) in
                       (match uu___6 with
                        | (arg_sub_probs, wl3) ->
                            let sub_probs =
                              let uu___7 =
                                let uu___8 =
                                  let uu___9 =
                                    FStarC_Compiler_CList.map
                                      (fun uu___10 ->
                                         match uu___10 with
                                         | (uu___11, uu___12, p) -> p)
                                      g_lift.FStarC_TypeChecker_Common.deferred in
                                  FStarC_Class_Monoid.op_Plus_Plus
                                    (FStarC_Compiler_CList.monoid_clist ())
                                    arg_sub_probs uu___9 in
                                Obj.magic
                                  (FStarC_Class_Listlike.cons ()
                                     (Obj.magic
                                        (FStarC_Compiler_CList.listlike_clist
                                           ())) ret_sub_prob
                                     (Obj.magic uu___8)) in
                              FStarC_Class_Monoid.op_Plus_Plus
                                (FStarC_Compiler_CList.monoid_clist ())
                                univ_sub_probs uu___7 in
                            let sub_probs1 =
                              FStarC_Class_Listlike.to_list
                                (FStarC_Compiler_CList.listlike_clist ())
                                sub_probs in
                            let guard =
                              let guard1 =
                                let uu___7 =
                                  FStarC_Compiler_List.map p_guard sub_probs1 in
                                FStarC_Syntax_Util.mk_conj_l uu___7 in
                              match g_lift.FStarC_TypeChecker_Common.guard_f
                              with
                              | FStarC_TypeChecker_Common.Trivial -> guard1
                              | FStarC_TypeChecker_Common.NonTrivial f ->
                                  FStarC_Syntax_Util.mk_conj guard1 f in
                            let wl4 =
                              let uu___7 =
                                FStarC_Class_Monoid.op_Plus_Plus
                                  (FStarC_Compiler_CList.monoid_clist ())
                                  g_lift.FStarC_TypeChecker_Common.implicits
                                  wl3.wl_implicits in
                              {
                                attempting = (wl3.attempting);
                                wl_deferred = (wl3.wl_deferred);
                                wl_deferred_to_tac = (wl3.wl_deferred_to_tac);
                                ctr = (wl3.ctr);
                                defer_ok = (wl3.defer_ok);
                                smt_ok = (wl3.smt_ok);
                                umax_heuristic_ok = (wl3.umax_heuristic_ok);
                                tcenv = (wl3.tcenv);
                                wl_implicits = uu___7;
                                repr_subcomp_allowed =
                                  (wl3.repr_subcomp_allowed);
                                typeclass_variables =
                                  (wl3.typeclass_variables)
                              } in
                            let wl5 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl4 in
                            let uu___7 = attempt sub_probs1 wl5 in
                            solve uu___7)))) in
      let should_fail_since_repr_subcomp_not_allowed repr_subcomp_allowed c11
        c21 =
        let uu___ =
          let uu___1 = FStarC_TypeChecker_Env.norm_eff_name wl.tcenv c11 in
          let uu___2 = FStarC_TypeChecker_Env.norm_eff_name wl.tcenv c21 in
          (uu___1, uu___2) in
        match uu___ with
        | (c12, c22) ->
            ((Prims.op_Negation wl.repr_subcomp_allowed) &&
               (let uu___1 = FStarC_Ident.lid_equals c12 c22 in
                Prims.op_Negation uu___1))
              && (FStarC_TypeChecker_Env.is_reifiable_effect wl.tcenv c22) in
      let solve_layered_sub c11 c21 =
        (let uu___1 = FStarC_Compiler_Effect.op_Bang dbg_LayeredEffectsApp in
         if uu___1
         then
           let uu___2 =
             let uu___3 = FStarC_Syntax_Syntax.mk_Comp c11 in
             FStarC_Class_Show.show FStarC_Syntax_Print.showable_comp uu___3 in
           let uu___3 =
             let uu___4 = FStarC_Syntax_Syntax.mk_Comp c21 in
             FStarC_Class_Show.show FStarC_Syntax_Print.showable_comp uu___4 in
           FStarC_Compiler_Util.print2
             "solve_layered_sub c1: %s and c2: %s {\n" uu___2 uu___3
         else ());
        if
          problem.FStarC_TypeChecker_Common.relation =
            FStarC_TypeChecker_Common.EQ
        then solve_eq c11 c21 FStarC_TypeChecker_Env.trivial_guard
        else
          (let r = FStarC_TypeChecker_Env.get_range wl.tcenv in
           let uu___2 =
             should_fail_since_repr_subcomp_not_allowed
               wl.repr_subcomp_allowed c11.FStarC_Syntax_Syntax.effect_name
               c21.FStarC_Syntax_Syntax.effect_name in
           if uu___2
           then
             let uu___3 =
               mklstr
                 (fun uu___4 ->
                    let uu___5 =
                      FStarC_Ident.string_of_lid
                        c11.FStarC_Syntax_Syntax.effect_name in
                    let uu___6 =
                      FStarC_Ident.string_of_lid
                        c21.FStarC_Syntax_Syntax.effect_name in
                    FStarC_Compiler_Util.format2
                      "Cannot lift from %s to %s, it needs a lift\n" uu___5
                      uu___6) in
             giveup wl uu___3 orig
           else
             (let subcomp_name =
                let uu___4 =
                  let uu___5 =
                    FStarC_Ident.ident_of_lid
                      c11.FStarC_Syntax_Syntax.effect_name in
                  FStarC_Ident.string_of_id uu___5 in
                let uu___5 =
                  let uu___6 =
                    FStarC_Ident.ident_of_lid
                      c21.FStarC_Syntax_Syntax.effect_name in
                  FStarC_Ident.string_of_id uu___6 in
                FStarC_Compiler_Util.format2 "%s <: %s" uu___4 uu___5 in
              let lift_c1 edge =
                let uu___4 =
                  let uu___5 = FStarC_Syntax_Syntax.mk_Comp c11 in
                  (edge.FStarC_TypeChecker_Env.mlift).FStarC_TypeChecker_Env.mlift_wp
                    env uu___5 in
                match uu___4 with
                | (c, g) ->
                    let uu___5 =
                      FStarC_TypeChecker_Env.comp_to_comp_typ env c in
                    (uu___5, g) in
              let uu___4 =
                let uu___5 =
                  FStarC_TypeChecker_Env.exists_polymonadic_subcomp env
                    c11.FStarC_Syntax_Syntax.effect_name
                    c21.FStarC_Syntax_Syntax.effect_name in
                match uu___5 with
                | FStar_Pervasives_Native.None ->
                    let uu___6 =
                      FStarC_TypeChecker_Env.monad_leq env
                        c11.FStarC_Syntax_Syntax.effect_name
                        c21.FStarC_Syntax_Syntax.effect_name in
                    (match uu___6 with
                     | FStar_Pervasives_Native.None ->
                         (c11, FStarC_TypeChecker_Env.trivial_guard,
                           FStar_Pervasives_Native.None,
                           FStarC_Syntax_Syntax.Ad_hoc_combinator,
                           Prims.int_zero, false)
                     | FStar_Pervasives_Native.Some edge ->
                         let uu___7 = lift_c1 edge in
                         (match uu___7 with
                          | (c12, g_lift) ->
                              let ed2 =
                                FStarC_TypeChecker_Env.get_effect_decl env
                                  c21.FStarC_Syntax_Syntax.effect_name in
                              let uu___8 =
                                let uu___9 =
                                  FStarC_Syntax_Util.get_stronger_vc_combinator
                                    ed2 in
                                match uu___9 with
                                | (ts, kopt) ->
                                    let uu___10 =
                                      let uu___11 =
                                        let uu___12 =
                                          FStarC_TypeChecker_Env.inst_tscheme_with
                                            ts
                                            c21.FStarC_Syntax_Syntax.comp_univs in
                                        FStar_Pervasives_Native.snd uu___12 in
                                      FStar_Pervasives_Native.Some uu___11 in
                                    let uu___11 =
                                      FStarC_Compiler_Util.must kopt in
                                    (uu___10, uu___11) in
                              (match uu___8 with
                               | (tsopt, k) ->
                                   let num_eff_params =
                                     match ed2.FStarC_Syntax_Syntax.signature
                                     with
                                     | FStarC_Syntax_Syntax.Layered_eff_sig
                                         (n, uu___9) -> n
                                     | uu___9 ->
                                         failwith
                                           "Impossible (expected indexed effect subcomp)" in
                                   (c12, g_lift, tsopt, k, num_eff_params,
                                     false))))
                | FStar_Pervasives_Native.Some (t, kind) ->
                    let uu___6 =
                      let uu___7 =
                        let uu___8 =
                          FStarC_TypeChecker_Env.inst_tscheme_with t
                            c21.FStarC_Syntax_Syntax.comp_univs in
                        FStar_Pervasives_Native.snd uu___8 in
                      FStar_Pervasives_Native.Some uu___7 in
                    (c11, FStarC_TypeChecker_Env.trivial_guard, uu___6, kind,
                      Prims.int_zero, true) in
              match uu___4 with
              | (c12, g_lift, stronger_t_opt, kind, num_eff_params,
                 is_polymonadic) ->
                  if FStarC_Compiler_Util.is_none stronger_t_opt
                  then
                    let uu___5 =
                      mklstr
                        (fun uu___6 ->
                           let uu___7 =
                             FStarC_Class_Show.show
                               FStarC_Ident.showable_lident
                               c12.FStarC_Syntax_Syntax.effect_name in
                           let uu___8 =
                             FStarC_Class_Show.show
                               FStarC_Ident.showable_lident
                               c21.FStarC_Syntax_Syntax.effect_name in
                           FStarC_Compiler_Util.format2
                             "incompatible monad ordering: %s </: %s" uu___7
                             uu___8) in
                    giveup wl uu___5 orig
                  else
                    (let stronger_t =
                       FStarC_Compiler_Util.must stronger_t_opt in
                     let wl1 =
                       extend_wl wl g_lift.FStarC_TypeChecker_Common.deferred
                         g_lift.FStarC_TypeChecker_Common.deferred_to_tac
                         g_lift.FStarC_TypeChecker_Common.implicits in
                     (let uu___7 =
                        ((is_polymonadic &&
                            (FStarC_TypeChecker_Env.is_erasable_effect env
                               c12.FStarC_Syntax_Syntax.effect_name))
                           &&
                           (let uu___8 =
                              FStarC_TypeChecker_Env.is_erasable_effect env
                                c21.FStarC_Syntax_Syntax.effect_name in
                            Prims.op_Negation uu___8))
                          &&
                          (let uu___8 =
                             FStarC_TypeChecker_Normalize.non_info_norm env
                               c12.FStarC_Syntax_Syntax.result_typ in
                           Prims.op_Negation uu___8) in
                      if uu___7
                      then
                        let uu___8 =
                          let uu___9 =
                            FStarC_Ident.string_of_lid
                              c12.FStarC_Syntax_Syntax.effect_name in
                          let uu___10 =
                            FStarC_Ident.string_of_lid
                              c21.FStarC_Syntax_Syntax.effect_name in
                          let uu___11 =
                            FStarC_Class_Show.show
                              FStarC_Syntax_Print.showable_term
                              c12.FStarC_Syntax_Syntax.result_typ in
                          FStarC_Compiler_Util.format3
                            "Cannot lift erasable expression from %s ~> %s since its type %s is informative"
                            uu___9 uu___10 uu___11 in
                        FStarC_Errors.raise_error
                          FStarC_Class_HasRange.hasRange_range r
                          FStarC_Errors_Codes.Error_TypeError ()
                          (Obj.magic
                             FStarC_Errors_Msg.is_error_message_string)
                          (Obj.magic uu___8)
                      else ());
                     (let uu___7 =
                        if is_polymonadic
                        then ([], wl1)
                        else
                          (let rec is_uvar t =
                             let uu___9 =
                               let uu___10 = FStarC_Syntax_Subst.compress t in
                               uu___10.FStarC_Syntax_Syntax.n in
                             match uu___9 with
                             | FStarC_Syntax_Syntax.Tm_uvar (uv, uu___10) ->
                                 let uu___11 =
                                   FStarC_TypeChecker_DeferredImplicits.should_defer_uvar_to_user_tac
                                     env uv in
                                 Prims.op_Negation uu___11
                             | FStarC_Syntax_Syntax.Tm_uinst (t1, uu___10) ->
                                 is_uvar t1
                             | FStarC_Syntax_Syntax.Tm_app
                                 { FStarC_Syntax_Syntax.hd = t1;
                                   FStarC_Syntax_Syntax.args = uu___10;_}
                                 -> is_uvar t1
                             | uu___10 -> false in
                           FStarC_Compiler_List.fold_right2
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
                                              FStarC_Compiler_Effect.op_Bang
                                                dbg_LayeredEffectsEqns in
                                            if uu___16
                                            then
                                              let uu___17 =
                                                FStarC_Class_Show.show
                                                  FStarC_Syntax_Print.showable_term
                                                  a1 in
                                              let uu___18 =
                                                FStarC_Class_Show.show
                                                  FStarC_Syntax_Print.showable_term
                                                  a2 in
                                              FStarC_Compiler_Util.print2
                                                "Layered Effects teq (rel c1 index uvar) %s = %s\n"
                                                uu___17 uu___18
                                            else ());
                                           (let uu___16 =
                                              sub_prob wl2 a1
                                                FStarC_TypeChecker_Common.EQ
                                                a2 "l.h.s. effect index uvar" in
                                            match uu___16 with
                                            | (p, wl3) ->
                                                ((p :: is_sub_probs), wl3)))
                                        else (is_sub_probs, wl2))
                             c12.FStarC_Syntax_Syntax.effect_args
                             c21.FStarC_Syntax_Syntax.effect_args ([], wl1)) in
                      match uu___7 with
                      | (is_sub_probs, wl2) ->
                          let uu___8 =
                            sub_prob wl2 c12.FStarC_Syntax_Syntax.result_typ
                              problem.FStarC_TypeChecker_Common.relation
                              c21.FStarC_Syntax_Syntax.result_typ
                              "result type" in
                          (match uu___8 with
                           | (ret_sub_prob, wl3) ->
                               let uu___9 =
                                 FStarC_Syntax_Util.arrow_formals_comp
                                   stronger_t in
                               (match uu___9 with
                                | (bs, subcomp_c) ->
                                    let uu___10 =
                                      if
                                        kind =
                                          FStarC_Syntax_Syntax.Ad_hoc_combinator
                                      then
                                        apply_ad_hoc_indexed_subcomp env bs
                                          subcomp_c c12 c21 sub_prob wl3
                                          subcomp_name r
                                      else
                                        apply_substitutive_indexed_subcomp
                                          env kind bs subcomp_c c12 c21
                                          sub_prob num_eff_params wl3
                                          subcomp_name r in
                                    (match uu___10 with
                                     | (fml, sub_probs, wl4) ->
                                         let sub_probs1 = ret_sub_prob ::
                                           (FStarC_Compiler_List.op_At
                                              is_sub_probs sub_probs) in
                                         let guard =
                                           let guard1 =
                                             let uu___11 =
                                               FStarC_Compiler_List.map
                                                 p_guard sub_probs1 in
                                             FStarC_Syntax_Util.mk_conj_l
                                               uu___11 in
                                           let guard2 =
                                             match g_lift.FStarC_TypeChecker_Common.guard_f
                                             with
                                             | FStarC_TypeChecker_Common.Trivial
                                                 -> guard1
                                             | FStarC_TypeChecker_Common.NonTrivial
                                                 f ->
                                                 FStarC_Syntax_Util.mk_conj
                                                   guard1 f in
                                           FStarC_Syntax_Util.mk_conj guard2
                                             fml in
                                         let wl5 =
                                           solve_prob orig
                                             (FStar_Pervasives_Native.Some
                                                guard) [] wl4 in
                                         ((let uu___12 =
                                             FStarC_Compiler_Effect.op_Bang
                                               dbg_LayeredEffectsApp in
                                           if uu___12
                                           then
                                             FStarC_Compiler_Util.print_string
                                               "}\n"
                                           else ());
                                          (let uu___12 =
                                             attempt sub_probs1 wl5 in
                                           solve uu___12))))))))) in
      let solve_sub c11 edge c21 =
        if
          problem.FStarC_TypeChecker_Common.relation <>
            FStarC_TypeChecker_Common.SUB
        then failwith "impossible: solve_sub"
        else ();
        (let r = FStarC_TypeChecker_Env.get_range env in
         let lift_c1 uu___1 =
           let univs =
             match c11.FStarC_Syntax_Syntax.comp_univs with
             | [] ->
                 let uu___2 =
                   env.FStarC_TypeChecker_Env.universe_of env
                     c11.FStarC_Syntax_Syntax.result_typ in
                 [uu___2]
             | x -> x in
           let c12 =
             {
               FStarC_Syntax_Syntax.comp_univs = univs;
               FStarC_Syntax_Syntax.effect_name =
                 (c11.FStarC_Syntax_Syntax.effect_name);
               FStarC_Syntax_Syntax.result_typ =
                 (c11.FStarC_Syntax_Syntax.result_typ);
               FStarC_Syntax_Syntax.effect_args =
                 (c11.FStarC_Syntax_Syntax.effect_args);
               FStarC_Syntax_Syntax.flags = (c11.FStarC_Syntax_Syntax.flags)
             } in
           let uu___2 =
             let uu___3 =
               FStarC_Syntax_Syntax.mk_Comp
                 {
                   FStarC_Syntax_Syntax.comp_univs = univs;
                   FStarC_Syntax_Syntax.effect_name =
                     (c12.FStarC_Syntax_Syntax.effect_name);
                   FStarC_Syntax_Syntax.result_typ =
                     (c12.FStarC_Syntax_Syntax.result_typ);
                   FStarC_Syntax_Syntax.effect_args =
                     (c12.FStarC_Syntax_Syntax.effect_args);
                   FStarC_Syntax_Syntax.flags =
                     (c12.FStarC_Syntax_Syntax.flags)
                 } in
             (edge.FStarC_TypeChecker_Env.mlift).FStarC_TypeChecker_Env.mlift_wp
               env uu___3 in
           match uu___2 with
           | (c, g) ->
               let uu___3 =
                 let uu___4 = FStarC_TypeChecker_Env.is_trivial g in
                 Prims.op_Negation uu___4 in
               if uu___3
               then
                 let uu___4 =
                   let uu___5 =
                     FStarC_Class_Show.show FStarC_Ident.showable_lident
                       c12.FStarC_Syntax_Syntax.effect_name in
                   let uu___6 =
                     FStarC_Class_Show.show FStarC_Ident.showable_lident
                       c21.FStarC_Syntax_Syntax.effect_name in
                   FStarC_Compiler_Util.format2
                     "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                     uu___5 uu___6 in
                 FStarC_Errors.raise_error
                   FStarC_Class_HasRange.hasRange_range r
                   FStarC_Errors_Codes.Fatal_UnexpectedEffect ()
                   (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                   (Obj.magic uu___4)
               else FStarC_TypeChecker_Env.comp_to_comp_typ env c in
         let uu___1 =
           should_fail_since_repr_subcomp_not_allowed wl.repr_subcomp_allowed
             c11.FStarC_Syntax_Syntax.effect_name
             c21.FStarC_Syntax_Syntax.effect_name in
         if uu___1
         then
           let uu___2 =
             mklstr
               (fun uu___3 ->
                  let uu___4 =
                    FStarC_Ident.string_of_lid
                      c11.FStarC_Syntax_Syntax.effect_name in
                  let uu___5 =
                    FStarC_Ident.string_of_lid
                      c21.FStarC_Syntax_Syntax.effect_name in
                  FStarC_Compiler_Util.format2
                    "Cannot lift from %s to %s, it needs a lift\n" uu___4
                    uu___5) in
           giveup wl uu___2 orig
         else
           (let is_null_wp_2 =
              FStarC_Compiler_Util.for_some
                (fun uu___3 ->
                   match uu___3 with
                   | FStarC_Syntax_Syntax.TOTAL -> true
                   | FStarC_Syntax_Syntax.MLEFFECT -> true
                   | FStarC_Syntax_Syntax.SOMETRIVIAL -> true
                   | uu___4 -> false) c21.FStarC_Syntax_Syntax.flags in
            let uu___3 =
              match ((c11.FStarC_Syntax_Syntax.effect_args),
                      (c21.FStarC_Syntax_Syntax.effect_args))
              with
              | ((wp1, uu___4)::uu___5, (wp2, uu___6)::uu___7) -> (wp1, wp2)
              | uu___4 ->
                  let uu___5 =
                    let uu___6 =
                      FStarC_Class_Show.show FStarC_Ident.showable_lident
                        c11.FStarC_Syntax_Syntax.effect_name in
                    let uu___7 =
                      FStarC_Class_Show.show FStarC_Ident.showable_lident
                        c21.FStarC_Syntax_Syntax.effect_name in
                    FStarC_Compiler_Util.format2
                      "Got effects %s and %s, expected normalized effects"
                      uu___6 uu___7 in
                  FStarC_Errors.raise_error
                    FStarC_TypeChecker_Env.hasRange_env env
                    FStarC_Errors_Codes.Fatal_ExpectNormalizedEffect ()
                    (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                    (Obj.magic uu___5) in
            match uu___3 with
            | (wpc1, wpc2) ->
                let uu___4 = FStarC_Compiler_Util.physical_equality wpc1 wpc2 in
                if uu___4
                then
                  let uu___5 =
                    problem_using_guard orig
                      c11.FStarC_Syntax_Syntax.result_typ
                      problem.FStarC_TypeChecker_Common.relation
                      c21.FStarC_Syntax_Syntax.result_typ
                      FStar_Pervasives_Native.None "result type" in
                  solve_t uu___5 wl
                else
                  (let uu___6 =
                     let uu___7 =
                       FStarC_TypeChecker_Env.effect_decl_opt env
                         c21.FStarC_Syntax_Syntax.effect_name in
                     FStarC_Compiler_Util.must uu___7 in
                   match uu___6 with
                   | (c2_decl, qualifiers) ->
                       if
                         FStarC_Compiler_List.contains
                           FStarC_Syntax_Syntax.Reifiable qualifiers
                       then
                         let c1_repr =
                           let uu___7 =
                             let uu___8 =
                               let uu___9 = lift_c1 () in
                               FStarC_Syntax_Syntax.mk_Comp uu___9 in
                             let uu___9 =
                               env.FStarC_TypeChecker_Env.universe_of env
                                 c11.FStarC_Syntax_Syntax.result_typ in
                             FStarC_TypeChecker_Env.reify_comp env uu___8
                               uu___9 in
                           norm_with_steps
                             "FStarC.TypeChecker.Rel.norm_with_steps.4"
                             [FStarC_TypeChecker_Env.UnfoldUntil
                                FStarC_Syntax_Syntax.delta_constant;
                             FStarC_TypeChecker_Env.Weak;
                             FStarC_TypeChecker_Env.HNF] env uu___7 in
                         let c2_repr =
                           let uu___7 =
                             let uu___8 = FStarC_Syntax_Syntax.mk_Comp c21 in
                             let uu___9 =
                               env.FStarC_TypeChecker_Env.universe_of env
                                 c21.FStarC_Syntax_Syntax.result_typ in
                             FStarC_TypeChecker_Env.reify_comp env uu___8
                               uu___9 in
                           norm_with_steps
                             "FStarC.TypeChecker.Rel.norm_with_steps.5"
                             [FStarC_TypeChecker_Env.UnfoldUntil
                                FStarC_Syntax_Syntax.delta_constant;
                             FStarC_TypeChecker_Env.Weak;
                             FStarC_TypeChecker_Env.HNF] env uu___7 in
                         let uu___7 =
                           let uu___8 =
                             let uu___9 =
                               FStarC_Class_Show.show
                                 FStarC_Syntax_Print.showable_term c1_repr in
                             let uu___10 =
                               FStarC_Class_Show.show
                                 FStarC_Syntax_Print.showable_term c2_repr in
                             FStarC_Compiler_Util.format2
                               "sub effect repr: %s <: %s" uu___9 uu___10 in
                           sub_prob wl c1_repr
                             problem.FStarC_TypeChecker_Common.relation
                             c2_repr uu___8 in
                         (match uu___7 with
                          | (prob, wl1) ->
                              let wl2 =
                                solve_prob orig
                                  (FStar_Pervasives_Native.Some
                                     (p_guard prob)) [] wl1 in
                              let uu___8 = attempt [prob] wl2 in solve uu___8)
                       else
                         (let g =
                            let uu___8 = FStarC_Options.lax () in
                            if uu___8
                            then FStarC_Syntax_Util.t_true
                            else
                              (let wpc1_2 =
                                 let uu___10 = lift_c1 () in
                                 FStarC_Compiler_List.hd
                                   uu___10.FStarC_Syntax_Syntax.effect_args in
                               if is_null_wp_2
                               then
                                 ((let uu___11 =
                                     FStarC_Compiler_Effect.op_Bang dbg_Rel in
                                   if uu___11
                                   then
                                     FStarC_Compiler_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStarC_TypeChecker_Env.universe_of
                                       env
                                       c11.FStarC_Syntax_Syntax.result_typ in
                                   let trivial =
                                     let uu___11 =
                                       FStarC_Syntax_Util.get_wp_trivial_combinator
                                         c2_decl in
                                     match uu___11 with
                                     | FStar_Pervasives_Native.None ->
                                         failwith
                                           "Rel doesn't yet handle undefined trivial combinator in an effect"
                                     | FStar_Pervasives_Native.Some t -> t in
                                   let uu___11 =
                                     let uu___12 =
                                       let uu___13 =
                                         FStarC_TypeChecker_Env.inst_effect_fun_with
                                           [c1_univ] env c2_decl trivial in
                                       let uu___14 =
                                         let uu___15 =
                                           FStarC_Syntax_Syntax.as_arg
                                             c11.FStarC_Syntax_Syntax.result_typ in
                                         [uu___15; wpc1_2] in
                                       {
                                         FStarC_Syntax_Syntax.hd = uu___13;
                                         FStarC_Syntax_Syntax.args = uu___14
                                       } in
                                     FStarC_Syntax_Syntax.Tm_app uu___12 in
                                   FStarC_Syntax_Syntax.mk uu___11 r))
                               else
                                 (let c2_univ =
                                    env.FStarC_TypeChecker_Env.universe_of
                                      env c21.FStarC_Syntax_Syntax.result_typ in
                                  let stronger =
                                    let uu___11 =
                                      FStarC_Syntax_Util.get_stronger_vc_combinator
                                        c2_decl in
                                    FStar_Pervasives_Native.fst uu___11 in
                                  let uu___11 =
                                    let uu___12 =
                                      let uu___13 =
                                        FStarC_TypeChecker_Env.inst_effect_fun_with
                                          [c2_univ] env c2_decl stronger in
                                      let uu___14 =
                                        let uu___15 =
                                          FStarC_Syntax_Syntax.as_arg
                                            c21.FStarC_Syntax_Syntax.result_typ in
                                        let uu___16 =
                                          let uu___17 =
                                            FStarC_Syntax_Syntax.as_arg wpc2 in
                                          [uu___17; wpc1_2] in
                                        uu___15 :: uu___16 in
                                      {
                                        FStarC_Syntax_Syntax.hd = uu___13;
                                        FStarC_Syntax_Syntax.args = uu___14
                                      } in
                                    FStarC_Syntax_Syntax.Tm_app uu___12 in
                                  FStarC_Syntax_Syntax.mk uu___11 r)) in
                          (let uu___9 =
                             FStarC_Compiler_Effect.op_Bang dbg_Rel in
                           if uu___9
                           then
                             let uu___10 =
                               let uu___11 =
                                 FStarC_TypeChecker_Normalize.normalize
                                   [FStarC_TypeChecker_Env.Iota;
                                   FStarC_TypeChecker_Env.Eager_unfolding;
                                   FStarC_TypeChecker_Env.Primops;
                                   FStarC_TypeChecker_Env.Simplify] env g in
                               FStarC_Class_Show.show
                                 FStarC_Syntax_Print.showable_term uu___11 in
                             FStarC_Compiler_Util.print1
                               "WP guard (simplifed) is (%s)\n" uu___10
                           else ());
                          (let uu___9 =
                             sub_prob wl c11.FStarC_Syntax_Syntax.result_typ
                               problem.FStarC_TypeChecker_Common.relation
                               c21.FStarC_Syntax_Syntax.result_typ
                               "result type" in
                           match uu___9 with
                           | (base_prob, wl1) ->
                               let wl2 =
                                 let uu___10 =
                                   let uu___11 =
                                     FStarC_Syntax_Util.mk_conj
                                       (p_guard base_prob) g in
                                   FStar_Pervasives_Native.Some uu___11 in
                                 solve_prob orig uu___10 [] wl1 in
                               let uu___10 = attempt [base_prob] wl2 in
                               solve uu___10))))) in
      let uu___ = FStarC_Compiler_Util.physical_equality c1 c2 in
      if uu___
      then
        let uu___1 = solve_prob orig FStar_Pervasives_Native.None [] wl in
        solve uu___1
      else
        ((let uu___3 = FStarC_Compiler_Effect.op_Bang dbg_Rel in
          if uu___3
          then
            let uu___4 =
              FStarC_Class_Show.show FStarC_Syntax_Print.showable_comp c1 in
            let uu___5 =
              FStarC_Class_Show.show FStarC_Syntax_Print.showable_comp c2 in
            FStarC_Compiler_Util.print3 "solve_c %s %s %s\n" uu___4
              (rel_to_string problem.FStarC_TypeChecker_Common.relation)
              uu___5
          else ());
         (let uu___3 =
            let uu___4 =
              let uu___5 =
                FStarC_TypeChecker_Env.norm_eff_name env
                  (FStarC_Syntax_Util.comp_effect_name c1) in
              let uu___6 =
                FStarC_TypeChecker_Env.norm_eff_name env
                  (FStarC_Syntax_Util.comp_effect_name c2) in
              (uu___5, uu___6) in
            match uu___4 with
            | (eff1, eff2) ->
                let uu___5 = FStarC_Ident.lid_equals eff1 eff2 in
                if uu___5
                then (c1, c2)
                else FStarC_TypeChecker_Normalize.ghost_to_pure2 env (c1, c2) in
          match uu___3 with
          | (c11, c21) ->
              (match ((c11.FStarC_Syntax_Syntax.n),
                       (c21.FStarC_Syntax_Syntax.n))
               with
               | (FStarC_Syntax_Syntax.GTotal t1, FStarC_Syntax_Syntax.Total
                  t2) when FStarC_TypeChecker_Env.non_informative env t2 ->
                   let uu___4 =
                     problem_using_guard orig t1
                       problem.FStarC_TypeChecker_Common.relation t2
                       FStar_Pervasives_Native.None "result type" in
                   solve_t uu___4 wl
               | (FStarC_Syntax_Syntax.GTotal uu___4,
                  FStarC_Syntax_Syntax.Total uu___5) ->
                   let uu___6 =
                     FStarC_Thunk.mkv
                       "incompatible monad ordering: GTot </: Tot" in
                   giveup wl uu___6 orig
               | (FStarC_Syntax_Syntax.Total t1, FStarC_Syntax_Syntax.Total
                  t2) ->
                   let uu___4 =
                     problem_using_guard orig t1
                       problem.FStarC_TypeChecker_Common.relation t2
                       FStar_Pervasives_Native.None "result type" in
                   solve_t uu___4 wl
               | (FStarC_Syntax_Syntax.GTotal t1, FStarC_Syntax_Syntax.GTotal
                  t2) ->
                   let uu___4 =
                     problem_using_guard orig t1
                       problem.FStarC_TypeChecker_Common.relation t2
                       FStar_Pervasives_Native.None "result type" in
                   solve_t uu___4 wl
               | (FStarC_Syntax_Syntax.Total t1, FStarC_Syntax_Syntax.GTotal
                  t2) when
                   problem.FStarC_TypeChecker_Common.relation =
                     FStarC_TypeChecker_Common.SUB
                   ->
                   let uu___4 =
                     problem_using_guard orig t1
                       problem.FStarC_TypeChecker_Common.relation t2
                       FStar_Pervasives_Native.None "result type" in
                   solve_t uu___4 wl
               | (FStarC_Syntax_Syntax.Total t1, FStarC_Syntax_Syntax.GTotal
                  t2) ->
                   let uu___4 = FStarC_Thunk.mkv "GTot =/= Tot" in
                   giveup wl uu___4 orig
               | (FStarC_Syntax_Syntax.GTotal uu___4,
                  FStarC_Syntax_Syntax.Comp uu___5) ->
                   let uu___6 =
                     let uu___7 =
                       let uu___8 =
                         FStarC_TypeChecker_Env.comp_to_comp_typ env c11 in
                       FStarC_Syntax_Syntax.mk_Comp uu___8 in
                     {
                       FStarC_TypeChecker_Common.pid =
                         (problem.FStarC_TypeChecker_Common.pid);
                       FStarC_TypeChecker_Common.lhs = uu___7;
                       FStarC_TypeChecker_Common.relation =
                         (problem.FStarC_TypeChecker_Common.relation);
                       FStarC_TypeChecker_Common.rhs =
                         (problem.FStarC_TypeChecker_Common.rhs);
                       FStarC_TypeChecker_Common.element =
                         (problem.FStarC_TypeChecker_Common.element);
                       FStarC_TypeChecker_Common.logical_guard =
                         (problem.FStarC_TypeChecker_Common.logical_guard);
                       FStarC_TypeChecker_Common.logical_guard_uvar =
                         (problem.FStarC_TypeChecker_Common.logical_guard_uvar);
                       FStarC_TypeChecker_Common.reason =
                         (problem.FStarC_TypeChecker_Common.reason);
                       FStarC_TypeChecker_Common.loc =
                         (problem.FStarC_TypeChecker_Common.loc);
                       FStarC_TypeChecker_Common.rank =
                         (problem.FStarC_TypeChecker_Common.rank);
                       FStarC_TypeChecker_Common.logical =
                         (problem.FStarC_TypeChecker_Common.logical)
                     } in
                   solve_c uu___6 wl
               | (FStarC_Syntax_Syntax.Total uu___4,
                  FStarC_Syntax_Syntax.Comp uu___5) ->
                   let uu___6 =
                     let uu___7 =
                       let uu___8 =
                         FStarC_TypeChecker_Env.comp_to_comp_typ env c11 in
                       FStarC_Syntax_Syntax.mk_Comp uu___8 in
                     {
                       FStarC_TypeChecker_Common.pid =
                         (problem.FStarC_TypeChecker_Common.pid);
                       FStarC_TypeChecker_Common.lhs = uu___7;
                       FStarC_TypeChecker_Common.relation =
                         (problem.FStarC_TypeChecker_Common.relation);
                       FStarC_TypeChecker_Common.rhs =
                         (problem.FStarC_TypeChecker_Common.rhs);
                       FStarC_TypeChecker_Common.element =
                         (problem.FStarC_TypeChecker_Common.element);
                       FStarC_TypeChecker_Common.logical_guard =
                         (problem.FStarC_TypeChecker_Common.logical_guard);
                       FStarC_TypeChecker_Common.logical_guard_uvar =
                         (problem.FStarC_TypeChecker_Common.logical_guard_uvar);
                       FStarC_TypeChecker_Common.reason =
                         (problem.FStarC_TypeChecker_Common.reason);
                       FStarC_TypeChecker_Common.loc =
                         (problem.FStarC_TypeChecker_Common.loc);
                       FStarC_TypeChecker_Common.rank =
                         (problem.FStarC_TypeChecker_Common.rank);
                       FStarC_TypeChecker_Common.logical =
                         (problem.FStarC_TypeChecker_Common.logical)
                     } in
                   solve_c uu___6 wl
               | (FStarC_Syntax_Syntax.Comp uu___4,
                  FStarC_Syntax_Syntax.GTotal uu___5) ->
                   let uu___6 =
                     let uu___7 =
                       let uu___8 =
                         FStarC_TypeChecker_Env.comp_to_comp_typ env c21 in
                       FStarC_Syntax_Syntax.mk_Comp uu___8 in
                     {
                       FStarC_TypeChecker_Common.pid =
                         (problem.FStarC_TypeChecker_Common.pid);
                       FStarC_TypeChecker_Common.lhs =
                         (problem.FStarC_TypeChecker_Common.lhs);
                       FStarC_TypeChecker_Common.relation =
                         (problem.FStarC_TypeChecker_Common.relation);
                       FStarC_TypeChecker_Common.rhs = uu___7;
                       FStarC_TypeChecker_Common.element =
                         (problem.FStarC_TypeChecker_Common.element);
                       FStarC_TypeChecker_Common.logical_guard =
                         (problem.FStarC_TypeChecker_Common.logical_guard);
                       FStarC_TypeChecker_Common.logical_guard_uvar =
                         (problem.FStarC_TypeChecker_Common.logical_guard_uvar);
                       FStarC_TypeChecker_Common.reason =
                         (problem.FStarC_TypeChecker_Common.reason);
                       FStarC_TypeChecker_Common.loc =
                         (problem.FStarC_TypeChecker_Common.loc);
                       FStarC_TypeChecker_Common.rank =
                         (problem.FStarC_TypeChecker_Common.rank);
                       FStarC_TypeChecker_Common.logical =
                         (problem.FStarC_TypeChecker_Common.logical)
                     } in
                   solve_c uu___6 wl
               | (FStarC_Syntax_Syntax.Comp uu___4,
                  FStarC_Syntax_Syntax.Total uu___5) ->
                   let uu___6 =
                     let uu___7 =
                       let uu___8 =
                         FStarC_TypeChecker_Env.comp_to_comp_typ env c21 in
                       FStarC_Syntax_Syntax.mk_Comp uu___8 in
                     {
                       FStarC_TypeChecker_Common.pid =
                         (problem.FStarC_TypeChecker_Common.pid);
                       FStarC_TypeChecker_Common.lhs =
                         (problem.FStarC_TypeChecker_Common.lhs);
                       FStarC_TypeChecker_Common.relation =
                         (problem.FStarC_TypeChecker_Common.relation);
                       FStarC_TypeChecker_Common.rhs = uu___7;
                       FStarC_TypeChecker_Common.element =
                         (problem.FStarC_TypeChecker_Common.element);
                       FStarC_TypeChecker_Common.logical_guard =
                         (problem.FStarC_TypeChecker_Common.logical_guard);
                       FStarC_TypeChecker_Common.logical_guard_uvar =
                         (problem.FStarC_TypeChecker_Common.logical_guard_uvar);
                       FStarC_TypeChecker_Common.reason =
                         (problem.FStarC_TypeChecker_Common.reason);
                       FStarC_TypeChecker_Common.loc =
                         (problem.FStarC_TypeChecker_Common.loc);
                       FStarC_TypeChecker_Common.rank =
                         (problem.FStarC_TypeChecker_Common.rank);
                       FStarC_TypeChecker_Common.logical =
                         (problem.FStarC_TypeChecker_Common.logical)
                     } in
                   solve_c uu___6 wl
               | (FStarC_Syntax_Syntax.Comp uu___4, FStarC_Syntax_Syntax.Comp
                  uu___5) ->
                   let uu___6 =
                     (((FStarC_Syntax_Util.is_ml_comp c11) &&
                         (FStarC_Syntax_Util.is_ml_comp c21))
                        ||
                        ((FStarC_Syntax_Util.is_total_comp c11) &&
                           (FStarC_Syntax_Util.is_total_comp c21)))
                       ||
                       (((FStarC_Syntax_Util.is_total_comp c11) &&
                           (FStarC_Syntax_Util.is_ml_comp c21))
                          &&
                          (problem.FStarC_TypeChecker_Common.relation =
                             FStarC_TypeChecker_Common.SUB)) in
                   if uu___6
                   then
                     let uu___7 =
                       problem_using_guard orig
                         (FStarC_Syntax_Util.comp_result c11)
                         problem.FStarC_TypeChecker_Common.relation
                         (FStarC_Syntax_Util.comp_result c21)
                         FStar_Pervasives_Native.None "result type" in
                     solve_t uu___7 wl
                   else
                     (let c1_comp =
                        FStarC_TypeChecker_Env.comp_to_comp_typ env c11 in
                      let c2_comp =
                        FStarC_TypeChecker_Env.comp_to_comp_typ env c21 in
                      if
                        problem.FStarC_TypeChecker_Common.relation =
                          FStarC_TypeChecker_Common.EQ
                      then
                        let uu___8 =
                          let uu___9 =
                            FStarC_Ident.lid_equals
                              c1_comp.FStarC_Syntax_Syntax.effect_name
                              c2_comp.FStarC_Syntax_Syntax.effect_name in
                          if uu___9
                          then (c1_comp, c2_comp)
                          else
                            (let uu___11 =
                               FStarC_TypeChecker_Env.unfold_effect_abbrev
                                 env c11 in
                             let uu___12 =
                               FStarC_TypeChecker_Env.unfold_effect_abbrev
                                 env c21 in
                             (uu___11, uu___12)) in
                        match uu___8 with
                        | (c1_comp1, c2_comp1) ->
                            solve_eq c1_comp1 c2_comp1
                              FStarC_TypeChecker_Env.trivial_guard
                      else
                        (let c12 =
                           FStarC_TypeChecker_Env.unfold_effect_abbrev env
                             c11 in
                         let c22 =
                           FStarC_TypeChecker_Env.unfold_effect_abbrev env
                             c21 in
                         (let uu___10 =
                            FStarC_Compiler_Effect.op_Bang dbg_Rel in
                          if uu___10
                          then
                            let uu___11 =
                              FStarC_Ident.string_of_lid
                                c12.FStarC_Syntax_Syntax.effect_name in
                            let uu___12 =
                              FStarC_Ident.string_of_lid
                                c22.FStarC_Syntax_Syntax.effect_name in
                            FStarC_Compiler_Util.print2
                              "solve_c for %s and %s\n" uu___11 uu___12
                          else ());
                         (let uu___10 =
                            FStarC_TypeChecker_Env.is_layered_effect env
                              c22.FStarC_Syntax_Syntax.effect_name in
                          if uu___10
                          then solve_layered_sub c12 c22
                          else
                            (let uu___12 =
                               FStarC_TypeChecker_Env.monad_leq env
                                 c12.FStarC_Syntax_Syntax.effect_name
                                 c22.FStarC_Syntax_Syntax.effect_name in
                             match uu___12 with
                             | FStar_Pervasives_Native.None ->
                                 let uu___13 =
                                   mklstr
                                     (fun uu___14 ->
                                        let uu___15 =
                                          FStarC_Class_Show.show
                                            FStarC_Ident.showable_lident
                                            c12.FStarC_Syntax_Syntax.effect_name in
                                        let uu___16 =
                                          FStarC_Class_Show.show
                                            FStarC_Ident.showable_lident
                                            c22.FStarC_Syntax_Syntax.effect_name in
                                        FStarC_Compiler_Util.format2
                                          "incompatible monad ordering: %s </: %s"
                                          uu___15 uu___16) in
                                 giveup wl uu___13 orig
                             | FStar_Pervasives_Native.Some edge ->
                                 solve_sub c12 edge c22)))))))
let (print_pending_implicits :
  FStarC_TypeChecker_Common.guard_t -> Prims.string) =
  fun g ->
    let uu___ =
      FStarC_Compiler_CList.map
        (fun i ->
           FStarC_Class_Show.show FStarC_Syntax_Print.showable_ctxu
             i.FStarC_TypeChecker_Common.imp_uvar)
        g.FStarC_TypeChecker_Common.implicits in
    FStarC_Class_Show.show
      (FStarC_Compiler_CList.showable_clist FStarC_Class_Show.showable_string)
      uu___
let (ineqs_to_string :
  (FStarC_Syntax_Syntax.universe FStarC_Compiler_CList.clist *
    (FStarC_Syntax_Syntax.universe * FStarC_Syntax_Syntax.universe)
    FStarC_Compiler_CList.clist) -> Prims.string)
  =
  fun ineqs ->
    let uu___ = ineqs in
    match uu___ with
    | (vars, ineqs1) ->
        let ineqs2 =
          FStarC_Compiler_CList.map
            (fun uu___1 ->
               match uu___1 with
               | (u1, u2) ->
                   let uu___2 =
                     FStarC_Class_Show.show FStarC_Syntax_Print.showable_univ
                       u1 in
                   let uu___3 =
                     FStarC_Class_Show.show FStarC_Syntax_Print.showable_univ
                       u2 in
                   FStarC_Compiler_Util.format2 "%s < %s" uu___2 uu___3)
            ineqs1 in
        let uu___1 =
          FStarC_Class_Show.show
            (FStarC_Compiler_CList.showable_clist
               FStarC_Syntax_Print.showable_univ) vars in
        let uu___2 =
          FStarC_Class_Show.show
            (FStarC_Compiler_CList.showable_clist
               FStarC_Class_Show.showable_string) ineqs2 in
        FStarC_Compiler_Util.format2 "Solving for %s; inequalities are %s"
          uu___1 uu___2
let (guard_to_string :
  FStarC_TypeChecker_Env.env ->
    FStarC_TypeChecker_Common.guard_t -> Prims.string)
  =
  fun env ->
    fun g ->
      let uu___ =
        let uu___1 =
          Obj.magic
            (FStarC_Class_Listlike.view ()
               (Obj.magic (FStarC_Compiler_CList.listlike_clist ()))
               (Obj.magic g.FStarC_TypeChecker_Common.deferred)) in
        ((g.FStarC_TypeChecker_Common.guard_f), uu___1) in
      match uu___ with
      | (FStarC_TypeChecker_Common.Trivial, FStarC_Class_Listlike.VNil) when
          (let uu___1 = FStarC_Options.print_implicits () in
           Prims.op_Negation uu___1) &&
            (FStarC_Class_Listlike.is_empty
               (FStarC_Compiler_CList.listlike_clist ())
               (FStar_Pervasives_Native.snd
                  g.FStarC_TypeChecker_Common.univ_ineqs))
          -> "{}"
      | uu___1 ->
          let form =
            match g.FStarC_TypeChecker_Common.guard_f with
            | FStarC_TypeChecker_Common.Trivial -> "trivial"
            | FStarC_TypeChecker_Common.NonTrivial f ->
                let uu___2 =
                  ((FStarC_Compiler_Effect.op_Bang dbg_Rel) ||
                     (FStarC_Compiler_Debug.extreme ()))
                    || (FStarC_Options.print_implicits ()) in
                if uu___2
                then FStarC_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry defs =
            let uu___2 =
              let uu___3 =
                FStarC_Compiler_CList.map
                  (fun uu___4 ->
                     match uu___4 with
                     | (uu___5, msg, x) ->
                         let uu___6 =
                           let uu___7 = prob_to_string env x in
                           Prims.strcat ": " uu___7 in
                         Prims.strcat msg uu___6) defs in
              FStarC_Class_Listlike.to_list
                (FStarC_Compiler_CList.listlike_clist ()) uu___3 in
            FStarC_Compiler_String.concat ",\n" uu___2 in
          let imps = print_pending_implicits g in
          let uu___2 = carry g.FStarC_TypeChecker_Common.deferred in
          let uu___3 = carry g.FStarC_TypeChecker_Common.deferred_to_tac in
          let uu___4 = ineqs_to_string g.FStarC_TypeChecker_Common.univ_ineqs in
          FStarC_Compiler_Util.format5
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t deferred_to_tac={\n%s};\n\t univ_ineqs={%s};\n\t implicits=%s}\n"
            form uu___2 uu___3 uu___4 imps
let (new_t_problem :
  worklist ->
    FStarC_TypeChecker_Env.env ->
      FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
        FStarC_TypeChecker_Common.rel ->
          FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
            FStarC_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
              FStarC_Compiler_Range_Type.range ->
                (FStarC_TypeChecker_Common.prob * worklist))
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
                    (FStarC_Compiler_Effect.op_Bang dbg_ExplainRel) ||
                      (FStarC_Compiler_Effect.op_Bang dbg_Rel) in
                  if uu___
                  then
                    let uu___1 =
                      FStarC_TypeChecker_Normalize.term_to_string env lhs in
                    let uu___2 =
                      FStarC_TypeChecker_Normalize.term_to_string env rhs in
                    FStarC_Compiler_Util.format3 "Top-level:\n%s\n\t%s\n%s"
                      uu___1 (rel_to_string rel) uu___2
                  else "TOP" in
                let uu___ = new_problem wl env lhs rel rhs elt loc reason in
                match uu___ with
                | (p, wl1) ->
                    (def_check_prob (Prims.strcat "new_t_problem." reason)
                       (FStarC_TypeChecker_Common.TProb p);
                     ((FStarC_TypeChecker_Common.TProb p), wl1))
let (new_t_prob :
  worklist ->
    FStarC_TypeChecker_Env.env ->
      FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
        FStarC_TypeChecker_Common.rel ->
          FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
            (FStarC_TypeChecker_Common.prob * FStarC_Syntax_Syntax.bv *
              worklist))
  =
  fun wl ->
    fun env ->
      fun t1 ->
        fun rel ->
          fun t2 ->
            let x =
              let uu___ =
                let uu___1 = FStarC_TypeChecker_Env.get_range env in
                FStar_Pervasives_Native.Some uu___1 in
              FStarC_Syntax_Syntax.new_bv uu___ t1 in
            let uu___ =
              let uu___1 = FStarC_TypeChecker_Env.get_range env in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu___1 in
            match uu___ with | (p, wl1) -> (p, x, wl1)
let (solve_and_commit :
  worklist ->
    ((FStarC_TypeChecker_Common.prob * lstring) ->
       (FStarC_TypeChecker_Common.deferred *
         FStarC_TypeChecker_Common.deferred *
         FStarC_TypeChecker_Common.implicits_t)
         FStar_Pervasives_Native.option)
      ->
      (FStarC_TypeChecker_Common.deferred *
        FStarC_TypeChecker_Common.deferred *
        FStarC_TypeChecker_Common.implicits_t) FStar_Pervasives_Native.option)
  =
  fun wl ->
    fun err ->
      let tx = FStarC_Syntax_Unionfind.new_transaction () in
      (let uu___1 = FStarC_Compiler_Effect.op_Bang dbg_RelBench in
       if uu___1
       then
         let uu___2 =
           (FStarC_Common.string_of_list ())
             (fun p -> FStarC_Compiler_Util.string_of_int (p_pid p))
             wl.attempting in
         FStarC_Compiler_Util.print1 "solving problems %s {\n" uu___2
       else ());
      (let uu___1 = FStarC_Compiler_Util.record_time (fun uu___2 -> solve wl) in
       match uu___1 with
       | (sol, ms) ->
           ((let uu___3 = FStarC_Compiler_Effect.op_Bang dbg_RelBench in
             if uu___3
             then
               let uu___4 = FStarC_Compiler_Util.string_of_int ms in
               FStarC_Compiler_Util.print1 "} solved in %s ms\n" uu___4
             else ());
            (match sol with
             | Success (deferred, defer_to_tac, implicits) ->
                 let uu___3 =
                   FStarC_Compiler_Util.record_time
                     (fun uu___4 -> FStarC_Syntax_Unionfind.commit tx) in
                 (match uu___3 with
                  | ((), ms1) ->
                      ((let uu___5 =
                          FStarC_Compiler_Effect.op_Bang dbg_RelBench in
                        if uu___5
                        then
                          let uu___6 = FStarC_Compiler_Util.string_of_int ms1 in
                          FStarC_Compiler_Util.print1 "committed in %s ms\n"
                            uu___6
                        else ());
                       FStar_Pervasives_Native.Some
                         (deferred, defer_to_tac, implicits)))
             | Failed (d, s) ->
                 ((let uu___4 =
                     (FStarC_Compiler_Effect.op_Bang dbg_ExplainRel) ||
                       (FStarC_Compiler_Effect.op_Bang dbg_Rel) in
                   if uu___4
                   then
                     let uu___5 = explain wl d s in
                     FStarC_Compiler_Util.print_string uu___5
                   else ());
                  (let result = err (d, s) in
                   FStarC_Syntax_Unionfind.rollback tx; result)))))
let (with_guard :
  FStarC_TypeChecker_Env.env ->
    FStarC_TypeChecker_Common.prob ->
      (FStarC_TypeChecker_Common.deferred *
        FStarC_TypeChecker_Common.deferred *
        FStarC_TypeChecker_Common.implicits_t) FStar_Pervasives_Native.option
        -> FStarC_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env ->
    fun prob ->
      fun dopt ->
        match dopt with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (deferred, defer_to_tac, implicits) ->
            (FStarC_Defensive.def_check_scoped
               FStarC_TypeChecker_Env.hasBinders_env
               FStarC_Class_Binders.hasNames_term
               FStarC_Syntax_Print.pretty_term (p_loc prob) "with_guard" env
               (p_guard prob);
             (let uu___1 =
                simplify_guard env
                  {
                    FStarC_TypeChecker_Common.guard_f =
                      (FStarC_TypeChecker_Common.NonTrivial (p_guard prob));
                    FStarC_TypeChecker_Common.deferred_to_tac = defer_to_tac;
                    FStarC_TypeChecker_Common.deferred = deferred;
                    FStarC_TypeChecker_Common.univ_ineqs =
                      ((Obj.magic
                          (FStarC_Class_Listlike.empty ()
                             (Obj.magic
                                (FStarC_Compiler_CList.listlike_clist ())))),
                        (Obj.magic
                           (FStarC_Class_Listlike.empty ()
                              (Obj.magic
                                 (FStarC_Compiler_CList.listlike_clist ())))));
                    FStarC_TypeChecker_Common.implicits = implicits
                  } in
              FStar_Pervasives_Native.Some uu___1))
let (try_teq :
  Prims.bool ->
    FStarC_TypeChecker_Env.env ->
      FStarC_Syntax_Syntax.typ ->
        FStarC_Syntax_Syntax.typ ->
          FStarC_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun smt_ok ->
    fun env ->
      fun t1 ->
        fun t2 ->
          FStarC_Defensive.def_check_scoped
            FStarC_TypeChecker_Env.hasBinders_env
            FStarC_Class_Binders.hasNames_term
            FStarC_Syntax_Print.pretty_term t1.FStarC_Syntax_Syntax.pos
            "try_teq.1" env t1;
          FStarC_Defensive.def_check_scoped
            FStarC_TypeChecker_Env.hasBinders_env
            FStarC_Class_Binders.hasNames_term
            FStarC_Syntax_Print.pretty_term t2.FStarC_Syntax_Syntax.pos
            "try_teq.2" env t2;
          (let smt_ok1 =
             smt_ok &&
               (let uu___2 = FStarC_Options.ml_ish () in
                Prims.op_Negation uu___2) in
           let uu___2 =
             let uu___3 =
               let uu___4 = FStarC_TypeChecker_Env.current_module env in
               FStarC_Ident.string_of_lid uu___4 in
             FStar_Pervasives_Native.Some uu___3 in
           FStarC_Profiling.profile
             (fun uu___3 ->
                (let uu___5 = FStarC_Compiler_Effect.op_Bang dbg_RelTop in
                 if uu___5
                 then
                   let uu___6 =
                     FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                       t1 in
                   let uu___7 =
                     FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                       t2 in
                   let uu___8 =
                     FStarC_Class_Show.show
                       (FStarC_Class_Show.show_list
                          FStarC_Syntax_Print.showable_binding)
                       env.FStarC_TypeChecker_Env.gamma in
                   FStarC_Compiler_Util.print3
                     "try_teq of %s and %s in %s {\n" uu___6 uu___7 uu___8
                 else ());
                (let uu___5 =
                   let uu___6 = empty_worklist env in
                   let uu___7 = FStarC_TypeChecker_Env.get_range env in
                   new_t_problem uu___6 env t1 FStarC_TypeChecker_Common.EQ
                     t2 FStar_Pervasives_Native.None uu___7 in
                 match uu___5 with
                 | (prob, wl) ->
                     let g =
                       let uu___6 =
                         solve_and_commit (singleton wl prob smt_ok1)
                           (fun uu___7 -> FStar_Pervasives_Native.None) in
                       with_guard env prob uu___6 in
                     ((let uu___7 = FStarC_Compiler_Effect.op_Bang dbg_RelTop in
                       if uu___7
                       then
                         let uu___8 =
                           FStarC_Common.string_of_option
                             (guard_to_string env) g in
                         FStarC_Compiler_Util.print1 "} res = %s\n" uu___8
                       else ());
                      g))) uu___2 "FStarC.TypeChecker.Rel.try_teq")
let (teq :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.typ ->
      FStarC_Syntax_Syntax.typ -> FStarC_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu___ = try_teq true env t1 t2 in
        match uu___ with
        | FStar_Pervasives_Native.None ->
            (FStarC_TypeChecker_Err.basic_type_error env
               env.FStarC_TypeChecker_Env.range FStar_Pervasives_Native.None
               t2 t1;
             FStarC_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu___2 =
                (FStarC_Compiler_Effect.op_Bang dbg_Rel) ||
                  (FStarC_Compiler_Effect.op_Bang dbg_RelTop) in
              if uu___2
              then
                let uu___3 =
                  FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t1 in
                let uu___4 =
                  FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t2 in
                let uu___5 = guard_to_string env g in
                FStarC_Compiler_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu___3 uu___4
                  uu___5
              else ());
             g)
let (get_teq_predicate :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.typ ->
      FStarC_Syntax_Syntax.typ ->
        FStarC_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        (let uu___1 =
           (FStarC_Compiler_Effect.op_Bang dbg_Rel) ||
             (FStarC_Compiler_Effect.op_Bang dbg_RelTop) in
         if uu___1
         then
           let uu___2 =
             FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t1 in
           let uu___3 =
             FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t2 in
           FStarC_Compiler_Util.print2 "get_teq_predicate of %s and %s {\n"
             uu___2 uu___3
         else ());
        (let uu___1 =
           let uu___2 = empty_worklist env in
           new_t_prob uu___2 env t1 FStarC_TypeChecker_Common.EQ t2 in
         match uu___1 with
         | (prob, x, wl) ->
             let g =
               let uu___2 =
                 solve_and_commit (singleton wl prob true)
                   (fun uu___3 -> FStar_Pervasives_Native.None) in
               with_guard env prob uu___2 in
             ((let uu___3 =
                 (FStarC_Compiler_Effect.op_Bang dbg_Rel) ||
                   (FStarC_Compiler_Effect.op_Bang dbg_RelTop) in
               if uu___3
               then
                 let uu___4 =
                   FStarC_Common.string_of_option (guard_to_string env) g in
                 FStarC_Compiler_Util.print1 "} res teq predicate = %s\n"
                   uu___4
               else ());
              (match g with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   let uu___3 =
                     let uu___4 = FStarC_Syntax_Syntax.mk_binder x in
                     FStarC_TypeChecker_Env.abstract_guard uu___4 g1 in
                   FStar_Pervasives_Native.Some uu___3)))
let (subtype_fail :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.term ->
      FStarC_Syntax_Syntax.typ -> FStarC_Syntax_Syntax.typ -> unit)
  =
  fun env ->
    fun e ->
      fun t1 ->
        fun t2 ->
          let uu___ = FStarC_TypeChecker_Env.get_range env in
          FStarC_TypeChecker_Err.basic_type_error env uu___
            (FStar_Pervasives_Native.Some e) t2 t1
let (sub_or_eq_comp :
  FStarC_TypeChecker_Env.env ->
    Prims.bool ->
      FStarC_Syntax_Syntax.comp ->
        FStarC_Syntax_Syntax.comp ->
          FStarC_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env ->
    fun use_eq ->
      fun c1 ->
        fun c2 ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStarC_TypeChecker_Env.current_module env in
              FStarC_Ident.string_of_lid uu___2 in
            FStar_Pervasives_Native.Some uu___1 in
          FStarC_Profiling.profile
            (fun uu___1 ->
               let rel =
                 if use_eq
                 then FStarC_TypeChecker_Common.EQ
                 else FStarC_TypeChecker_Common.SUB in
               (let uu___3 =
                  (FStarC_Compiler_Effect.op_Bang dbg_Rel) ||
                    (FStarC_Compiler_Effect.op_Bang dbg_RelTop) in
                if uu___3
                then
                  let uu___4 =
                    FStarC_Class_Show.show FStarC_Syntax_Print.showable_comp
                      c1 in
                  let uu___5 =
                    FStarC_Class_Show.show FStarC_Syntax_Print.showable_comp
                      c2 in
                  FStarC_Compiler_Util.print3
                    "sub_comp of %s --and-- %s --with-- %s\n" uu___4 uu___5
                    (if rel = FStarC_TypeChecker_Common.EQ
                     then "EQ"
                     else "SUB")
                else ());
               (let uu___3 =
                  let uu___4 = empty_worklist env in
                  let uu___5 = FStarC_TypeChecker_Env.get_range env in
                  new_problem uu___4 env c1 rel c2
                    FStar_Pervasives_Native.None uu___5 "sub_comp" in
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
                        repr_subcomp_allowed = true;
                        typeclass_variables = (wl.typeclass_variables)
                      } in
                    let prob1 = FStarC_TypeChecker_Common.CProb prob in
                    (def_check_prob "sub_comp" prob1;
                     (let uu___5 =
                        FStarC_Compiler_Util.record_time
                          (fun uu___6 ->
                             let uu___7 =
                               solve_and_commit (singleton wl1 prob1 true)
                                 (fun uu___8 -> FStar_Pervasives_Native.None) in
                             with_guard env prob1 uu___7) in
                      match uu___5 with
                      | (r, ms) ->
                          ((let uu___7 =
                              ((FStarC_Compiler_Effect.op_Bang dbg_Rel) ||
                                 (FStarC_Compiler_Effect.op_Bang dbg_RelTop))
                                ||
                                (FStarC_Compiler_Effect.op_Bang dbg_RelBench) in
                            if uu___7
                            then
                              let uu___8 =
                                FStarC_Class_Show.show
                                  FStarC_Syntax_Print.showable_comp c1 in
                              let uu___9 =
                                FStarC_Class_Show.show
                                  FStarC_Syntax_Print.showable_comp c2 in
                              let uu___10 =
                                FStarC_Compiler_Util.string_of_int ms in
                              FStarC_Compiler_Util.print4
                                "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                                uu___8 uu___9
                                (if rel = FStarC_TypeChecker_Common.EQ
                                 then "EQ"
                                 else "SUB") uu___10
                            else ());
                           r))))) uu___ "FStarC.TypeChecker.Rel.sub_comp"
let (sub_comp :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.comp ->
      FStarC_Syntax_Syntax.comp ->
        FStarC_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env ->
    fun c1 ->
      fun c2 ->
        FStarC_Errors.with_ctx "While trying to subtype computation types"
          (fun uu___ ->
             FStarC_Defensive.def_check_scoped
               FStarC_TypeChecker_Env.hasBinders_env
               FStarC_Class_Binders.hasNames_comp
               FStarC_Syntax_Print.pretty_comp c1.FStarC_Syntax_Syntax.pos
               "sub_comp c1" env c1;
             FStarC_Defensive.def_check_scoped
               FStarC_TypeChecker_Env.hasBinders_env
               FStarC_Class_Binders.hasNames_comp
               FStarC_Syntax_Print.pretty_comp c2.FStarC_Syntax_Syntax.pos
               "sub_comp c2" env c2;
             sub_or_eq_comp env false c1 c2)
let (eq_comp :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.comp ->
      FStarC_Syntax_Syntax.comp ->
        FStarC_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env ->
    fun c1 ->
      fun c2 ->
        FStarC_Errors.with_ctx "While trying to equate computation types"
          (fun uu___ ->
             FStarC_Defensive.def_check_scoped
               FStarC_TypeChecker_Env.hasBinders_env
               FStarC_Class_Binders.hasNames_comp
               FStarC_Syntax_Print.pretty_comp c1.FStarC_Syntax_Syntax.pos
               "eq_comp c1" env c1;
             FStarC_Defensive.def_check_scoped
               FStarC_TypeChecker_Env.hasBinders_env
               FStarC_Class_Binders.hasNames_comp
               FStarC_Syntax_Print.pretty_comp c2.FStarC_Syntax_Syntax.pos
               "eq_comp c2" env c2;
             sub_or_eq_comp env true c1 c2)
let (solve_universe_inequalities' :
  FStarC_Syntax_Unionfind.tx ->
    FStarC_TypeChecker_Env.env_t ->
      (FStarC_Syntax_Syntax.universe FStarC_Compiler_CList.clist *
        (FStarC_Syntax_Syntax.universe * FStarC_Syntax_Syntax.universe)
        FStarC_Compiler_CList.clist) -> unit)
  =
  fun tx ->
    fun env ->
      fun uu___ ->
        match uu___ with
        | (variables, ineqs) ->
            let fail u1 u2 =
              FStarC_Syntax_Unionfind.rollback tx;
              (let uu___2 =
                 let uu___3 =
                   FStarC_Class_Show.show FStarC_Syntax_Print.showable_univ
                     u1 in
                 let uu___4 =
                   FStarC_Class_Show.show FStarC_Syntax_Print.showable_univ
                     u2 in
                 FStarC_Compiler_Util.format2
                   "Universe %s and %s are incompatible" uu___3 uu___4 in
               FStarC_Errors.raise_error FStarC_TypeChecker_Env.hasRange_env
                 env FStarC_Errors_Codes.Fatal_IncompatibleUniverse ()
                 (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                 (Obj.magic uu___2)) in
            let equiv v v' =
              let uu___1 =
                let uu___2 = FStarC_Syntax_Subst.compress_univ v in
                let uu___3 = FStarC_Syntax_Subst.compress_univ v' in
                (uu___2, uu___3) in
              match uu___1 with
              | (FStarC_Syntax_Syntax.U_unif v0, FStarC_Syntax_Syntax.U_unif
                 v0') -> FStarC_Syntax_Unionfind.univ_equiv v0 v0'
              | uu___2 -> false in
            let sols =
              FStarC_Compiler_CList.collect
                (fun uu___1 ->
                   (fun v ->
                      let uu___1 = FStarC_Syntax_Subst.compress_univ v in
                      match uu___1 with
                      | FStarC_Syntax_Syntax.U_unif uu___2 ->
                          Obj.magic
                            (Obj.repr
                               (let lower_bounds_of_v =
                                  FStarC_Compiler_CList.collect
                                    (fun uu___3 ->
                                       (fun uu___3 ->
                                          match uu___3 with
                                          | (u, v') ->
                                              let uu___4 = equiv v v' in
                                              if uu___4
                                              then
                                                let uu___5 =
                                                  FStarC_Compiler_CList.existsb
                                                    (equiv u) variables in
                                                (if uu___5
                                                 then
                                                   Obj.magic
                                                     (FStarC_Class_Listlike.empty
                                                        ()
                                                        (Obj.magic
                                                           (FStarC_Compiler_CList.listlike_clist
                                                              ())))
                                                 else
                                                   Obj.magic
                                                     (FStarC_Class_Listlike.cons
                                                        ()
                                                        (Obj.magic
                                                           (FStarC_Compiler_CList.listlike_clist
                                                              ())) u
                                                        (FStarC_Class_Listlike.empty
                                                           ()
                                                           (Obj.magic
                                                              (FStarC_Compiler_CList.listlike_clist
                                                                 ())))))
                                              else
                                                Obj.magic
                                                  (FStarC_Class_Listlike.empty
                                                     ()
                                                     (Obj.magic
                                                        (FStarC_Compiler_CList.listlike_clist
                                                           ())))) uu___3)
                                    ineqs in
                                let lb =
                                  let uu___3 =
                                    let uu___4 =
                                      FStarC_Class_Listlike.to_list
                                        (FStarC_Compiler_CList.listlike_clist
                                           ()) lower_bounds_of_v in
                                    FStarC_Syntax_Syntax.U_max uu___4 in
                                  FStarC_TypeChecker_Normalize.normalize_universe
                                    env uu___3 in
                                FStarC_Class_Listlike.singleton
                                  (FStarC_Compiler_CList.listlike_clist ())
                                  (lb, v)))
                      | uu___2 ->
                          Obj.magic
                            (Obj.repr
                               (FStarC_Class_Listlike.empty ()
                                  (Obj.magic
                                     (FStarC_Compiler_CList.listlike_clist ())))))
                     uu___1) variables in
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
                  repr_subcomp_allowed = (uu___2.repr_subcomp_allowed);
                  typeclass_variables = (uu___2.typeclass_variables)
                } in
              FStarC_Compiler_CList.map
                (fun uu___2 ->
                   match uu___2 with
                   | (lb, v) ->
                       let uu___3 =
                         solve_universe_eq (Prims.of_int (-1)) wl lb v in
                       (match uu___3 with
                        | USolved wl1 -> ()
                        | uu___4 -> fail lb v)) sols in
            let rec check_ineq uu___2 =
              match uu___2 with
              | (u, v) ->
                  let u1 =
                    FStarC_TypeChecker_Normalize.normalize_universe env u in
                  let v1 =
                    FStarC_TypeChecker_Normalize.normalize_universe env v in
                  (match (u1, v1) with
                   | (FStarC_Syntax_Syntax.U_zero, uu___3) -> true
                   | (FStarC_Syntax_Syntax.U_succ u0,
                      FStarC_Syntax_Syntax.U_succ v0) -> check_ineq (u0, v0)
                   | (FStarC_Syntax_Syntax.U_name u0,
                      FStarC_Syntax_Syntax.U_name v0) ->
                       FStarC_Ident.ident_equals u0 v0
                   | (FStarC_Syntax_Syntax.U_unif u0,
                      FStarC_Syntax_Syntax.U_unif v0) ->
                       FStarC_Syntax_Unionfind.univ_equiv u0 v0
                   | (FStarC_Syntax_Syntax.U_name uu___3,
                      FStarC_Syntax_Syntax.U_succ v0) -> check_ineq (u1, v0)
                   | (FStarC_Syntax_Syntax.U_unif uu___3,
                      FStarC_Syntax_Syntax.U_succ v0) -> check_ineq (u1, v0)
                   | (FStarC_Syntax_Syntax.U_max us, uu___3) ->
                       FStarC_Compiler_Util.for_all
                         (fun u2 -> check_ineq (u2, v1)) us
                   | (uu___3, FStarC_Syntax_Syntax.U_max vs) ->
                       FStarC_Compiler_Util.for_some
                         (fun v2 -> check_ineq (u1, v2)) vs
                   | uu___3 -> false) in
            let uu___2 =
              FStarC_Compiler_CList.for_all
                (fun uu___3 ->
                   match uu___3 with
                   | (u, v) ->
                       let uu___4 = check_ineq (u, v) in
                       if uu___4
                       then true
                       else
                         ((let uu___7 =
                             FStarC_Compiler_Effect.op_Bang dbg_GenUniverses in
                           if uu___7
                           then
                             let uu___8 =
                               FStarC_Class_Show.show
                                 FStarC_Syntax_Print.showable_univ u in
                             let uu___9 =
                               FStarC_Class_Show.show
                                 FStarC_Syntax_Print.showable_univ v in
                             FStarC_Compiler_Util.print2 "%s </= %s" uu___8
                               uu___9
                           else ());
                          false)) ineqs in
            if uu___2
            then ()
            else
              ((let uu___5 = FStarC_Compiler_Effect.op_Bang dbg_GenUniverses in
                if uu___5
                then
                  ((let uu___7 = ineqs_to_string (variables, ineqs) in
                    FStarC_Compiler_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu___7);
                   FStarC_Syntax_Unionfind.rollback tx;
                   (let uu___8 = ineqs_to_string (variables, ineqs) in
                    FStarC_Compiler_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu___8))
                else ());
               FStarC_Errors.raise_error FStarC_TypeChecker_Env.hasRange_env
                 env FStarC_Errors_Codes.Fatal_FailToSolveUniverseInEquality
                 () (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                 (Obj.magic
                    "Failed to solve universe inequalities for inductives"))
let (solve_universe_inequalities :
  FStarC_TypeChecker_Env.env_t ->
    (FStarC_Syntax_Syntax.universe FStarC_Compiler_CList.clist *
      (FStarC_Syntax_Syntax.universe * FStarC_Syntax_Syntax.universe)
      FStarC_Compiler_CList.clist) -> unit)
  =
  fun env ->
    fun ineqs ->
      let tx = FStarC_Syntax_Unionfind.new_transaction () in
      solve_universe_inequalities' tx env ineqs;
      FStarC_Syntax_Unionfind.commit tx
let (try_solve_deferred_constraints :
  defer_ok_t ->
    Prims.bool ->
      Prims.bool ->
        FStarC_TypeChecker_Env.env ->
          FStarC_TypeChecker_Common.guard_t ->
            FStarC_TypeChecker_Common.guard_t)
  =
  fun defer_ok ->
    fun smt_ok ->
      fun deferred_to_tac_ok ->
        fun env ->
          fun g ->
            let smt_ok1 =
              smt_ok &&
                (let uu___ = FStarC_Options.ml_ish () in
                 Prims.op_Negation uu___) in
            FStarC_Errors.with_ctx "While solving deferred constraints"
              (fun uu___ ->
                 let uu___1 =
                   let uu___2 =
                     let uu___3 = FStarC_TypeChecker_Env.current_module env in
                     FStarC_Ident.string_of_lid uu___3 in
                   FStar_Pervasives_Native.Some uu___2 in
                 FStarC_Profiling.profile
                   (fun uu___2 ->
                      let imps_l =
                        FStarC_Class_Listlike.to_list
                          (FStarC_Compiler_CList.listlike_clist ())
                          g.FStarC_TypeChecker_Common.implicits in
                      let typeclass_variables =
                        let uu___3 =
                          FStarC_Compiler_List.collect
                            (fun i ->
                               match (i.FStarC_TypeChecker_Common.imp_uvar).FStarC_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.Some
                                   (FStarC_Syntax_Syntax.Ctx_uvar_meta_tac
                                   tac) ->
                                   let uu___4 =
                                     FStarC_Syntax_Util.head_and_args_full
                                       tac in
                                   (match uu___4 with
                                    | (head, uu___5) ->
                                        let uu___6 =
                                          FStarC_Syntax_Util.is_fvar
                                            FStarC_Parser_Const.tcresolve_lid
                                            head in
                                        if uu___6
                                        then
                                          let goal_type =
                                            FStarC_Syntax_Util.ctx_uvar_typ
                                              i.FStarC_TypeChecker_Common.imp_uvar in
                                          let uvs =
                                            FStarC_Syntax_Free.uvars
                                              goal_type in
                                          FStarC_Class_Setlike.elems ()
                                            (Obj.magic
                                               (FStarC_Compiler_FlatSet.setlike_flat_set
                                                  FStarC_Syntax_Free.ord_ctx_uvar))
                                            (Obj.magic uvs)
                                        else [])
                               | uu___4 -> []) imps_l in
                        Obj.magic
                          (FStarC_Class_Setlike.from_list ()
                             (Obj.magic
                                (FStarC_Compiler_RBSet.setlike_rbset
                                   FStarC_Syntax_Free.ord_ctx_uvar)) uu___3) in
                      let wl =
                        let uu___3 =
                          let uu___4 =
                            FStarC_Class_Listlike.to_list
                              (FStarC_Compiler_CList.listlike_clist ())
                              g.FStarC_TypeChecker_Common.deferred in
                          wl_of_guard env uu___4 in
                        {
                          attempting = (uu___3.attempting);
                          wl_deferred = (uu___3.wl_deferred);
                          wl_deferred_to_tac = (uu___3.wl_deferred_to_tac);
                          ctr = (uu___3.ctr);
                          defer_ok;
                          smt_ok = smt_ok1;
                          umax_heuristic_ok = (uu___3.umax_heuristic_ok);
                          tcenv = (uu___3.tcenv);
                          wl_implicits = (uu___3.wl_implicits);
                          repr_subcomp_allowed =
                            (uu___3.repr_subcomp_allowed);
                          typeclass_variables
                        } in
                      let fail uu___3 =
                        match uu___3 with
                        | (d, s) ->
                            let msg = explain wl d s in
                            FStarC_Errors.raise_error
                              FStarC_Class_HasRange.hasRange_range (p_loc d)
                              FStarC_Errors_Codes.Fatal_ErrorInSolveDeferredConstraints
                              ()
                              (Obj.magic
                                 FStarC_Errors_Msg.is_error_message_string)
                              (Obj.magic msg) in
                      (let uu___4 = FStarC_Compiler_Effect.op_Bang dbg_Rel in
                       if uu___4
                       then
                         let uu___5 = FStarC_Class_Show.show uu___0 defer_ok in
                         let uu___6 =
                           FStarC_Class_Show.show
                             FStarC_Class_Show.showable_bool
                             deferred_to_tac_ok in
                         let uu___7 = FStarC_Class_Show.show showable_wl wl in
                         let uu___8 =
                           FStarC_Class_Show.show
                             FStarC_Class_Show.showable_nat
                             (FStarC_Compiler_List.length imps_l) in
                         FStarC_Compiler_Util.print4
                           "Trying to solve carried problems (defer_ok=%s) (deferred_to_tac_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
                           uu___5 uu___6 uu___7 uu___8
                       else ());
                      (let g1 =
                         let uu___4 = solve_and_commit wl fail in
                         match uu___4 with
                         | FStar_Pervasives_Native.Some
                             (deferred, uu___5, uu___6) when
                             (let uu___7 =
                                Obj.magic
                                  (FStarC_Class_Listlike.view ()
                                     (Obj.magic
                                        (FStarC_Compiler_CList.listlike_clist
                                           ())) (Obj.magic deferred)) in
                              FStarC_Class_Listlike.uu___is_VCons uu___7) &&
                               (defer_ok = NoDefer)
                             ->
                             failwith
                               "Impossible: Unexpected deferred constraints remain"
                         | FStar_Pervasives_Native.Some
                             (deferred, defer_to_tac, imps) ->
                             let uu___5 =
                               FStarC_Class_Monoid.op_Plus_Plus
                                 (FStarC_Compiler_CList.monoid_clist ())
                                 g.FStarC_TypeChecker_Common.deferred_to_tac
                                 defer_to_tac in
                             let uu___6 =
                               FStarC_Class_Monoid.op_Plus_Plus
                                 (FStarC_Compiler_CList.monoid_clist ())
                                 g.FStarC_TypeChecker_Common.implicits imps in
                             {
                               FStarC_TypeChecker_Common.guard_f =
                                 (g.FStarC_TypeChecker_Common.guard_f);
                               FStarC_TypeChecker_Common.deferred_to_tac =
                                 uu___5;
                               FStarC_TypeChecker_Common.deferred = deferred;
                               FStarC_TypeChecker_Common.univ_ineqs =
                                 (g.FStarC_TypeChecker_Common.univ_ineqs);
                               FStarC_TypeChecker_Common.implicits = uu___6
                             }
                         | uu___5 ->
                             failwith
                               "Impossible: should have raised a failure already" in
                       solve_universe_inequalities env
                         g1.FStarC_TypeChecker_Common.univ_ineqs;
                       (let g2 =
                          if deferred_to_tac_ok
                          then
                            let uu___5 =
                              let uu___6 =
                                let uu___7 =
                                  FStarC_TypeChecker_Env.current_module env in
                                FStarC_Ident.string_of_lid uu___7 in
                              FStar_Pervasives_Native.Some uu___6 in
                            FStarC_Profiling.profile
                              (fun uu___6 ->
                                 FStarC_TypeChecker_DeferredImplicits.solve_deferred_to_tactic_goals
                                   env g1) uu___5
                              "FStarC.TypeChecker.Rel.solve_deferred_to_tactic_goals"
                          else g1 in
                        (let uu___6 =
                           FStarC_Compiler_Effect.op_Bang
                             dbg_ResolveImplicitsHook in
                         if uu___6
                         then
                           let uu___7 = guard_to_string env g2 in
                           let uu___8 =
                             let uu___9 =
                               let uu___10 =
                                 FStarC_Class_Listlike.to_list
                                   (FStarC_Compiler_CList.listlike_clist ())
                                   g2.FStarC_TypeChecker_Common.implicits in
                               FStarC_Compiler_List.length uu___10 in
                             FStarC_Class_Show.show
                               FStarC_Class_Show.showable_nat uu___9 in
                           FStarC_Compiler_Util.print2
                             "ResolveImplicitsHook: Solved deferred to tactic goals, remaining guard is\n%s (and %s implicits)\n"
                             uu___7 uu___8
                         else ());
                        {
                          FStarC_TypeChecker_Common.guard_f =
                            (g2.FStarC_TypeChecker_Common.guard_f);
                          FStarC_TypeChecker_Common.deferred_to_tac =
                            (g2.FStarC_TypeChecker_Common.deferred_to_tac);
                          FStarC_TypeChecker_Common.deferred =
                            (g2.FStarC_TypeChecker_Common.deferred);
                          FStarC_TypeChecker_Common.univ_ineqs =
                            ((Obj.magic
                                (FStarC_Class_Listlike.empty ()
                                   (Obj.magic
                                      (FStarC_Compiler_CList.listlike_clist
                                         ())))),
                              (Obj.magic
                                 (FStarC_Class_Listlike.empty ()
                                    (Obj.magic
                                       (FStarC_Compiler_CList.listlike_clist
                                          ())))));
                          FStarC_TypeChecker_Common.implicits =
                            (g2.FStarC_TypeChecker_Common.implicits)
                        }))) uu___1
                   "FStarC.TypeChecker.Rel.try_solve_deferred_constraints")
let (solve_deferred_constraints :
  FStarC_TypeChecker_Env.env ->
    FStarC_TypeChecker_Common.guard_t -> FStarC_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun g ->
      let defer_ok = NoDefer in
      let smt_ok =
        let uu___ = FStarC_Options.ml_ish () in Prims.op_Negation uu___ in
      let deferred_to_tac_ok = true in
      try_solve_deferred_constraints defer_ok smt_ok deferred_to_tac_ok env g
let (solve_non_tactic_deferred_constraints :
  Prims.bool ->
    FStarC_TypeChecker_Env.env ->
      FStarC_TypeChecker_Common.guard_t -> FStarC_TypeChecker_Common.guard_t)
  =
  fun maybe_defer_flex_flex ->
    fun env ->
      fun g ->
        FStarC_Errors.with_ctx "solve_non_tactic_deferred_constraints"
          (fun uu___ ->
             FStarC_Defensive.def_check_scoped
               FStarC_TypeChecker_Env.hasBinders_env
               FStarC_TypeChecker_Env.hasNames_guard
               FStarC_TypeChecker_Env.pretty_guard
               FStarC_Compiler_Range_Type.dummyRange
               "solve_non_tactic_deferred_constraints.g" env g;
             (let defer_ok =
                if maybe_defer_flex_flex then DeferFlexFlexOnly else NoDefer in
              let smt_ok =
                let uu___2 = FStarC_Options.ml_ish () in
                Prims.op_Negation uu___2 in
              let deferred_to_tac_ok = false in
              try_solve_deferred_constraints defer_ok smt_ok
                deferred_to_tac_ok env g))
let (do_discharge_vc :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStarC_TypeChecker_Env.env -> FStarC_TypeChecker_Env.goal -> unit)
  =
  fun use_env_range_msg ->
    fun env ->
      fun vc ->
        let debug =
          ((FStarC_Compiler_Effect.op_Bang dbg_Rel) ||
             (FStarC_Compiler_Effect.op_Bang dbg_SMTQuery))
            || (FStarC_Compiler_Effect.op_Bang dbg_Discharge) in
        let diag uu___1 uu___ =
          (let uu___ = FStarC_TypeChecker_Env.get_range env in
           Obj.magic
             (FStarC_Errors.diag FStarC_Class_HasRange.hasRange_range uu___
                ())) uu___1 uu___ in
        if debug
        then
          (let uu___1 =
             let uu___2 =
               let uu___3 = FStarC_Errors_Msg.text "Checking VC:" in
               let uu___4 =
                 FStarC_Class_PP.pp FStarC_Syntax_Print.pretty_term vc in
               FStarC_Pprint.op_Hat_Slash_Hat uu___3 uu___4 in
             [uu___2] in
           diag FStarC_Errors_Msg.is_error_message_list_doc uu___1)
        else ();
        (let vcs =
           let uu___1 = FStarC_Options.use_tactics () in
           if uu___1
           then
             FStarC_Options.with_saved_options
               (fun uu___2 ->
                  (let uu___4 = FStarC_Options.set_options "--no_tactics" in
                   ());
                  (let uu___4 =
                     (env.FStarC_TypeChecker_Env.solver).FStarC_TypeChecker_Env.preprocess
                       env vc in
                   match uu___4 with
                   | (did_anything, vcs1) ->
                       (if debug && did_anything
                        then
                          (let uu___6 =
                             let uu___7 =
                               let uu___8 =
                                 FStarC_Errors_Msg.text
                                   "Tactic preprocessing produced" in
                               let uu___9 =
                                 let uu___10 =
                                   FStarC_Class_PP.pp FStarC_Class_PP.pp_int
                                     (FStarC_Compiler_List.length vcs1) in
                                 let uu___11 = FStarC_Errors_Msg.text "goals" in
                                 FStarC_Pprint.op_Hat_Slash_Hat uu___10
                                   uu___11 in
                               FStarC_Pprint.op_Hat_Slash_Hat uu___8 uu___9 in
                             [uu___7] in
                           diag FStarC_Errors_Msg.is_error_message_list_doc
                             uu___6)
                        else ();
                        (let vcs2 =
                           FStarC_Compiler_List.map
                             (fun uu___6 ->
                                match uu___6 with
                                | (env1, goal, opts) ->
                                    let uu___7 =
                                      norm_with_steps
                                        "FStarC.TypeChecker.Rel.norm_with_steps.7"
                                        [FStarC_TypeChecker_Env.Simplify;
                                        FStarC_TypeChecker_Env.Primops;
                                        FStarC_TypeChecker_Env.Exclude
                                          FStarC_TypeChecker_Env.Zeta] env1
                                        goal in
                                    (env1, uu___7, opts)) vcs1 in
                         let vcs3 =
                           FStarC_Compiler_List.concatMap
                             (fun uu___6 ->
                                match uu___6 with
                                | (env1, goal, opts) ->
                                    let uu___7 =
                                      (env1.FStarC_TypeChecker_Env.solver).FStarC_TypeChecker_Env.handle_smt_goal
                                        env1 goal in
                                    FStarC_Compiler_List.map
                                      (fun uu___8 ->
                                         match uu___8 with
                                         | (env2, goal1) ->
                                             (env2, goal1, opts)) uu___7)
                             vcs2 in
                         let vcs4 =
                           FStarC_Compiler_List.concatMap
                             (fun uu___6 ->
                                match uu___6 with
                                | (env1, goal, opts) ->
                                    let uu___7 =
                                      FStarC_TypeChecker_Common.check_trivial
                                        goal in
                                    (match uu___7 with
                                     | FStarC_TypeChecker_Common.Trivial ->
                                         (if debug
                                          then
                                            (let uu___9 =
                                               let uu___10 =
                                                 FStarC_Errors_Msg.text
                                                   "Goal completely solved by tactic\n" in
                                               [uu___10] in
                                             diag
                                               FStarC_Errors_Msg.is_error_message_list_doc
                                               uu___9)
                                          else ();
                                          [])
                                     | FStarC_TypeChecker_Common.NonTrivial
                                         goal1 -> [(env1, goal1, opts)]))
                             vcs3 in
                         vcs4))))
           else
             (let uu___3 =
                let uu___4 = FStarC_Options.peek () in (env, vc, uu___4) in
              [uu___3]) in
         let vcs1 =
           let uu___1 =
             let uu___2 = FStarC_Options.split_queries () in
             uu___2 = FStarC_Options.Always in
           if uu___1
           then
             FStarC_Compiler_List.collect
               (fun uu___2 ->
                  match uu___2 with
                  | (env1, goal, opts) ->
                      let uu___3 =
                        FStarC_TypeChecker_Env.split_smt_query env1 goal in
                      (match uu___3 with
                       | FStar_Pervasives_Native.None -> [(env1, goal, opts)]
                       | FStar_Pervasives_Native.Some goals ->
                           FStarC_Compiler_List.map
                             (fun uu___4 ->
                                match uu___4 with
                                | (env2, goal1) -> (env2, goal1, opts)) goals))
               vcs
           else vcs in
         FStarC_Compiler_List.iter
           (fun uu___1 ->
              match uu___1 with
              | (env1, goal, opts) ->
                  FStarC_Options.with_saved_options
                    (fun uu___2 ->
                       FStarC_Options.set opts;
                       if debug
                       then
                         (let uu___5 =
                            let uu___6 =
                              let uu___7 =
                                FStarC_Errors_Msg.text
                                  "Before calling solver, VC =" in
                              let uu___8 =
                                FStarC_Class_PP.pp
                                  FStarC_Syntax_Print.pretty_term goal in
                              FStarC_Pprint.op_Hat_Slash_Hat uu___7 uu___8 in
                            [uu___6] in
                          diag FStarC_Errors_Msg.is_error_message_list_doc
                            uu___5)
                       else ();
                       (env1.FStarC_TypeChecker_Env.solver).FStarC_TypeChecker_Env.solve
                         use_env_range_msg env1 goal)) vcs1)
let (discharge_guard' :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStarC_TypeChecker_Env.env ->
      FStarC_TypeChecker_Common.guard_t ->
        Prims.bool ->
          FStarC_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun use_env_range_msg ->
    fun env ->
      fun g ->
        fun use_smt ->
          (let uu___1 =
             FStarC_Compiler_Effect.op_Bang dbg_ResolveImplicitsHook in
           if uu___1
           then
             let uu___2 = guard_to_string env g in
             FStarC_Compiler_Util.print1
               "///////////////////ResolveImplicitsHook: discharge_guard'\nguard = %s\n"
               uu___2
           else ());
          (let g1 =
             let defer_ok = NoDefer in
             let smt_ok =
               (let uu___1 = FStarC_Options.ml_ish () in
                Prims.op_Negation uu___1) && use_smt in
             let deferred_to_tac_ok = true in
             try_solve_deferred_constraints defer_ok smt_ok
               deferred_to_tac_ok env g in
           let debug =
             ((FStarC_Compiler_Effect.op_Bang dbg_Rel) ||
                (FStarC_Compiler_Effect.op_Bang dbg_SMTQuery))
               || (FStarC_Compiler_Effect.op_Bang dbg_Discharge) in
           let diag uu___2 uu___1 =
             (let uu___1 = FStarC_TypeChecker_Env.get_range env in
              Obj.magic
                (FStarC_Errors.diag FStarC_Class_HasRange.hasRange_range
                   uu___1 ())) uu___2 uu___1 in
           let ret_g =
             {
               FStarC_TypeChecker_Common.guard_f =
                 FStarC_TypeChecker_Common.Trivial;
               FStarC_TypeChecker_Common.deferred_to_tac =
                 (g1.FStarC_TypeChecker_Common.deferred_to_tac);
               FStarC_TypeChecker_Common.deferred =
                 (g1.FStarC_TypeChecker_Common.deferred);
               FStarC_TypeChecker_Common.univ_ineqs =
                 (g1.FStarC_TypeChecker_Common.univ_ineqs);
               FStarC_TypeChecker_Common.implicits =
                 (g1.FStarC_TypeChecker_Common.implicits)
             } in
           if env.FStarC_TypeChecker_Env.admit
           then
             (if
                (debug &&
                   (Prims.op_Negation
                      (FStarC_TypeChecker_Common.uu___is_Trivial
                         g1.FStarC_TypeChecker_Common.guard_f)))
                  && (Prims.op_Negation env.FStarC_TypeChecker_Env.phase1)
              then
                (let uu___2 =
                   let uu___3 =
                     FStarC_Errors_Msg.text
                       "Skipping VC because verification is disabled." in
                   let uu___4 =
                     let uu___5 =
                       let uu___6 = FStarC_Errors_Msg.text "VC =" in
                       let uu___7 =
                         FStarC_Class_PP.pp
                           FStarC_TypeChecker_Env.pretty_guard g1 in
                       FStarC_Pprint.op_Hat_Slash_Hat uu___6 uu___7 in
                     [uu___5] in
                   uu___3 :: uu___4 in
                 diag FStarC_Errors_Msg.is_error_message_list_doc uu___2)
              else ();
              FStar_Pervasives_Native.Some ret_g)
           else
             (let g2 = simplify_guard_full_norm env g1 in
              match g2.FStarC_TypeChecker_Common.guard_f with
              | FStarC_TypeChecker_Common.Trivial ->
                  FStar_Pervasives_Native.Some ret_g
              | FStarC_TypeChecker_Common.NonTrivial vc when
                  Prims.op_Negation use_smt ->
                  (if debug
                   then
                     (let uu___3 =
                        let uu___4 =
                          let uu___5 =
                            FStarC_Errors_Msg.text
                              "Cannot solve without SMT:" in
                          let uu___6 =
                            FStarC_Class_PP.pp
                              FStarC_Syntax_Print.pretty_term vc in
                          FStarC_Pprint.op_Hat_Slash_Hat uu___5 uu___6 in
                        [uu___4] in
                      diag FStarC_Errors_Msg.is_error_message_list_doc uu___3)
                   else ();
                   FStar_Pervasives_Native.None)
              | FStarC_TypeChecker_Common.NonTrivial vc ->
                  (do_discharge_vc use_env_range_msg env vc;
                   FStar_Pervasives_Native.Some ret_g)))
let (discharge_guard :
  FStarC_TypeChecker_Env.env ->
    FStarC_TypeChecker_Common.guard_t -> FStarC_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun g ->
      let uu___ = discharge_guard' FStar_Pervasives_Native.None env g true in
      match uu___ with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
let (discharge_guard_no_smt :
  FStarC_TypeChecker_Env.env ->
    FStarC_TypeChecker_Common.guard_t -> FStarC_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun g ->
      let uu___ = discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu___ with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None ->
          let uu___1 =
            let uu___2 =
              FStarC_Errors_Msg.text "Expected a trivial pre-condition" in
            [uu___2] in
          FStarC_Errors.raise_error FStarC_TypeChecker_Env.hasRange_env env
            FStarC_Errors_Codes.Fatal_ExpectTrivialPreCondition ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
            (Obj.magic uu___1)
let (teq_nosmt :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.typ ->
      FStarC_Syntax_Syntax.typ ->
        FStarC_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
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
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.typ ->
      FStarC_Syntax_Syntax.typ ->
        FStarC_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        (let uu___1 =
           (FStarC_Compiler_Effect.op_Bang dbg_Rel) ||
             (FStarC_Compiler_Effect.op_Bang dbg_RelTop) in
         if uu___1
         then
           let uu___2 = FStarC_TypeChecker_Normalize.term_to_string env t1 in
           let uu___3 = FStarC_TypeChecker_Normalize.term_to_string env t2 in
           FStarC_Compiler_Util.print2 "try_subtype_no_smt of %s and %s\n"
             uu___2 uu___3
         else ());
        (let uu___1 =
           let uu___2 = empty_worklist env in
           new_t_prob uu___2 env t1 FStarC_TypeChecker_Common.SUB t2 in
         match uu___1 with
         | (prob, x, wl) ->
             let g =
               let uu___2 =
                 solve_and_commit (singleton wl prob false)
                   (fun uu___3 -> FStar_Pervasives_Native.None) in
               with_guard env prob uu___2 in
             (match g with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu___2 =
                      let uu___3 = FStarC_Syntax_Syntax.mk_binder x in
                      [uu___3] in
                    FStarC_TypeChecker_Env.close_guard env uu___2 g1 in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
let (check_subtyping :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
      FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
        (FStarC_Syntax_Syntax.bv * FStarC_TypeChecker_Common.guard_t)
          FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStarC_TypeChecker_Env.current_module env in
            FStarC_Ident.string_of_lid uu___2 in
          FStar_Pervasives_Native.Some uu___1 in
        FStarC_Profiling.profile
          (fun uu___1 ->
             (let uu___3 =
                (FStarC_Compiler_Effect.op_Bang dbg_Rel) ||
                  (FStarC_Compiler_Effect.op_Bang dbg_RelTop) in
              if uu___3
              then
                let uu___4 =
                  FStarC_TypeChecker_Normalize.term_to_string env t1 in
                let uu___5 =
                  FStarC_TypeChecker_Normalize.term_to_string env t2 in
                FStarC_Compiler_Util.print2 "check_subtyping of %s and %s\n"
                  uu___4 uu___5
              else ());
             (let uu___3 =
                let uu___4 = empty_worklist env in
                new_t_prob uu___4 env t1 FStarC_TypeChecker_Common.SUB t2 in
              match uu___3 with
              | (prob, x, wl) ->
                  let env_x = FStarC_TypeChecker_Env.push_bv env x in
                  let smt_ok =
                    let uu___4 = FStarC_Options.ml_ish () in
                    Prims.op_Negation uu___4 in
                  let g =
                    let uu___4 =
                      solve_and_commit (singleton wl prob smt_ok)
                        (fun uu___5 -> FStar_Pervasives_Native.None) in
                    with_guard env_x prob uu___4 in
                  (match g with
                   | FStar_Pervasives_Native.None ->
                       ((let uu___5 =
                           (FStarC_Compiler_Effect.op_Bang dbg_Rel) ||
                             (FStarC_Compiler_Effect.op_Bang dbg_RelTop) in
                         if uu___5
                         then
                           let uu___6 =
                             FStarC_TypeChecker_Normalize.term_to_string
                               env_x t1 in
                           let uu___7 =
                             FStarC_TypeChecker_Normalize.term_to_string
                               env_x t2 in
                           FStarC_Compiler_Util.print2
                             "check_subtyping FAILED: %s <: %s\n" uu___6
                             uu___7
                         else ());
                        FStar_Pervasives_Native.None)
                   | FStar_Pervasives_Native.Some g1 ->
                       ((let uu___5 =
                           (FStarC_Compiler_Effect.op_Bang dbg_Rel) ||
                             (FStarC_Compiler_Effect.op_Bang dbg_RelTop) in
                         if uu___5
                         then
                           let uu___6 =
                             FStarC_TypeChecker_Normalize.term_to_string
                               env_x t1 in
                           let uu___7 =
                             FStarC_TypeChecker_Normalize.term_to_string
                               env_x t2 in
                           let uu___8 = guard_to_string env_x g1 in
                           FStarC_Compiler_Util.print3
                             "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                             uu___6 uu___7 uu___8
                         else ());
                        FStar_Pervasives_Native.Some (x, g1))))) uu___
          "FStarC.TypeChecker.Rel.check_subtyping"
let (get_subtyping_predicate :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.typ ->
      FStarC_Syntax_Syntax.typ ->
        FStarC_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        FStarC_Errors.with_ctx "While trying to get a subtyping predicate"
          (fun uu___ ->
             FStarC_Defensive.def_check_scoped
               FStarC_TypeChecker_Env.hasBinders_env
               FStarC_Class_Binders.hasNames_term
               FStarC_Syntax_Print.pretty_term t1.FStarC_Syntax_Syntax.pos
               "get_subtyping_predicate.1" env t1;
             FStarC_Defensive.def_check_scoped
               FStarC_TypeChecker_Env.hasBinders_env
               FStarC_Class_Binders.hasNames_term
               FStarC_Syntax_Print.pretty_term t2.FStarC_Syntax_Syntax.pos
               "get_subtyping_predicate.2" env t2;
             (let uu___3 = check_subtyping env t1 t2 in
              match uu___3 with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some (x, g) ->
                  let uu___4 =
                    let uu___5 = FStarC_Syntax_Syntax.mk_binder x in
                    FStarC_TypeChecker_Env.abstract_guard uu___5 g in
                  FStar_Pervasives_Native.Some uu___4))
let (get_subtyping_prop :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.typ ->
      FStarC_Syntax_Syntax.typ ->
        FStarC_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        FStarC_Errors.with_ctx "While trying to get a subtyping proposition"
          (fun uu___ ->
             FStarC_Defensive.def_check_scoped
               FStarC_TypeChecker_Env.hasBinders_env
               FStarC_Class_Binders.hasNames_term
               FStarC_Syntax_Print.pretty_term t1.FStarC_Syntax_Syntax.pos
               "get_subtyping_prop.1" env t1;
             FStarC_Defensive.def_check_scoped
               FStarC_TypeChecker_Env.hasBinders_env
               FStarC_Class_Binders.hasNames_term
               FStarC_Syntax_Print.pretty_term t2.FStarC_Syntax_Syntax.pos
               "get_subtyping_prop.2" env t2;
             (let uu___3 = check_subtyping env t1 t2 in
              match uu___3 with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some (x, g) ->
                  let uu___4 =
                    let uu___5 =
                      let uu___6 = FStarC_Syntax_Syntax.mk_binder x in
                      [uu___6] in
                    FStarC_TypeChecker_Env.close_guard env uu___5 g in
                  FStar_Pervasives_Native.Some uu___4))
let (try_solve_single_valued_implicits :
  FStarC_TypeChecker_Env.env ->
    Prims.bool ->
      FStarC_TypeChecker_Env.implicits ->
        (FStarC_TypeChecker_Env.implicits * Prims.bool))
  =
  fun env ->
    fun is_tac ->
      fun imps ->
        if is_tac
        then (imps, false)
        else
          (let imp_value imp =
             let uu___1 =
               ((imp.FStarC_TypeChecker_Common.imp_uvar),
                 (imp.FStarC_TypeChecker_Common.imp_range)) in
             match uu___1 with
             | (ctx_u, r) ->
                 let t_norm =
                   let uu___2 = FStarC_Syntax_Util.ctx_uvar_typ ctx_u in
                   FStarC_TypeChecker_Normalize.normalize
                     FStarC_TypeChecker_Normalize.whnf_steps env uu___2 in
                 let uu___2 =
                   let uu___3 = FStarC_Syntax_Subst.compress t_norm in
                   uu___3.FStarC_Syntax_Syntax.n in
                 (match uu___2 with
                  | FStarC_Syntax_Syntax.Tm_fvar fv when
                      FStarC_Syntax_Syntax.fv_eq_lid fv
                        FStarC_Parser_Const.unit_lid
                      ->
                      let uu___3 =
                        FStarC_Syntax_Syntax.unit_const_with_range r in
                      FStar_Pervasives_Native.Some uu___3
                  | FStarC_Syntax_Syntax.Tm_refine
                      { FStarC_Syntax_Syntax.b = b;
                        FStarC_Syntax_Syntax.phi = uu___3;_}
                      when
                      FStarC_Syntax_Util.is_unit b.FStarC_Syntax_Syntax.sort
                      ->
                      let uu___4 =
                        FStarC_Syntax_Syntax.unit_const_with_range r in
                      FStar_Pervasives_Native.Some uu___4
                  | uu___3 -> FStar_Pervasives_Native.None) in
           let b =
             FStarC_Compiler_List.fold_left
               (fun b1 ->
                  fun imp ->
                    let uu___1 =
                      (let uu___2 =
                         FStarC_Syntax_Unionfind.find
                           (imp.FStarC_TypeChecker_Common.imp_uvar).FStarC_Syntax_Syntax.ctx_uvar_head in
                       FStarC_Compiler_Util.is_none uu___2) &&
                        (let uu___2 =
                           FStarC_Syntax_Util.ctx_uvar_should_check
                             imp.FStarC_TypeChecker_Common.imp_uvar in
                         uu___2 = FStarC_Syntax_Syntax.Strict) in
                    if uu___1
                    then
                      let uu___2 = imp_value imp in
                      match uu___2 with
                      | FStar_Pervasives_Native.Some tm ->
                          (commit env
                             [TERM
                                ((imp.FStarC_TypeChecker_Common.imp_uvar),
                                  tm)];
                           true)
                      | FStar_Pervasives_Native.None -> b1
                    else b1) false imps in
           (imps, b))
let (check_implicit_solution_and_discharge_guard :
  FStarC_TypeChecker_Env.env ->
    FStarC_TypeChecker_Common.implicit ->
      Prims.bool ->
        Prims.bool ->
          FStarC_TypeChecker_Common.implicits_t
            FStar_Pervasives_Native.option)
  =
  fun env ->
    fun imp ->
      fun is_tac ->
        fun force_univ_constraints ->
          let uu___ = imp in
          match uu___ with
          | { FStarC_TypeChecker_Common.imp_reason = imp_reason;
              FStarC_TypeChecker_Common.imp_uvar = imp_uvar;
              FStarC_TypeChecker_Common.imp_tm = imp_tm;
              FStarC_TypeChecker_Common.imp_range = imp_range;_} ->
              let uvar_ty = FStarC_Syntax_Util.ctx_uvar_typ imp_uvar in
              let uvar_should_check =
                FStarC_Syntax_Util.ctx_uvar_should_check imp_uvar in
              ((let uu___2 = FStarC_Compiler_Effect.op_Bang dbg_Rel in
                if uu___2
                then
                  let uu___3 =
                    FStarC_Class_Show.show FStarC_Syntax_Print.showable_uvar
                      imp_uvar.FStarC_Syntax_Syntax.ctx_uvar_head in
                  let uu___4 =
                    FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                      imp_tm in
                  let uu___5 =
                    FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                      uvar_ty in
                  let uu___6 =
                    FStarC_Compiler_Range_Ops.string_of_range imp_range in
                  FStarC_Compiler_Util.print5
                    "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                    uu___3 uu___4 uu___5 imp_reason uu___6
                else ());
               (let env1 =
                  let uu___2 =
                    FStarC_TypeChecker_Env.clear_expected_typ
                      {
                        FStarC_TypeChecker_Env.solver =
                          (env.FStarC_TypeChecker_Env.solver);
                        FStarC_TypeChecker_Env.range =
                          (env.FStarC_TypeChecker_Env.range);
                        FStarC_TypeChecker_Env.curmodule =
                          (env.FStarC_TypeChecker_Env.curmodule);
                        FStarC_TypeChecker_Env.gamma =
                          (imp_uvar.FStarC_Syntax_Syntax.ctx_uvar_gamma);
                        FStarC_TypeChecker_Env.gamma_sig =
                          (env.FStarC_TypeChecker_Env.gamma_sig);
                        FStarC_TypeChecker_Env.gamma_cache =
                          (env.FStarC_TypeChecker_Env.gamma_cache);
                        FStarC_TypeChecker_Env.modules =
                          (env.FStarC_TypeChecker_Env.modules);
                        FStarC_TypeChecker_Env.expected_typ =
                          (env.FStarC_TypeChecker_Env.expected_typ);
                        FStarC_TypeChecker_Env.sigtab =
                          (env.FStarC_TypeChecker_Env.sigtab);
                        FStarC_TypeChecker_Env.attrtab =
                          (env.FStarC_TypeChecker_Env.attrtab);
                        FStarC_TypeChecker_Env.instantiate_imp =
                          (env.FStarC_TypeChecker_Env.instantiate_imp);
                        FStarC_TypeChecker_Env.effects =
                          (env.FStarC_TypeChecker_Env.effects);
                        FStarC_TypeChecker_Env.generalize =
                          (env.FStarC_TypeChecker_Env.generalize);
                        FStarC_TypeChecker_Env.letrecs =
                          (env.FStarC_TypeChecker_Env.letrecs);
                        FStarC_TypeChecker_Env.top_level =
                          (env.FStarC_TypeChecker_Env.top_level);
                        FStarC_TypeChecker_Env.check_uvars =
                          (env.FStarC_TypeChecker_Env.check_uvars);
                        FStarC_TypeChecker_Env.use_eq_strict =
                          (env.FStarC_TypeChecker_Env.use_eq_strict);
                        FStarC_TypeChecker_Env.is_iface =
                          (env.FStarC_TypeChecker_Env.is_iface);
                        FStarC_TypeChecker_Env.admit =
                          (env.FStarC_TypeChecker_Env.admit);
                        FStarC_TypeChecker_Env.lax_universes =
                          (env.FStarC_TypeChecker_Env.lax_universes);
                        FStarC_TypeChecker_Env.phase1 =
                          (env.FStarC_TypeChecker_Env.phase1);
                        FStarC_TypeChecker_Env.failhard =
                          (env.FStarC_TypeChecker_Env.failhard);
                        FStarC_TypeChecker_Env.flychecking =
                          (env.FStarC_TypeChecker_Env.flychecking);
                        FStarC_TypeChecker_Env.uvar_subtyping =
                          (env.FStarC_TypeChecker_Env.uvar_subtyping);
                        FStarC_TypeChecker_Env.intactics =
                          (env.FStarC_TypeChecker_Env.intactics);
                        FStarC_TypeChecker_Env.nocoerce =
                          (env.FStarC_TypeChecker_Env.nocoerce);
                        FStarC_TypeChecker_Env.tc_term =
                          (env.FStarC_TypeChecker_Env.tc_term);
                        FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
                          (env.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                        FStarC_TypeChecker_Env.universe_of =
                          (env.FStarC_TypeChecker_Env.universe_of);
                        FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                          =
                          (env.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                        FStarC_TypeChecker_Env.teq_nosmt_force =
                          (env.FStarC_TypeChecker_Env.teq_nosmt_force);
                        FStarC_TypeChecker_Env.subtype_nosmt_force =
                          (env.FStarC_TypeChecker_Env.subtype_nosmt_force);
                        FStarC_TypeChecker_Env.qtbl_name_and_index =
                          (env.FStarC_TypeChecker_Env.qtbl_name_and_index);
                        FStarC_TypeChecker_Env.normalized_eff_names =
                          (env.FStarC_TypeChecker_Env.normalized_eff_names);
                        FStarC_TypeChecker_Env.fv_delta_depths =
                          (env.FStarC_TypeChecker_Env.fv_delta_depths);
                        FStarC_TypeChecker_Env.proof_ns =
                          (env.FStarC_TypeChecker_Env.proof_ns);
                        FStarC_TypeChecker_Env.synth_hook =
                          (env.FStarC_TypeChecker_Env.synth_hook);
                        FStarC_TypeChecker_Env.try_solve_implicits_hook =
                          (env.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                        FStarC_TypeChecker_Env.splice =
                          (env.FStarC_TypeChecker_Env.splice);
                        FStarC_TypeChecker_Env.mpreprocess =
                          (env.FStarC_TypeChecker_Env.mpreprocess);
                        FStarC_TypeChecker_Env.postprocess =
                          (env.FStarC_TypeChecker_Env.postprocess);
                        FStarC_TypeChecker_Env.identifier_info =
                          (env.FStarC_TypeChecker_Env.identifier_info);
                        FStarC_TypeChecker_Env.tc_hooks =
                          (env.FStarC_TypeChecker_Env.tc_hooks);
                        FStarC_TypeChecker_Env.dsenv =
                          (env.FStarC_TypeChecker_Env.dsenv);
                        FStarC_TypeChecker_Env.nbe =
                          (env.FStarC_TypeChecker_Env.nbe);
                        FStarC_TypeChecker_Env.strict_args_tab =
                          (env.FStarC_TypeChecker_Env.strict_args_tab);
                        FStarC_TypeChecker_Env.erasable_types_tab =
                          (env.FStarC_TypeChecker_Env.erasable_types_tab);
                        FStarC_TypeChecker_Env.enable_defer_to_tac =
                          (env.FStarC_TypeChecker_Env.enable_defer_to_tac);
                        FStarC_TypeChecker_Env.unif_allow_ref_guards =
                          (env.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                        FStarC_TypeChecker_Env.erase_erasable_args =
                          (env.FStarC_TypeChecker_Env.erase_erasable_args);
                        FStarC_TypeChecker_Env.core_check =
                          (env.FStarC_TypeChecker_Env.core_check);
                        FStarC_TypeChecker_Env.missing_decl =
                          (env.FStarC_TypeChecker_Env.missing_decl)
                      } in
                  FStar_Pervasives_Native.fst uu___2 in
                let g =
                  FStarC_Errors.with_ctx "While checking implicit solution"
                    (fun uu___2 ->
                       let skip_core =
                         ((env1.FStarC_TypeChecker_Env.phase1 ||
                             env1.FStarC_TypeChecker_Env.admit)
                            ||
                            (FStarC_Syntax_Syntax.uu___is_Allow_untyped
                               uvar_should_check))
                           ||
                           (FStarC_Syntax_Syntax.uu___is_Already_checked
                              uvar_should_check) in
                       let must_tot =
                         Prims.op_Negation
                           ((env1.FStarC_TypeChecker_Env.phase1 ||
                               env1.FStarC_TypeChecker_Env.admit)
                              ||
                              (FStarC_Syntax_Syntax.uu___is_Allow_ghost
                                 uvar_should_check)) in
                       if skip_core
                       then
                         (if is_tac
                          then FStarC_TypeChecker_Env.trivial_guard
                          else
                            (let imp_tm1 =
                               let uu___4 =
                                 let uu___5 =
                                   FStarC_Syntax_Subst.compress imp_tm in
                                 uu___5.FStarC_Syntax_Syntax.n in
                               match uu___4 with
                               | FStarC_Syntax_Syntax.Tm_abs
                                   { FStarC_Syntax_Syntax.bs = bs;
                                     FStarC_Syntax_Syntax.body = body;
                                     FStarC_Syntax_Syntax.rc_opt =
                                       FStar_Pervasives_Native.Some rc;_}
                                   ->
                                   {
                                     FStarC_Syntax_Syntax.n =
                                       (FStarC_Syntax_Syntax.Tm_abs
                                          {
                                            FStarC_Syntax_Syntax.bs = bs;
                                            FStarC_Syntax_Syntax.body = body;
                                            FStarC_Syntax_Syntax.rc_opt =
                                              (FStar_Pervasives_Native.Some
                                                 {
                                                   FStarC_Syntax_Syntax.residual_effect
                                                     =
                                                     (rc.FStarC_Syntax_Syntax.residual_effect);
                                                   FStarC_Syntax_Syntax.residual_typ
                                                     =
                                                     FStar_Pervasives_Native.None;
                                                   FStarC_Syntax_Syntax.residual_flags
                                                     =
                                                     (rc.FStarC_Syntax_Syntax.residual_flags)
                                                 })
                                          });
                                     FStarC_Syntax_Syntax.pos =
                                       (imp_tm.FStarC_Syntax_Syntax.pos);
                                     FStarC_Syntax_Syntax.vars =
                                       (imp_tm.FStarC_Syntax_Syntax.vars);
                                     FStarC_Syntax_Syntax.hash_code =
                                       (imp_tm.FStarC_Syntax_Syntax.hash_code)
                                   }
                               | uu___5 -> imp_tm in
                             let uu___4 =
                               env1.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                 env1 imp_tm1 must_tot in
                             match uu___4 with
                             | (k', g1) ->
                                 let uu___5 =
                                   get_subtyping_predicate env1 k' uvar_ty in
                                 (match uu___5 with
                                  | FStar_Pervasives_Native.None ->
                                      FStarC_TypeChecker_Err.expected_expression_of_type
                                        env1 imp_tm1.FStarC_Syntax_Syntax.pos
                                        uvar_ty imp_tm1 k'
                                  | FStar_Pervasives_Native.Some f ->
                                      let uu___6 =
                                        let uu___7 =
                                          FStarC_TypeChecker_Env.apply_guard
                                            f imp_tm1 in
                                        FStarC_TypeChecker_Env.conj_guard
                                          uu___7 g1 in
                                      {
                                        FStarC_TypeChecker_Common.guard_f =
                                          FStarC_TypeChecker_Common.Trivial;
                                        FStarC_TypeChecker_Common.deferred_to_tac
                                          =
                                          (uu___6.FStarC_TypeChecker_Common.deferred_to_tac);
                                        FStarC_TypeChecker_Common.deferred =
                                          (uu___6.FStarC_TypeChecker_Common.deferred);
                                        FStarC_TypeChecker_Common.univ_ineqs
                                          =
                                          (uu___6.FStarC_TypeChecker_Common.univ_ineqs);
                                        FStarC_TypeChecker_Common.implicits =
                                          (uu___6.FStarC_TypeChecker_Common.implicits)
                                      })))
                       else
                         (let uu___4 =
                            env1.FStarC_TypeChecker_Env.core_check env1
                              imp_tm uvar_ty must_tot in
                          match uu___4 with
                          | FStar_Pervasives.Inl
                              (FStar_Pervasives_Native.None) ->
                              FStarC_TypeChecker_Common.trivial_guard
                          | FStar_Pervasives.Inl
                              (FStar_Pervasives_Native.Some g1) ->
                              {
                                FStarC_TypeChecker_Common.guard_f =
                                  (FStarC_TypeChecker_Common.NonTrivial g1);
                                FStarC_TypeChecker_Common.deferred_to_tac =
                                  (FStarC_TypeChecker_Common.trivial_guard.FStarC_TypeChecker_Common.deferred_to_tac);
                                FStarC_TypeChecker_Common.deferred =
                                  (FStarC_TypeChecker_Common.trivial_guard.FStarC_TypeChecker_Common.deferred);
                                FStarC_TypeChecker_Common.univ_ineqs =
                                  (FStarC_TypeChecker_Common.trivial_guard.FStarC_TypeChecker_Common.univ_ineqs);
                                FStarC_TypeChecker_Common.implicits =
                                  (FStarC_TypeChecker_Common.trivial_guard.FStarC_TypeChecker_Common.implicits)
                              }
                          | FStar_Pervasives.Inr print_err ->
                              let uu___5 =
                                let uu___6 =
                                  FStarC_Class_Show.show
                                    FStarC_Syntax_Print.showable_ctxu
                                    imp_uvar in
                                let uu___7 =
                                  FStarC_Class_Show.show
                                    FStarC_Class_Show.showable_bool is_tac in
                                let uu___8 =
                                  FStarC_Class_Show.show
                                    FStarC_Syntax_Print.showable_term imp_tm in
                                let uu___9 =
                                  FStarC_Class_Show.show
                                    FStarC_Syntax_Print.showable_term uvar_ty in
                                FStarC_Compiler_Util.format5
                                  "Core checking failed for implicit %s (is_tac: %s) (reason: %s) (%s <: %s)"
                                  uu___6 uu___7 imp_reason uu___8 uu___9 in
                              FStarC_Errors.raise_error
                                FStarC_Class_HasRange.hasRange_range
                                imp_range
                                FStarC_Errors_Codes.Fatal_FailToResolveImplicitArgument
                                ()
                                (Obj.magic
                                   FStarC_Errors_Msg.is_error_message_string)
                                (Obj.magic uu___5))) in
                let uu___2 =
                  (Prims.op_Negation force_univ_constraints) &&
                    (FStarC_Compiler_CList.existsb
                       (fun uu___3 ->
                          match uu___3 with
                          | (reason, uu___4, uu___5) ->
                              reason =
                                FStarC_TypeChecker_Common.Deferred_univ_constraint)
                       g.FStarC_TypeChecker_Common.deferred) in
                if uu___2
                then FStar_Pervasives_Native.None
                else
                  (let g' =
                     let uu___4 =
                       discharge_guard'
                         (FStar_Pervasives_Native.Some
                            (fun uu___5 ->
                               let uu___6 =
                                 FStarC_Class_Show.show
                                   FStarC_Syntax_Print.showable_term imp_tm in
                               let uu___7 =
                                 FStarC_Class_Show.show
                                   FStarC_Compiler_Range_Ops.showable_range
                                   imp_range in
                               let uu___8 =
                                 FStarC_Class_Show.show
                                   FStarC_Compiler_Range_Ops.showable_range
                                   imp_tm.FStarC_Syntax_Syntax.pos in
                               FStarC_Compiler_Util.format4
                                 "%s (Introduced at %s for %s resolved at %s)"
                                 uu___6 uu___7 imp_reason uu___8)) env1 g
                         true in
                     match uu___4 with
                     | FStar_Pervasives_Native.Some g1 -> g1
                     | FStar_Pervasives_Native.None ->
                         failwith
                           "Impossible, with use_smt = true, discharge_guard' must return Some" in
                   FStar_Pervasives_Native.Some
                     (g'.FStarC_TypeChecker_Common.implicits))))
let rec (unresolved : FStarC_Syntax_Syntax.ctx_uvar -> Prims.bool) =
  fun ctx_u ->
    let uu___ =
      FStarC_Syntax_Unionfind.find ctx_u.FStarC_Syntax_Syntax.ctx_uvar_head in
    match uu___ with
    | FStar_Pervasives_Native.Some r ->
        (match ctx_u.FStarC_Syntax_Syntax.ctx_uvar_meta with
         | FStar_Pervasives_Native.None -> false
         | FStar_Pervasives_Native.Some uu___1 ->
             let uu___2 =
               let uu___3 = FStarC_Syntax_Subst.compress r in
               uu___3.FStarC_Syntax_Syntax.n in
             (match uu___2 with
              | FStarC_Syntax_Syntax.Tm_uvar (ctx_u', uu___3) ->
                  unresolved ctx_u'
              | uu___3 -> false))
    | FStar_Pervasives_Native.None -> true
let (pick_a_univ_deffered_implicit :
  tagged_implicits ->
    (FStarC_TypeChecker_Env.implicit FStar_Pervasives_Native.option *
      tagged_implicits))
  =
  fun out ->
    let uu___ =
      FStarC_Compiler_List.partition
        (fun uu___1 ->
           match uu___1 with
           | (uu___2, status) ->
               status = Implicit_checking_defers_univ_constraint) out in
    match uu___ with
    | (imps_with_deferred_univs, rest) ->
        (match imps_with_deferred_univs with
         | [] -> (FStar_Pervasives_Native.None, out)
         | hd::tl ->
             ((FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst hd)),
               (FStarC_Compiler_List.op_At tl rest)))
let (is_tac_implicit_resolved :
  FStarC_TypeChecker_Env.env ->
    FStarC_TypeChecker_Common.implicit -> Prims.bool)
  =
  fun env ->
    fun i ->
      let uu___ = FStarC_Syntax_Free.uvars i.FStarC_TypeChecker_Common.imp_tm in
      FStarC_Class_Setlike.for_all ()
        (Obj.magic
           (FStarC_Compiler_FlatSet.setlike_flat_set
              FStarC_Syntax_Free.ord_ctx_uvar))
        (fun uv ->
           let uu___1 = FStarC_Syntax_Util.ctx_uvar_should_check uv in
           FStarC_Syntax_Syntax.uu___is_Allow_unresolved uu___1)
        (Obj.magic uu___)
let (resolve_implicits' :
  FStarC_TypeChecker_Env.env ->
    Prims.bool ->
      Prims.bool ->
        FStarC_TypeChecker_Env.implicits ->
          (FStarC_TypeChecker_Common.implicit * implicit_checking_status)
            Prims.list)
  =
  fun env ->
    fun is_tac ->
      fun is_gen ->
        fun implicits ->
          let cacheable tac =
            (FStarC_Syntax_Util.is_fvar FStarC_Parser_Const.tcresolve_lid tac)
              ||
              (let uu___ =
                 let uu___1 = FStarC_Syntax_Subst.compress tac in
                 uu___1.FStarC_Syntax_Syntax.n in
               match uu___ with
               | FStarC_Syntax_Syntax.Tm_abs
                   { FStarC_Syntax_Syntax.bs = uu___1::[];
                     FStarC_Syntax_Syntax.body = body;
                     FStarC_Syntax_Syntax.rc_opt = uu___2;_}
                   ->
                   let uu___3 = FStarC_Syntax_Util.head_and_args body in
                   (match uu___3 with
                    | (hd, args) ->
                        (FStarC_Syntax_Util.is_fvar
                           FStarC_Parser_Const.tcresolve_lid hd)
                          &&
                          ((FStarC_Compiler_List.length args) = Prims.int_one))
               | uu___1 -> false) in
          let meta_tac_allowed_for_open_problem tac = cacheable tac in
          let __meta_arg_cache = FStarC_Compiler_Util.mk_ref [] in
          let meta_arg_cache_result tac e ty res =
            let uu___ =
              let uu___1 = FStarC_Compiler_Effect.op_Bang __meta_arg_cache in
              (tac, e, ty, res) :: uu___1 in
            FStarC_Compiler_Effect.op_Colon_Equals __meta_arg_cache uu___ in
          let meta_arg_cache_lookup tac e ty =
            let rec aux l =
              match l with
              | [] -> FStar_Pervasives_Native.None
              | (tac', e', ty', res')::l' ->
                  let uu___ =
                    ((FStarC_Syntax_Util.term_eq tac tac') &&
                       (FStarC_Common.eq_list FStarC_Syntax_Util.eq_binding
                          e.FStarC_TypeChecker_Env.gamma
                          e'.FStarC_TypeChecker_Env.gamma))
                      && (FStarC_Syntax_Util.term_eq ty ty') in
                  if uu___ then FStar_Pervasives_Native.Some res' else aux l' in
            let uu___ = FStarC_Compiler_Effect.op_Bang __meta_arg_cache in
            aux uu___ in
          let rec until_fixpoint acc implicits1 =
            let uu___ = acc in
            match uu___ with
            | (out, changed, defer_open_metas) ->
                (match implicits1 with
                 | [] ->
                     if changed
                     then
                       let uu___1 =
                         FStarC_Compiler_List.map FStar_Pervasives_Native.fst
                           out in
                       until_fixpoint ([], false, true) uu___1
                     else
                       if defer_open_metas
                       then
                         (let uu___2 =
                            FStarC_Compiler_List.map
                              FStar_Pervasives_Native.fst out in
                          until_fixpoint ([], false, false) uu___2)
                       else
                         (let uu___3 =
                            let uu___4 =
                              FStarC_Compiler_List.map
                                FStar_Pervasives_Native.fst out in
                            try_solve_single_valued_implicits env is_tac
                              uu___4 in
                          match uu___3 with
                          | (imps, changed1) ->
                              if changed1
                              then until_fixpoint ([], false, true) imps
                              else
                                (let uu___5 =
                                   pick_a_univ_deffered_implicit out in
                                 match uu___5 with
                                 | (imp_opt, rest) ->
                                     (match imp_opt with
                                      | FStar_Pervasives_Native.None -> rest
                                      | FStar_Pervasives_Native.Some imp ->
                                          let force_univ_constraints = true in
                                          let imps1 =
                                            let uu___6 =
                                              check_implicit_solution_and_discharge_guard
                                                env imp is_tac
                                                force_univ_constraints in
                                            FStarC_Compiler_Util.must uu___6 in
                                          let uu___6 =
                                            let uu___7 =
                                              FStarC_Class_Listlike.to_list
                                                (FStarC_Compiler_CList.listlike_clist
                                                   ()) imps1 in
                                            let uu___8 =
                                              FStarC_Compiler_List.map
                                                FStar_Pervasives_Native.fst
                                                rest in
                                            FStarC_Class_Monoid.op_Plus_Plus
                                              (FStarC_Class_Monoid.monoid_list
                                                 ()) uu___7 uu___8 in
                                          until_fixpoint ([], false, true)
                                            uu___6)))
                 | hd::tl ->
                     let uu___1 = hd in
                     (match uu___1 with
                      | { FStarC_TypeChecker_Common.imp_reason = reason;
                          FStarC_TypeChecker_Common.imp_uvar = ctx_u;
                          FStarC_TypeChecker_Common.imp_tm = tm;
                          FStarC_TypeChecker_Common.imp_range = r;_} ->
                          let uu___2 =
                            FStarC_Syntax_Unionfind.find_decoration
                              ctx_u.FStarC_Syntax_Syntax.ctx_uvar_head in
                          (match uu___2 with
                           | {
                               FStarC_Syntax_Syntax.uvar_decoration_typ =
                                 uvar_decoration_typ;
                               FStarC_Syntax_Syntax.uvar_decoration_typedness_depends_on
                                 = uu___3;
                               FStarC_Syntax_Syntax.uvar_decoration_should_check
                                 = uvar_decoration_should_check;
                               FStarC_Syntax_Syntax.uvar_decoration_should_unrefine
                                 = uu___4;_}
                               ->
                               ((let uu___6 =
                                   FStarC_Compiler_Effect.op_Bang dbg_Rel in
                                 if uu___6
                                 then
                                   let uu___7 =
                                     FStarC_Class_Show.show
                                       FStarC_Syntax_Print.showable_term tm in
                                   let uu___8 =
                                     FStarC_Class_Show.show
                                       FStarC_Syntax_Print.showable_ctxu
                                       ctx_u in
                                   let uu___9 =
                                     FStarC_Class_Show.show
                                       FStarC_Class_Show.showable_bool is_tac in
                                   let uu___10 =
                                     FStarC_Class_Show.show
                                       FStarC_Syntax_Syntax.showable_should_check_uvar
                                       uvar_decoration_should_check in
                                   FStarC_Compiler_Util.print4
                                     "resolve_implicits' loop, imp_tm=%s and ctx_u=%s, is_tac=%s, should_check=%s\n"
                                     uu___7 uu___8 uu___9 uu___10
                                 else ());
                                if
                                  FStarC_Syntax_Syntax.uu___is_Allow_unresolved
                                    uvar_decoration_should_check
                                then
                                  until_fixpoint
                                    (out, true, defer_open_metas) tl
                                else
                                  if
                                    (unresolved ctx_u) &&
                                      (flex_uvar_has_meta_tac ctx_u)
                                  then
                                    (let uu___6 =
                                       ctx_u.FStarC_Syntax_Syntax.ctx_uvar_meta in
                                     match uu___6 with
                                     | FStar_Pervasives_Native.Some
                                         (FStarC_Syntax_Syntax.Ctx_uvar_meta_tac
                                         tac) ->
                                         let env1 =
                                           {
                                             FStarC_TypeChecker_Env.solver =
                                               (env.FStarC_TypeChecker_Env.solver);
                                             FStarC_TypeChecker_Env.range =
                                               (env.FStarC_TypeChecker_Env.range);
                                             FStarC_TypeChecker_Env.curmodule
                                               =
                                               (env.FStarC_TypeChecker_Env.curmodule);
                                             FStarC_TypeChecker_Env.gamma =
                                               (ctx_u.FStarC_Syntax_Syntax.ctx_uvar_gamma);
                                             FStarC_TypeChecker_Env.gamma_sig
                                               =
                                               (env.FStarC_TypeChecker_Env.gamma_sig);
                                             FStarC_TypeChecker_Env.gamma_cache
                                               =
                                               (env.FStarC_TypeChecker_Env.gamma_cache);
                                             FStarC_TypeChecker_Env.modules =
                                               (env.FStarC_TypeChecker_Env.modules);
                                             FStarC_TypeChecker_Env.expected_typ
                                               =
                                               (env.FStarC_TypeChecker_Env.expected_typ);
                                             FStarC_TypeChecker_Env.sigtab =
                                               (env.FStarC_TypeChecker_Env.sigtab);
                                             FStarC_TypeChecker_Env.attrtab =
                                               (env.FStarC_TypeChecker_Env.attrtab);
                                             FStarC_TypeChecker_Env.instantiate_imp
                                               =
                                               (env.FStarC_TypeChecker_Env.instantiate_imp);
                                             FStarC_TypeChecker_Env.effects =
                                               (env.FStarC_TypeChecker_Env.effects);
                                             FStarC_TypeChecker_Env.generalize
                                               =
                                               (env.FStarC_TypeChecker_Env.generalize);
                                             FStarC_TypeChecker_Env.letrecs =
                                               (env.FStarC_TypeChecker_Env.letrecs);
                                             FStarC_TypeChecker_Env.top_level
                                               =
                                               (env.FStarC_TypeChecker_Env.top_level);
                                             FStarC_TypeChecker_Env.check_uvars
                                               =
                                               (env.FStarC_TypeChecker_Env.check_uvars);
                                             FStarC_TypeChecker_Env.use_eq_strict
                                               =
                                               (env.FStarC_TypeChecker_Env.use_eq_strict);
                                             FStarC_TypeChecker_Env.is_iface
                                               =
                                               (env.FStarC_TypeChecker_Env.is_iface);
                                             FStarC_TypeChecker_Env.admit =
                                               (env.FStarC_TypeChecker_Env.admit);
                                             FStarC_TypeChecker_Env.lax_universes
                                               =
                                               (env.FStarC_TypeChecker_Env.lax_universes);
                                             FStarC_TypeChecker_Env.phase1 =
                                               (env.FStarC_TypeChecker_Env.phase1);
                                             FStarC_TypeChecker_Env.failhard
                                               =
                                               (env.FStarC_TypeChecker_Env.failhard);
                                             FStarC_TypeChecker_Env.flychecking
                                               =
                                               (env.FStarC_TypeChecker_Env.flychecking);
                                             FStarC_TypeChecker_Env.uvar_subtyping
                                               =
                                               (env.FStarC_TypeChecker_Env.uvar_subtyping);
                                             FStarC_TypeChecker_Env.intactics
                                               =
                                               (env.FStarC_TypeChecker_Env.intactics);
                                             FStarC_TypeChecker_Env.nocoerce
                                               =
                                               (env.FStarC_TypeChecker_Env.nocoerce);
                                             FStarC_TypeChecker_Env.tc_term =
                                               (env.FStarC_TypeChecker_Env.tc_term);
                                             FStarC_TypeChecker_Env.typeof_tot_or_gtot_term
                                               =
                                               (env.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                                             FStarC_TypeChecker_Env.universe_of
                                               =
                                               (env.FStarC_TypeChecker_Env.universe_of);
                                             FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                               =
                                               (env.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                             FStarC_TypeChecker_Env.teq_nosmt_force
                                               =
                                               (env.FStarC_TypeChecker_Env.teq_nosmt_force);
                                             FStarC_TypeChecker_Env.subtype_nosmt_force
                                               =
                                               (env.FStarC_TypeChecker_Env.subtype_nosmt_force);
                                             FStarC_TypeChecker_Env.qtbl_name_and_index
                                               =
                                               (env.FStarC_TypeChecker_Env.qtbl_name_and_index);
                                             FStarC_TypeChecker_Env.normalized_eff_names
                                               =
                                               (env.FStarC_TypeChecker_Env.normalized_eff_names);
                                             FStarC_TypeChecker_Env.fv_delta_depths
                                               =
                                               (env.FStarC_TypeChecker_Env.fv_delta_depths);
                                             FStarC_TypeChecker_Env.proof_ns
                                               =
                                               (env.FStarC_TypeChecker_Env.proof_ns);
                                             FStarC_TypeChecker_Env.synth_hook
                                               =
                                               (env.FStarC_TypeChecker_Env.synth_hook);
                                             FStarC_TypeChecker_Env.try_solve_implicits_hook
                                               =
                                               (env.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                                             FStarC_TypeChecker_Env.splice =
                                               (env.FStarC_TypeChecker_Env.splice);
                                             FStarC_TypeChecker_Env.mpreprocess
                                               =
                                               (env.FStarC_TypeChecker_Env.mpreprocess);
                                             FStarC_TypeChecker_Env.postprocess
                                               =
                                               (env.FStarC_TypeChecker_Env.postprocess);
                                             FStarC_TypeChecker_Env.identifier_info
                                               =
                                               (env.FStarC_TypeChecker_Env.identifier_info);
                                             FStarC_TypeChecker_Env.tc_hooks
                                               =
                                               (env.FStarC_TypeChecker_Env.tc_hooks);
                                             FStarC_TypeChecker_Env.dsenv =
                                               (env.FStarC_TypeChecker_Env.dsenv);
                                             FStarC_TypeChecker_Env.nbe =
                                               (env.FStarC_TypeChecker_Env.nbe);
                                             FStarC_TypeChecker_Env.strict_args_tab
                                               =
                                               (env.FStarC_TypeChecker_Env.strict_args_tab);
                                             FStarC_TypeChecker_Env.erasable_types_tab
                                               =
                                               (env.FStarC_TypeChecker_Env.erasable_types_tab);
                                             FStarC_TypeChecker_Env.enable_defer_to_tac
                                               =
                                               (env.FStarC_TypeChecker_Env.enable_defer_to_tac);
                                             FStarC_TypeChecker_Env.unif_allow_ref_guards
                                               =
                                               (env.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                                             FStarC_TypeChecker_Env.erase_erasable_args
                                               =
                                               (env.FStarC_TypeChecker_Env.erase_erasable_args);
                                             FStarC_TypeChecker_Env.core_check
                                               =
                                               (env.FStarC_TypeChecker_Env.core_check);
                                             FStarC_TypeChecker_Env.missing_decl
                                               =
                                               (env.FStarC_TypeChecker_Env.missing_decl)
                                           } in
                                         let typ =
                                           FStarC_Syntax_Util.ctx_uvar_typ
                                             ctx_u in
                                         let is_open =
                                           (has_free_uvars typ) ||
                                             (gamma_has_free_uvars
                                                ctx_u.FStarC_Syntax_Syntax.ctx_uvar_gamma) in
                                         if defer_open_metas && is_open
                                         then
                                           ((let uu___8 =
                                               (FStarC_Compiler_Effect.op_Bang
                                                  dbg_Rel)
                                                 ||
                                                 (FStarC_Compiler_Effect.op_Bang
                                                    dbg_Imps) in
                                             if uu___8
                                             then
                                               let uu___9 =
                                                 FStarC_Class_Show.show
                                                   FStarC_Syntax_Print.showable_ctxu
                                                   ctx_u in
                                               FStarC_Compiler_Util.print1
                                                 "Deferring implicit due to open ctx/typ %s\n"
                                                 uu___9
                                             else ());
                                            until_fixpoint
                                              (((hd, Implicit_unresolved) ::
                                                out), changed,
                                                defer_open_metas) tl)
                                         else
                                           (let uu___8 =
                                              (is_open &&
                                                 (let uu___9 =
                                                    meta_tac_allowed_for_open_problem
                                                      tac in
                                                  Prims.op_Negation uu___9))
                                                &&
                                                (let uu___9 =
                                                   FStarC_Options_Ext.get
                                                     "compat:open_metas" in
                                                 uu___9 = "") in
                                            if uu___8
                                            then
                                              until_fixpoint
                                                (((hd, Implicit_unresolved)
                                                  :: out), changed,
                                                  defer_open_metas) tl
                                            else
                                              (let solve_with t =
                                                 let extra =
                                                   let uu___10 =
                                                     teq_nosmt env1 t tm in
                                                   match uu___10 with
                                                   | FStar_Pervasives_Native.None
                                                       ->
                                                       failwith
                                                         "resolve_implicits: unifying with an unresolved uvar failed?"
                                                   | FStar_Pervasives_Native.Some
                                                       g ->
                                                       FStarC_Class_Listlike.to_list
                                                         (FStarC_Compiler_CList.listlike_clist
                                                            ())
                                                         g.FStarC_TypeChecker_Common.implicits in
                                                 until_fixpoint
                                                   (out, true,
                                                     defer_open_metas)
                                                   (FStarC_Compiler_List.op_At
                                                      extra tl) in
                                               let uu___10 = cacheable tac in
                                               if uu___10
                                               then
                                                 let uu___11 =
                                                   meta_arg_cache_lookup tac
                                                     env1 typ in
                                                 match uu___11 with
                                                 | FStar_Pervasives_Native.Some
                                                     res -> solve_with res
                                                 | FStar_Pervasives_Native.None
                                                     ->
                                                     let t =
                                                       run_meta_arg_tac env1
                                                         ctx_u in
                                                     (meta_arg_cache_result
                                                        tac env1 typ t;
                                                      solve_with t)
                                               else
                                                 (let t =
                                                    run_meta_arg_tac env1
                                                      ctx_u in
                                                  solve_with t))))
                                  else
                                    if unresolved ctx_u
                                    then
                                      until_fixpoint
                                        (((hd, Implicit_unresolved) :: out),
                                          changed, defer_open_metas) tl
                                    else
                                      if
                                        ((FStarC_Syntax_Syntax.uu___is_Allow_untyped
                                            uvar_decoration_should_check)
                                           ||
                                           (FStarC_Syntax_Syntax.uu___is_Already_checked
                                              uvar_decoration_should_check))
                                          || is_gen
                                      then
                                        until_fixpoint
                                          (out, true, defer_open_metas) tl
                                      else
                                        (let env1 =
                                           {
                                             FStarC_TypeChecker_Env.solver =
                                               (env.FStarC_TypeChecker_Env.solver);
                                             FStarC_TypeChecker_Env.range =
                                               (env.FStarC_TypeChecker_Env.range);
                                             FStarC_TypeChecker_Env.curmodule
                                               =
                                               (env.FStarC_TypeChecker_Env.curmodule);
                                             FStarC_TypeChecker_Env.gamma =
                                               (ctx_u.FStarC_Syntax_Syntax.ctx_uvar_gamma);
                                             FStarC_TypeChecker_Env.gamma_sig
                                               =
                                               (env.FStarC_TypeChecker_Env.gamma_sig);
                                             FStarC_TypeChecker_Env.gamma_cache
                                               =
                                               (env.FStarC_TypeChecker_Env.gamma_cache);
                                             FStarC_TypeChecker_Env.modules =
                                               (env.FStarC_TypeChecker_Env.modules);
                                             FStarC_TypeChecker_Env.expected_typ
                                               =
                                               (env.FStarC_TypeChecker_Env.expected_typ);
                                             FStarC_TypeChecker_Env.sigtab =
                                               (env.FStarC_TypeChecker_Env.sigtab);
                                             FStarC_TypeChecker_Env.attrtab =
                                               (env.FStarC_TypeChecker_Env.attrtab);
                                             FStarC_TypeChecker_Env.instantiate_imp
                                               =
                                               (env.FStarC_TypeChecker_Env.instantiate_imp);
                                             FStarC_TypeChecker_Env.effects =
                                               (env.FStarC_TypeChecker_Env.effects);
                                             FStarC_TypeChecker_Env.generalize
                                               =
                                               (env.FStarC_TypeChecker_Env.generalize);
                                             FStarC_TypeChecker_Env.letrecs =
                                               (env.FStarC_TypeChecker_Env.letrecs);
                                             FStarC_TypeChecker_Env.top_level
                                               =
                                               (env.FStarC_TypeChecker_Env.top_level);
                                             FStarC_TypeChecker_Env.check_uvars
                                               =
                                               (env.FStarC_TypeChecker_Env.check_uvars);
                                             FStarC_TypeChecker_Env.use_eq_strict
                                               =
                                               (env.FStarC_TypeChecker_Env.use_eq_strict);
                                             FStarC_TypeChecker_Env.is_iface
                                               =
                                               (env.FStarC_TypeChecker_Env.is_iface);
                                             FStarC_TypeChecker_Env.admit =
                                               (env.FStarC_TypeChecker_Env.admit);
                                             FStarC_TypeChecker_Env.lax_universes
                                               =
                                               (env.FStarC_TypeChecker_Env.lax_universes);
                                             FStarC_TypeChecker_Env.phase1 =
                                               (env.FStarC_TypeChecker_Env.phase1);
                                             FStarC_TypeChecker_Env.failhard
                                               =
                                               (env.FStarC_TypeChecker_Env.failhard);
                                             FStarC_TypeChecker_Env.flychecking
                                               =
                                               (env.FStarC_TypeChecker_Env.flychecking);
                                             FStarC_TypeChecker_Env.uvar_subtyping
                                               =
                                               (env.FStarC_TypeChecker_Env.uvar_subtyping);
                                             FStarC_TypeChecker_Env.intactics
                                               =
                                               (env.FStarC_TypeChecker_Env.intactics);
                                             FStarC_TypeChecker_Env.nocoerce
                                               =
                                               (env.FStarC_TypeChecker_Env.nocoerce);
                                             FStarC_TypeChecker_Env.tc_term =
                                               (env.FStarC_TypeChecker_Env.tc_term);
                                             FStarC_TypeChecker_Env.typeof_tot_or_gtot_term
                                               =
                                               (env.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                                             FStarC_TypeChecker_Env.universe_of
                                               =
                                               (env.FStarC_TypeChecker_Env.universe_of);
                                             FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                               =
                                               (env.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                             FStarC_TypeChecker_Env.teq_nosmt_force
                                               =
                                               (env.FStarC_TypeChecker_Env.teq_nosmt_force);
                                             FStarC_TypeChecker_Env.subtype_nosmt_force
                                               =
                                               (env.FStarC_TypeChecker_Env.subtype_nosmt_force);
                                             FStarC_TypeChecker_Env.qtbl_name_and_index
                                               =
                                               (env.FStarC_TypeChecker_Env.qtbl_name_and_index);
                                             FStarC_TypeChecker_Env.normalized_eff_names
                                               =
                                               (env.FStarC_TypeChecker_Env.normalized_eff_names);
                                             FStarC_TypeChecker_Env.fv_delta_depths
                                               =
                                               (env.FStarC_TypeChecker_Env.fv_delta_depths);
                                             FStarC_TypeChecker_Env.proof_ns
                                               =
                                               (env.FStarC_TypeChecker_Env.proof_ns);
                                             FStarC_TypeChecker_Env.synth_hook
                                               =
                                               (env.FStarC_TypeChecker_Env.synth_hook);
                                             FStarC_TypeChecker_Env.try_solve_implicits_hook
                                               =
                                               (env.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                                             FStarC_TypeChecker_Env.splice =
                                               (env.FStarC_TypeChecker_Env.splice);
                                             FStarC_TypeChecker_Env.mpreprocess
                                               =
                                               (env.FStarC_TypeChecker_Env.mpreprocess);
                                             FStarC_TypeChecker_Env.postprocess
                                               =
                                               (env.FStarC_TypeChecker_Env.postprocess);
                                             FStarC_TypeChecker_Env.identifier_info
                                               =
                                               (env.FStarC_TypeChecker_Env.identifier_info);
                                             FStarC_TypeChecker_Env.tc_hooks
                                               =
                                               (env.FStarC_TypeChecker_Env.tc_hooks);
                                             FStarC_TypeChecker_Env.dsenv =
                                               (env.FStarC_TypeChecker_Env.dsenv);
                                             FStarC_TypeChecker_Env.nbe =
                                               (env.FStarC_TypeChecker_Env.nbe);
                                             FStarC_TypeChecker_Env.strict_args_tab
                                               =
                                               (env.FStarC_TypeChecker_Env.strict_args_tab);
                                             FStarC_TypeChecker_Env.erasable_types_tab
                                               =
                                               (env.FStarC_TypeChecker_Env.erasable_types_tab);
                                             FStarC_TypeChecker_Env.enable_defer_to_tac
                                               =
                                               (env.FStarC_TypeChecker_Env.enable_defer_to_tac);
                                             FStarC_TypeChecker_Env.unif_allow_ref_guards
                                               =
                                               (env.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                                             FStarC_TypeChecker_Env.erase_erasable_args
                                               =
                                               (env.FStarC_TypeChecker_Env.erase_erasable_args);
                                             FStarC_TypeChecker_Env.core_check
                                               =
                                               (env.FStarC_TypeChecker_Env.core_check);
                                             FStarC_TypeChecker_Env.missing_decl
                                               =
                                               (env.FStarC_TypeChecker_Env.missing_decl)
                                           } in
                                         let tm1 =
                                           norm_with_steps
                                             "FStarC.TypeChecker.Rel.norm_with_steps.8"
                                             [FStarC_TypeChecker_Env.Beta]
                                             env1 tm in
                                         let hd1 =
                                           {
                                             FStarC_TypeChecker_Common.imp_reason
                                               =
                                               (hd.FStarC_TypeChecker_Common.imp_reason);
                                             FStarC_TypeChecker_Common.imp_uvar
                                               =
                                               (hd.FStarC_TypeChecker_Common.imp_uvar);
                                             FStarC_TypeChecker_Common.imp_tm
                                               = tm1;
                                             FStarC_TypeChecker_Common.imp_range
                                               =
                                               (hd.FStarC_TypeChecker_Common.imp_range)
                                           } in
                                         if is_tac
                                         then
                                           ((let uu___7 =
                                               is_tac_implicit_resolved env1
                                                 hd1 in
                                             if uu___7
                                             then
                                               let force_univ_constraints =
                                                 true in
                                               let res =
                                                 check_implicit_solution_and_discharge_guard
                                                   env1 hd1 is_tac
                                                   force_univ_constraints in
                                               let res1 =
                                                 FStarC_Compiler_Util.map_opt
                                                   res
                                                   (FStarC_Class_Listlike.to_list
                                                      (FStarC_Compiler_CList.listlike_clist
                                                         ())) in
                                               (if
                                                  res1 <>
                                                    (FStar_Pervasives_Native.Some
                                                       [])
                                                then
                                                  failwith
                                                    "Impossible: check_implicit_solution_and_discharge_guard for tac must return Some []"
                                                else ())
                                             else ());
                                            until_fixpoint
                                              (out, true, defer_open_metas)
                                              tl)
                                         else
                                           (let force_univ_constraints =
                                              false in
                                            let imps_opt =
                                              check_implicit_solution_and_discharge_guard
                                                env1 hd1 is_tac
                                                force_univ_constraints in
                                            match imps_opt with
                                            | FStar_Pervasives_Native.None ->
                                                until_fixpoint
                                                  (((hd1,
                                                      Implicit_checking_defers_univ_constraint)
                                                    :: out), changed,
                                                    defer_open_metas) tl
                                            | FStar_Pervasives_Native.Some
                                                imps ->
                                                let uu___7 =
                                                  let uu___8 =
                                                    let uu___9 =
                                                      let uu___10 =
                                                        FStarC_Class_Listlike.to_list
                                                          (FStarC_Compiler_CList.listlike_clist
                                                             ()) imps in
                                                      FStarC_Compiler_List.map
                                                        (fun i ->
                                                           (i,
                                                             Implicit_unresolved))
                                                        uu___10 in
                                                    FStarC_Compiler_List.op_At
                                                      uu___9 out in
                                                  (uu___8, true,
                                                    defer_open_metas) in
                                                until_fixpoint uu___7 tl)))))) in
          until_fixpoint ([], false, true) implicits
let (resolve_implicits :
  FStarC_TypeChecker_Env.env ->
    FStarC_TypeChecker_Common.guard_t -> FStarC_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun g ->
      (let uu___1 = FStarC_Compiler_Effect.op_Bang dbg_ResolveImplicitsHook in
       if uu___1
       then
         let uu___2 = guard_to_string env g in
         FStarC_Compiler_Util.print1
           "//////////////////////////ResolveImplicitsHook: resolve_implicits begin////////////\nguard = %s {\n"
           uu___2
       else ());
      (let tagged_implicits1 =
         let uu___1 =
           FStarC_Class_Listlike.to_list
             (FStarC_Compiler_CList.listlike_clist ())
             g.FStarC_TypeChecker_Common.implicits in
         resolve_implicits' env false false uu___1 in
       (let uu___2 = FStarC_Compiler_Effect.op_Bang dbg_ResolveImplicitsHook in
        if uu___2
        then
          FStarC_Compiler_Util.print_string
            "//////////////////////////ResolveImplicitsHook: resolve_implicits end////////////\n}\n"
        else ());
       (let uu___2 =
          let uu___3 =
            FStarC_Compiler_List.map FStar_Pervasives_Native.fst
              tagged_implicits1 in
          FStarC_Class_Listlike.from_list
            (FStarC_Compiler_CList.listlike_clist ()) uu___3 in
        {
          FStarC_TypeChecker_Common.guard_f =
            (g.FStarC_TypeChecker_Common.guard_f);
          FStarC_TypeChecker_Common.deferred_to_tac =
            (g.FStarC_TypeChecker_Common.deferred_to_tac);
          FStarC_TypeChecker_Common.deferred =
            (g.FStarC_TypeChecker_Common.deferred);
          FStarC_TypeChecker_Common.univ_ineqs =
            (g.FStarC_TypeChecker_Common.univ_ineqs);
          FStarC_TypeChecker_Common.implicits = uu___2
        }))
let (resolve_generalization_implicits :
  FStarC_TypeChecker_Env.env ->
    FStarC_TypeChecker_Common.guard_t -> FStarC_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun g ->
      let tagged_implicits1 =
        let uu___ =
          FStarC_Class_Listlike.to_list
            (FStarC_Compiler_CList.listlike_clist ())
            g.FStarC_TypeChecker_Common.implicits in
        resolve_implicits' env false true uu___ in
      let uu___ =
        let uu___1 =
          FStarC_Compiler_List.map FStar_Pervasives_Native.fst
            tagged_implicits1 in
        FStarC_Class_Listlike.from_list
          (FStarC_Compiler_CList.listlike_clist ()) uu___1 in
      {
        FStarC_TypeChecker_Common.guard_f =
          (g.FStarC_TypeChecker_Common.guard_f);
        FStarC_TypeChecker_Common.deferred_to_tac =
          (g.FStarC_TypeChecker_Common.deferred_to_tac);
        FStarC_TypeChecker_Common.deferred =
          (g.FStarC_TypeChecker_Common.deferred);
        FStarC_TypeChecker_Common.univ_ineqs =
          (g.FStarC_TypeChecker_Common.univ_ineqs);
        FStarC_TypeChecker_Common.implicits = uu___
      }
let (resolve_implicits_tac :
  FStarC_TypeChecker_Env.env ->
    FStarC_TypeChecker_Common.guard_t -> tagged_implicits)
  =
  fun env ->
    fun g ->
      let uu___ =
        FStarC_Class_Listlike.to_list
          (FStarC_Compiler_CList.listlike_clist ())
          g.FStarC_TypeChecker_Common.implicits in
      resolve_implicits' env true false uu___
let (force_trivial_guard :
  FStarC_TypeChecker_Env.env -> FStarC_TypeChecker_Common.guard_t -> unit) =
  fun env ->
    fun g ->
      (let uu___1 = FStarC_Compiler_Effect.op_Bang dbg_ResolveImplicitsHook in
       if uu___1
       then
         let uu___2 = guard_to_string env g in
         FStarC_Compiler_Util.print1
           "//////////////////////////ResolveImplicitsHook: force_trivial_guard////////////\nguard = %s\n"
           uu___2
       else ());
      (let g1 = solve_deferred_constraints env g in
       let g2 = resolve_implicits env g1 in
       let uu___1 =
         FStarC_Class_Listlike.to_list
           (FStarC_Compiler_CList.listlike_clist ())
           g2.FStarC_TypeChecker_Common.implicits in
       match uu___1 with
       | [] -> let uu___2 = discharge_guard env g2 in ()
       | imp::uu___2 ->
           let uu___3 =
             let uu___4 =
               let uu___5 =
                 let uu___6 =
                   FStarC_Errors_Msg.text
                     "Failed to resolve implicit argument" in
                 let uu___7 =
                   let uu___8 =
                     FStarC_Class_Show.show FStarC_Syntax_Print.showable_uvar
                       (imp.FStarC_TypeChecker_Common.imp_uvar).FStarC_Syntax_Syntax.ctx_uvar_head in
                   FStarC_Pprint.arbitrary_string uu___8 in
                 FStarC_Pprint.prefix (Prims.of_int (4)) Prims.int_one uu___6
                   uu___7 in
               let uu___6 =
                 let uu___7 =
                   let uu___8 = FStarC_Errors_Msg.text "of type" in
                   let uu___9 =
                     let uu___10 =
                       FStarC_Syntax_Util.ctx_uvar_typ
                         imp.FStarC_TypeChecker_Common.imp_uvar in
                     FStarC_TypeChecker_Normalize.term_to_doc env uu___10 in
                   FStarC_Pprint.prefix (Prims.of_int (4)) Prims.int_one
                     uu___8 uu___9 in
                 let uu___8 =
                   let uu___9 = FStarC_Errors_Msg.text "introduced for" in
                   let uu___10 =
                     FStarC_Errors_Msg.text
                       imp.FStarC_TypeChecker_Common.imp_reason in
                   FStarC_Pprint.prefix (Prims.of_int (4)) Prims.int_one
                     uu___9 uu___10 in
                 FStarC_Pprint.op_Hat_Slash_Hat uu___7 uu___8 in
               FStarC_Pprint.op_Hat_Slash_Hat uu___5 uu___6 in
             [uu___4] in
           FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range
             imp.FStarC_TypeChecker_Common.imp_range
             FStarC_Errors_Codes.Fatal_FailToResolveImplicitArgument ()
             (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
             (Obj.magic uu___3))
let (subtype_nosmt_force :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.typ -> FStarC_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu___ = subtype_nosmt env t1 t2 in
        match uu___ with
        | FStar_Pervasives_Native.None -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
let (teq_force :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.typ -> FStarC_Syntax_Syntax.typ -> unit)
  =
  fun env ->
    fun t1 ->
      fun t2 -> let uu___ = teq env t1 t2 in force_trivial_guard env uu___
let (teq_nosmt_force :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.typ -> FStarC_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu___ = teq_nosmt env t1 t2 in
        match uu___ with
        | FStar_Pervasives_Native.None -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
let (layered_effect_teq :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.typ ->
      FStarC_Syntax_Syntax.typ ->
        Prims.string FStar_Pervasives_Native.option ->
          FStarC_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        fun reason ->
          (let uu___1 = FStarC_Compiler_Effect.op_Bang dbg_LayeredEffectsEqns in
           if uu___1
           then
             let uu___2 =
               if FStarC_Compiler_Util.is_none reason
               then "_"
               else FStarC_Compiler_Util.must reason in
             let uu___3 =
               FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t1 in
             let uu___4 =
               FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t2 in
             FStarC_Compiler_Util.print3 "Layered Effect (%s) %s = %s\n"
               uu___2 uu___3 uu___4
           else ());
          teq env t1 t2
let (universe_inequality :
  FStarC_Syntax_Syntax.universe ->
    FStarC_Syntax_Syntax.universe -> FStarC_TypeChecker_Common.guard_t)
  =
  fun u1 ->
    fun u2 ->
      let uu___ =
        let uu___1 =
          Obj.magic
            (FStarC_Class_Listlike.cons ()
               (Obj.magic (FStarC_Compiler_CList.listlike_clist ())) 
               (u1, u2)
               (FStarC_Class_Listlike.empty ()
                  (Obj.magic (FStarC_Compiler_CList.listlike_clist ())))) in
        ((Obj.magic
            (FStarC_Class_Listlike.empty ()
               (Obj.magic (FStarC_Compiler_CList.listlike_clist ())))),
          uu___1) in
      {
        FStarC_TypeChecker_Common.guard_f =
          (FStarC_TypeChecker_Common.trivial_guard.FStarC_TypeChecker_Common.guard_f);
        FStarC_TypeChecker_Common.deferred_to_tac =
          (FStarC_TypeChecker_Common.trivial_guard.FStarC_TypeChecker_Common.deferred_to_tac);
        FStarC_TypeChecker_Common.deferred =
          (FStarC_TypeChecker_Common.trivial_guard.FStarC_TypeChecker_Common.deferred);
        FStarC_TypeChecker_Common.univ_ineqs = uu___;
        FStarC_TypeChecker_Common.implicits =
          (FStarC_TypeChecker_Common.trivial_guard.FStarC_TypeChecker_Common.implicits)
      }