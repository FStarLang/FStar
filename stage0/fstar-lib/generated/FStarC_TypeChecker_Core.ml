open Prims
type tot_or_ghost =
  | E_Total 
  | E_Ghost 
let (uu___is_E_Total : tot_or_ghost -> Prims.bool) =
  fun projectee -> match projectee with | E_Total -> true | uu___ -> false
let (uu___is_E_Ghost : tot_or_ghost -> Prims.bool) =
  fun projectee -> match projectee with | E_Ghost -> true | uu___ -> false
let (dbg : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "Core"
let (dbg_Eq : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "CoreEq"
let (dbg_Top : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "CoreTop"
let (dbg_Exit : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "CoreExit"
let (goal_ctr : Prims.int FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Util.mk_ref Prims.int_zero
let (get_goal_ctr : unit -> Prims.int) =
  fun uu___ -> FStarC_Compiler_Effect.op_Bang goal_ctr
let (incr_goal_ctr : unit -> Prims.int) =
  fun uu___ ->
    let v = FStarC_Compiler_Effect.op_Bang goal_ctr in
    FStarC_Compiler_Effect.op_Colon_Equals goal_ctr (v + Prims.int_one);
    v + Prims.int_one
type guard_handler_t =
  FStarC_TypeChecker_Env.env -> FStarC_Syntax_Syntax.typ -> Prims.bool
type env =
  {
  tcenv: FStarC_TypeChecker_Env.env ;
  allow_universe_instantiation: Prims.bool ;
  max_binder_index: Prims.int ;
  guard_handler: guard_handler_t FStar_Pervasives_Native.option ;
  should_read_cache: Prims.bool }
let (__proj__Mkenv__item__tcenv : env -> FStarC_TypeChecker_Env.env) =
  fun projectee ->
    match projectee with
    | { tcenv; allow_universe_instantiation; max_binder_index; guard_handler;
        should_read_cache;_} -> tcenv
let (__proj__Mkenv__item__allow_universe_instantiation : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { tcenv; allow_universe_instantiation; max_binder_index; guard_handler;
        should_read_cache;_} -> allow_universe_instantiation
let (__proj__Mkenv__item__max_binder_index : env -> Prims.int) =
  fun projectee ->
    match projectee with
    | { tcenv; allow_universe_instantiation; max_binder_index; guard_handler;
        should_read_cache;_} -> max_binder_index
let (__proj__Mkenv__item__guard_handler :
  env -> guard_handler_t FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { tcenv; allow_universe_instantiation; max_binder_index; guard_handler;
        should_read_cache;_} -> guard_handler
let (__proj__Mkenv__item__should_read_cache : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { tcenv; allow_universe_instantiation; max_binder_index; guard_handler;
        should_read_cache;_} -> should_read_cache
let (push_binder : env -> FStarC_Syntax_Syntax.binder -> env) =
  fun g ->
    fun b ->
      if
        (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.index <=
          g.max_binder_index
      then
        failwith
          "Assertion failed: unexpected shadowing in the core environment"
      else
        (let uu___1 = FStarC_TypeChecker_Env.push_binders g.tcenv [b] in
         {
           tcenv = uu___1;
           allow_universe_instantiation = (g.allow_universe_instantiation);
           max_binder_index =
             ((b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.index);
           guard_handler = (g.guard_handler);
           should_read_cache = (g.should_read_cache)
         })
let (push_binders : env -> FStarC_Syntax_Syntax.binder Prims.list -> env) =
  FStarC_Compiler_List.fold_left push_binder
let (fresh_binder :
  env -> FStarC_Syntax_Syntax.binder -> (env * FStarC_Syntax_Syntax.binder))
  =
  fun g ->
    fun old ->
      let ctr = g.max_binder_index + Prims.int_one in
      let bv =
        let uu___ = old.FStarC_Syntax_Syntax.binder_bv in
        {
          FStarC_Syntax_Syntax.ppname = (uu___.FStarC_Syntax_Syntax.ppname);
          FStarC_Syntax_Syntax.index = ctr;
          FStarC_Syntax_Syntax.sort = (uu___.FStarC_Syntax_Syntax.sort)
        } in
      let b =
        FStarC_Syntax_Syntax.mk_binder_with_attrs bv
          old.FStarC_Syntax_Syntax.binder_qual
          old.FStarC_Syntax_Syntax.binder_positivity
          old.FStarC_Syntax_Syntax.binder_attrs in
      let uu___ = push_binder g b in (uu___, b)
let (open_binders :
  env ->
    FStarC_Syntax_Syntax.binders ->
      (env * FStarC_Syntax_Syntax.binder Prims.list *
        FStarC_Syntax_Syntax.subst_elt Prims.list))
  =
  fun g ->
    fun bs ->
      let uu___ =
        FStarC_Compiler_List.fold_left
          (fun uu___1 ->
             fun b ->
               match uu___1 with
               | (g1, bs1, subst) ->
                   let bv =
                     let uu___2 = b.FStarC_Syntax_Syntax.binder_bv in
                     let uu___3 =
                       FStarC_Syntax_Subst.subst subst
                         (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                     {
                       FStarC_Syntax_Syntax.ppname =
                         (uu___2.FStarC_Syntax_Syntax.ppname);
                       FStarC_Syntax_Syntax.index =
                         (uu___2.FStarC_Syntax_Syntax.index);
                       FStarC_Syntax_Syntax.sort = uu___3
                     } in
                   let b1 =
                     let uu___2 =
                       FStarC_Syntax_Subst.subst_bqual subst
                         b.FStarC_Syntax_Syntax.binder_qual in
                     let uu___3 =
                       FStarC_Compiler_List.map
                         (FStarC_Syntax_Subst.subst subst)
                         b.FStarC_Syntax_Syntax.binder_attrs in
                     {
                       FStarC_Syntax_Syntax.binder_bv = bv;
                       FStarC_Syntax_Syntax.binder_qual = uu___2;
                       FStarC_Syntax_Syntax.binder_positivity =
                         (b.FStarC_Syntax_Syntax.binder_positivity);
                       FStarC_Syntax_Syntax.binder_attrs = uu___3
                     } in
                   let uu___2 = fresh_binder g1 b1 in
                   (match uu___2 with
                    | (g2, b') ->
                        let uu___3 =
                          let uu___4 =
                            FStarC_Syntax_Subst.shift_subst Prims.int_one
                              subst in
                          (FStarC_Syntax_Syntax.DB
                             (Prims.int_zero,
                               (b'.FStarC_Syntax_Syntax.binder_bv)))
                            :: uu___4 in
                        (g2, (b' :: bs1), uu___3))) (g, [], []) bs in
      match uu___ with
      | (g1, bs_rev, subst) -> (g1, (FStarC_Compiler_List.rev bs_rev), subst)
let (open_pat :
  env ->
    FStarC_Syntax_Syntax.pat ->
      (env * FStarC_Syntax_Syntax.pat * FStarC_Syntax_Syntax.subst_t))
  =
  fun g ->
    fun p ->
      let rec open_pat_aux g1 p1 sub =
        match p1.FStarC_Syntax_Syntax.v with
        | FStarC_Syntax_Syntax.Pat_constant uu___ -> (g1, p1, sub)
        | FStarC_Syntax_Syntax.Pat_cons (fv, us_opt, pats) ->
            let uu___ =
              FStarC_Compiler_List.fold_left
                (fun uu___1 ->
                   fun uu___2 ->
                     match (uu___1, uu___2) with
                     | ((g2, pats1, sub1), (p2, imp)) ->
                         let uu___3 = open_pat_aux g2 p2 sub1 in
                         (match uu___3 with
                          | (g3, p3, sub2) ->
                              (g3, ((p3, imp) :: pats1), sub2)))
                (g1, [], sub) pats in
            (match uu___ with
             | (g2, pats1, sub1) ->
                 (g2,
                   {
                     FStarC_Syntax_Syntax.v =
                       (FStarC_Syntax_Syntax.Pat_cons
                          (fv, us_opt, (FStarC_Compiler_List.rev pats1)));
                     FStarC_Syntax_Syntax.p = (p1.FStarC_Syntax_Syntax.p)
                   }, sub1))
        | FStarC_Syntax_Syntax.Pat_var x ->
            let bx =
              let uu___ =
                let uu___1 =
                  FStarC_Syntax_Subst.subst sub x.FStarC_Syntax_Syntax.sort in
                {
                  FStarC_Syntax_Syntax.ppname =
                    (x.FStarC_Syntax_Syntax.ppname);
                  FStarC_Syntax_Syntax.index = (x.FStarC_Syntax_Syntax.index);
                  FStarC_Syntax_Syntax.sort = uu___1
                } in
              FStarC_Syntax_Syntax.mk_binder uu___ in
            let uu___ = fresh_binder g1 bx in
            (match uu___ with
             | (g2, bx') ->
                 let sub1 =
                   let uu___1 =
                     FStarC_Syntax_Subst.shift_subst Prims.int_one sub in
                   (FStarC_Syntax_Syntax.DB
                      (Prims.int_zero, (bx'.FStarC_Syntax_Syntax.binder_bv)))
                     :: uu___1 in
                 (g2,
                   {
                     FStarC_Syntax_Syntax.v =
                       (FStarC_Syntax_Syntax.Pat_var
                          (bx'.FStarC_Syntax_Syntax.binder_bv));
                     FStarC_Syntax_Syntax.p = (p1.FStarC_Syntax_Syntax.p)
                   }, sub1))
        | FStarC_Syntax_Syntax.Pat_dot_term eopt ->
            let eopt1 =
              FStarC_Compiler_Util.map_option (FStarC_Syntax_Subst.subst sub)
                eopt in
            (g1,
              {
                FStarC_Syntax_Syntax.v =
                  (FStarC_Syntax_Syntax.Pat_dot_term eopt1);
                FStarC_Syntax_Syntax.p = (p1.FStarC_Syntax_Syntax.p)
              }, sub) in
      open_pat_aux g p []
let (open_term :
  env ->
    FStarC_Syntax_Syntax.binder ->
      FStarC_Syntax_Syntax.term ->
        (env * FStarC_Syntax_Syntax.binder * FStarC_Syntax_Syntax.term))
  =
  fun g ->
    fun b ->
      fun t ->
        let uu___ = fresh_binder g b in
        match uu___ with
        | (g1, b') ->
            let t1 =
              FStarC_Syntax_Subst.subst
                [FStarC_Syntax_Syntax.DB
                   (Prims.int_zero, (b'.FStarC_Syntax_Syntax.binder_bv))] t in
            (g1, b', t1)
let (open_term_binders :
  env ->
    FStarC_Syntax_Syntax.binders ->
      FStarC_Syntax_Syntax.term ->
        (env * FStarC_Syntax_Syntax.binders * FStarC_Syntax_Syntax.term))
  =
  fun g ->
    fun bs ->
      fun t ->
        let uu___ = open_binders g bs in
        match uu___ with
        | (g1, bs1, subst) ->
            let uu___1 = FStarC_Syntax_Subst.subst subst t in
            (g1, bs1, uu___1)
let (open_comp :
  env ->
    FStarC_Syntax_Syntax.binder ->
      FStarC_Syntax_Syntax.comp ->
        (env * FStarC_Syntax_Syntax.binder * FStarC_Syntax_Syntax.comp))
  =
  fun g ->
    fun b ->
      fun c ->
        let uu___ = fresh_binder g b in
        match uu___ with
        | (g1, bx) ->
            let c1 =
              FStarC_Syntax_Subst.subst_comp
                [FStarC_Syntax_Syntax.DB
                   (Prims.int_zero, (bx.FStarC_Syntax_Syntax.binder_bv))] c in
            (g1, bx, c1)
let (open_comp_binders :
  env ->
    FStarC_Syntax_Syntax.binders ->
      FStarC_Syntax_Syntax.comp ->
        (env * FStarC_Syntax_Syntax.binders * FStarC_Syntax_Syntax.comp))
  =
  fun g ->
    fun bs ->
      fun c ->
        let uu___ = open_binders g bs in
        match uu___ with
        | (g1, bs1, s) ->
            let c1 = FStarC_Syntax_Subst.subst_comp s c in (g1, bs1, c1)
let (arrow_formals_comp :
  env ->
    FStarC_Syntax_Syntax.term ->
      (env * FStarC_Syntax_Syntax.binder Prims.list *
        FStarC_Syntax_Syntax.comp))
  =
  fun g ->
    fun c ->
      let uu___ = FStarC_Syntax_Util.arrow_formals_comp_ln c in
      match uu___ with
      | (bs, c1) ->
          let uu___1 = open_binders g bs in
          (match uu___1 with
           | (g1, bs1, subst) ->
               let uu___2 = FStarC_Syntax_Subst.subst_comp subst c1 in
               (g1, bs1, uu___2))
let (open_branch :
  env -> FStarC_Syntax_Syntax.branch -> (env * FStarC_Syntax_Syntax.branch))
  =
  fun g ->
    fun br ->
      let uu___ = br in
      match uu___ with
      | (p, wopt, e) ->
          let uu___1 = open_pat g p in
          (match uu___1 with
           | (g1, p1, s) ->
               let uu___2 =
                 let uu___3 =
                   FStarC_Compiler_Util.map_option
                     (FStarC_Syntax_Subst.subst s) wopt in
                 let uu___4 = FStarC_Syntax_Subst.subst s e in
                 (p1, uu___3, uu___4) in
               (g1, uu___2))
let (open_branches_eq_pat :
  env ->
    FStarC_Syntax_Syntax.branch ->
      FStarC_Syntax_Syntax.branch ->
        (env * (FStarC_Syntax_Syntax.pat * FStarC_Syntax_Syntax.term
          FStar_Pervasives_Native.option * FStarC_Syntax_Syntax.term) *
          (FStarC_Syntax_Syntax.pat * FStarC_Syntax_Syntax.term
          FStar_Pervasives_Native.option * FStarC_Syntax_Syntax.term)))
  =
  fun g ->
    fun br0 ->
      fun br1 ->
        let uu___ = br0 in
        match uu___ with
        | (p0, wopt0, e0) ->
            let uu___1 = br1 in
            (match uu___1 with
             | (uu___2, wopt1, e1) ->
                 let uu___3 = open_pat g p0 in
                 (match uu___3 with
                  | (g1, p01, s) ->
                      let uu___4 =
                        let uu___5 =
                          FStarC_Compiler_Util.map_option
                            (FStarC_Syntax_Subst.subst s) wopt0 in
                        let uu___6 = FStarC_Syntax_Subst.subst s e0 in
                        (p01, uu___5, uu___6) in
                      let uu___5 =
                        let uu___6 =
                          FStarC_Compiler_Util.map_option
                            (FStarC_Syntax_Subst.subst s) wopt1 in
                        let uu___7 = FStarC_Syntax_Subst.subst s e1 in
                        (p01, uu___6, uu___7) in
                      (g1, uu___4, uu___5)))
type precondition = FStarC_Syntax_Syntax.typ FStar_Pervasives_Native.option
type 'a success = ('a * precondition)
type relation =
  | EQUALITY 
  | SUBTYPING of FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option 
let (uu___is_EQUALITY : relation -> Prims.bool) =
  fun projectee -> match projectee with | EQUALITY -> true | uu___ -> false
let (uu___is_SUBTYPING : relation -> Prims.bool) =
  fun projectee ->
    match projectee with | SUBTYPING _0 -> true | uu___ -> false
let (__proj__SUBTYPING__item___0 :
  relation -> FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | SUBTYPING _0 -> _0
let (relation_to_string : relation -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | EQUALITY -> "=?="
    | SUBTYPING (FStar_Pervasives_Native.None) -> "<:?"
    | SUBTYPING (FStar_Pervasives_Native.Some tm) ->
        let uu___1 =
          FStarC_Class_Show.show FStarC_Syntax_Print.showable_term tm in
        FStarC_Compiler_Util.format1 "( <:? %s)" uu___1
type context_term =
  | CtxTerm of FStarC_Syntax_Syntax.term 
  | CtxRel of FStarC_Syntax_Syntax.term * relation *
  FStarC_Syntax_Syntax.term 
let (uu___is_CtxTerm : context_term -> Prims.bool) =
  fun projectee -> match projectee with | CtxTerm _0 -> true | uu___ -> false
let (__proj__CtxTerm__item___0 : context_term -> FStarC_Syntax_Syntax.term) =
  fun projectee -> match projectee with | CtxTerm _0 -> _0
let (uu___is_CtxRel : context_term -> Prims.bool) =
  fun projectee ->
    match projectee with | CtxRel (_0, _1, _2) -> true | uu___ -> false
let (__proj__CtxRel__item___0 : context_term -> FStarC_Syntax_Syntax.term) =
  fun projectee -> match projectee with | CtxRel (_0, _1, _2) -> _0
let (__proj__CtxRel__item___1 : context_term -> relation) =
  fun projectee -> match projectee with | CtxRel (_0, _1, _2) -> _1
let (__proj__CtxRel__item___2 : context_term -> FStarC_Syntax_Syntax.term) =
  fun projectee -> match projectee with | CtxRel (_0, _1, _2) -> _2
let (context_term_to_string : context_term -> Prims.string) =
  fun c ->
    match c with
    | CtxTerm term ->
        FStarC_Class_Show.show FStarC_Syntax_Print.showable_term term
    | CtxRel (t0, r, t1) ->
        let uu___ =
          FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t0 in
        let uu___1 = relation_to_string r in
        let uu___2 =
          FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t1 in
        FStarC_Compiler_Util.format3 "%s %s %s" uu___ uu___1 uu___2
type context =
  {
  no_guard: Prims.bool ;
  unfolding_ok: Prims.bool ;
  error_context:
    (Prims.string * context_term FStar_Pervasives_Native.option) Prims.list }
let (__proj__Mkcontext__item__no_guard : context -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { no_guard; unfolding_ok; error_context;_} -> no_guard
let (__proj__Mkcontext__item__unfolding_ok : context -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { no_guard; unfolding_ok; error_context;_} -> unfolding_ok
let (__proj__Mkcontext__item__error_context :
  context ->
    (Prims.string * context_term FStar_Pervasives_Native.option) Prims.list)
  =
  fun projectee ->
    match projectee with
    | { no_guard; unfolding_ok; error_context;_} -> error_context
let (showable_context : context FStarC_Class_Show.showable) =
  {
    FStarC_Class_Show.show =
      (fun context1 ->
         let uu___ =
           FStarC_Class_Show.show FStarC_Class_Show.showable_bool
             context1.no_guard in
         let uu___1 =
           FStarC_Class_Show.show FStarC_Class_Show.showable_bool
             context1.unfolding_ok in
         let uu___2 =
           let uu___3 =
             FStarC_Compiler_List.map FStar_Pervasives_Native.fst
               context1.error_context in
           FStarC_Class_Show.show
             (FStarC_Class_Show.show_list FStarC_Class_Show.showable_string)
             uu___3 in
         FStarC_Compiler_Util.format3
           "{no_guard=%s; unfolding_ok=%s; error_context=%s}" uu___ uu___1
           uu___2)
  }
let (print_context : context -> Prims.string) =
  fun ctx ->
    let rec aux depth ctx1 =
      match ctx1 with
      | [] -> ""
      | (msg, ctx_term)::tl ->
          let hd =
            let uu___ =
              match ctx_term with
              | FStar_Pervasives_Native.None -> ""
              | FStar_Pervasives_Native.Some ctx_term1 ->
                  context_term_to_string ctx_term1 in
            FStarC_Compiler_Util.format3 "%s %s (%s)\n" depth msg uu___ in
          let tl1 = aux (Prims.strcat depth ">") tl in Prims.strcat hd tl1 in
    aux "" (FStarC_Compiler_List.rev ctx.error_context)
type error = (context * Prims.string)
let (print_error : error -> Prims.string) =
  fun err ->
    let uu___ = err in
    match uu___ with
    | (ctx, msg) ->
        let uu___1 = print_context ctx in
        FStarC_Compiler_Util.format2 "%s%s" uu___1 msg
let (print_error_short : error -> Prims.string) =
  fun err -> FStar_Pervasives_Native.snd err
type 'a __result =
  | Success of 'a 
  | Error of error 
let uu___is_Success : 'a . 'a __result -> Prims.bool =
  fun projectee -> match projectee with | Success _0 -> true | uu___ -> false
let __proj__Success__item___0 : 'a . 'a __result -> 'a =
  fun projectee -> match projectee with | Success _0 -> _0
let uu___is_Error : 'a . 'a __result -> Prims.bool =
  fun projectee -> match projectee with | Error _0 -> true | uu___ -> false
let __proj__Error__item___0 : 'a . 'a __result -> error =
  fun projectee -> match projectee with | Error _0 -> _0
let showable_result :
  'a .
    'a FStarC_Class_Show.showable -> 'a __result FStarC_Class_Show.showable
  =
  fun uu___ ->
    {
      FStarC_Class_Show.show =
        (fun uu___1 ->
           match uu___1 with
           | Success a1 ->
               let uu___2 = FStarC_Class_Show.show uu___ a1 in
               Prims.strcat "Success " uu___2
           | Error e ->
               let uu___2 = print_error_short e in
               Prims.strcat "Error " uu___2)
    }
type 'a result = context -> 'a success __result
type hash_entry =
  {
  he_term: FStarC_Syntax_Syntax.term ;
  he_gamma: FStarC_Syntax_Syntax.binding Prims.list ;
  he_res: (tot_or_ghost * FStarC_Syntax_Syntax.typ) success }
let (__proj__Mkhash_entry__item__he_term :
  hash_entry -> FStarC_Syntax_Syntax.term) =
  fun projectee ->
    match projectee with | { he_term; he_gamma; he_res;_} -> he_term
let (__proj__Mkhash_entry__item__he_gamma :
  hash_entry -> FStarC_Syntax_Syntax.binding Prims.list) =
  fun projectee ->
    match projectee with | { he_term; he_gamma; he_res;_} -> he_gamma
let (__proj__Mkhash_entry__item__he_res :
  hash_entry -> (tot_or_ghost * FStarC_Syntax_Syntax.typ) success) =
  fun projectee ->
    match projectee with | { he_term; he_gamma; he_res;_} -> he_res
type tc_table = hash_entry FStarC_Syntax_TermHashTable.hashtable
let (equal_term_for_hash :
  FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term -> Prims.bool) =
  fun t1 ->
    fun t2 ->
      FStarC_Profiling.profile
        (fun uu___ -> FStarC_Syntax_Hash.equal_term t1 t2)
        FStar_Pervasives_Native.None
        "FStarC.TypeChecker.Core.equal_term_for_hash"
let (equal_term :
  FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term -> Prims.bool) =
  fun t1 ->
    fun t2 ->
      FStarC_Profiling.profile
        (fun uu___ -> FStarC_Syntax_Hash.equal_term t1 t2)
        FStar_Pervasives_Native.None "FStarC.TypeChecker.Core.equal_term"
let (table : tc_table) =
  FStarC_Syntax_TermHashTable.create (Prims.parse_int "1048576")
type cache_stats_t = {
  hits: Prims.int ;
  misses: Prims.int }
let (__proj__Mkcache_stats_t__item__hits : cache_stats_t -> Prims.int) =
  fun projectee -> match projectee with | { hits; misses;_} -> hits
let (__proj__Mkcache_stats_t__item__misses : cache_stats_t -> Prims.int) =
  fun projectee -> match projectee with | { hits; misses;_} -> misses
let (cache_stats : cache_stats_t FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Util.mk_ref
    { hits = Prims.int_zero; misses = Prims.int_zero }
let (record_cache_hit : unit -> unit) =
  fun uu___ ->
    let cs = FStarC_Compiler_Effect.op_Bang cache_stats in
    FStarC_Compiler_Effect.op_Colon_Equals cache_stats
      { hits = (cs.hits + Prims.int_one); misses = (cs.misses) }
let (record_cache_miss : unit -> unit) =
  fun uu___ ->
    let cs = FStarC_Compiler_Effect.op_Bang cache_stats in
    FStarC_Compiler_Effect.op_Colon_Equals cache_stats
      { hits = (cs.hits); misses = (cs.misses + Prims.int_one) }
let (reset_cache_stats : unit -> unit) =
  fun uu___ ->
    FStarC_Compiler_Effect.op_Colon_Equals cache_stats
      { hits = Prims.int_zero; misses = Prims.int_zero }
let (report_cache_stats : unit -> cache_stats_t) =
  fun uu___ -> FStarC_Compiler_Effect.op_Bang cache_stats
let (clear_memo_table : unit -> unit) =
  fun uu___ -> FStarC_Syntax_TermHashTable.clear table
type side =
  | Left 
  | Right 
  | Both 
  | Neither 
let (uu___is_Left : side -> Prims.bool) =
  fun projectee -> match projectee with | Left -> true | uu___ -> false
let (uu___is_Right : side -> Prims.bool) =
  fun projectee -> match projectee with | Right -> true | uu___ -> false
let (uu___is_Both : side -> Prims.bool) =
  fun projectee -> match projectee with | Both -> true | uu___ -> false
let (uu___is_Neither : side -> Prims.bool) =
  fun projectee -> match projectee with | Neither -> true | uu___ -> false
let (insert :
  env ->
    FStarC_Syntax_Syntax.term ->
      (tot_or_ghost * FStarC_Syntax_Syntax.typ) success -> unit)
  =
  fun g ->
    fun e ->
      fun res ->
        let entry =
          {
            he_term = e;
            he_gamma = ((g.tcenv).FStarC_TypeChecker_Env.gamma);
            he_res = res
          } in
        FStarC_Syntax_TermHashTable.insert e entry table
let return : 'a . 'a -> 'a result =
  fun x -> fun uu___ -> Success (x, FStar_Pervasives_Native.None)
let (and_pre :
  precondition ->
    precondition ->
      FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option)
  =
  fun p1 ->
    fun p2 ->
      match (p1, p2) with
      | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
          FStar_Pervasives_Native.None
      | (FStar_Pervasives_Native.Some p, FStar_Pervasives_Native.None) ->
          FStar_Pervasives_Native.Some p
      | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some p) ->
          FStar_Pervasives_Native.Some p
      | (FStar_Pervasives_Native.Some p11, FStar_Pervasives_Native.Some p21)
          ->
          let uu___ = FStarC_Syntax_Util.mk_conj p11 p21 in
          FStar_Pervasives_Native.Some uu___
let op_let_Bang : 'a 'b . 'a result -> ('a -> 'b result) -> 'b result =
  fun x ->
    fun y ->
      fun ctx0 ->
        let uu___ = x ctx0 in
        match uu___ with
        | Success (x1, g1) ->
            let uu___1 = let uu___2 = y x1 in uu___2 ctx0 in
            (match uu___1 with
             | Success (y1, g2) ->
                 let uu___2 = let uu___3 = and_pre g1 g2 in (y1, uu___3) in
                 Success uu___2
             | err -> err)
        | Error err -> Error err
let op_and_Bang : 'a 'b . 'a result -> 'b result -> ('a * 'b) result =
  fun x ->
    fun y ->
      fun ctx0 ->
        let uu___ = x ctx0 in
        match uu___ with
        | Success (x1, g1) ->
            let uu___1 =
              let uu___2 ctx01 =
                let uu___3 = y ctx01 in
                match uu___3 with
                | Success (x2, g11) ->
                    let uu___4 =
                      let uu___5 uu___6 =
                        Success ((x1, x2), FStar_Pervasives_Native.None) in
                      uu___5 ctx01 in
                    (match uu___4 with
                     | Success (y1, g2) ->
                         let uu___5 =
                           let uu___6 = and_pre g11 g2 in (y1, uu___6) in
                         Success uu___5
                     | err -> err)
                | Error err -> Error err in
              uu___2 ctx0 in
            (match uu___1 with
             | Success (y1, g2) ->
                 let uu___2 = let uu___3 = and_pre g1 g2 in (y1, uu___3) in
                 Success uu___2
             | err -> err)
        | Error err -> Error err
let op_let_Question :
  'a 'b .
    'a FStar_Pervasives_Native.option ->
      ('a -> 'b FStar_Pervasives_Native.option) ->
        'b FStar_Pervasives_Native.option
  =
  fun x ->
    fun f ->
      match x with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some x1 -> f x1
let fail : 'a . Prims.string -> 'a result =
  fun msg -> fun ctx -> Error (ctx, msg)
let (dump_context : unit result) =
  fun ctx ->
    (let uu___1 = print_context ctx in
     FStarC_Compiler_Util.print_string uu___1);
    (let uu___1 uu___2 = Success ((), FStar_Pervasives_Native.None) in
     uu___1 ctx)
let handle_with : 'a . 'a result -> (unit -> 'a result) -> 'a result =
  fun x ->
    fun h ->
      fun ctx ->
        let uu___ = x ctx in
        match uu___ with
        | Error uu___1 -> let uu___2 = h () in uu___2 ctx
        | res -> res
let with_context :
  'a .
    Prims.string ->
      context_term FStar_Pervasives_Native.option ->
        (unit -> 'a result) -> 'a result
  =
  fun msg ->
    fun t ->
      fun x ->
        fun ctx ->
          let ctx1 =
            {
              no_guard = (ctx.no_guard);
              unfolding_ok = (ctx.unfolding_ok);
              error_context = ((msg, t) :: (ctx.error_context))
            } in
          let uu___ = x () in uu___ ctx1
let (mk_type :
  FStarC_Syntax_Syntax.universe ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  =
  fun u ->
    FStarC_Syntax_Syntax.mk (FStarC_Syntax_Syntax.Tm_type u)
      FStarC_Compiler_Range_Type.dummyRange
let (is_type :
  env -> FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.universe result) =
  fun g ->
    fun t ->
      let aux t1 =
        let uu___ =
          let uu___1 = FStarC_Syntax_Subst.compress t1 in
          uu___1.FStarC_Syntax_Syntax.n in
        match uu___ with
        | FStarC_Syntax_Syntax.Tm_type u ->
            (fun uu___1 -> Success (u, FStar_Pervasives_Native.None))
        | uu___1 ->
            let uu___2 =
              let uu___3 =
                FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t1 in
              FStarC_Compiler_Util.format1 "Expected a type; got %s" uu___3 in
            fail uu___2 in
      fun ctx ->
        let ctx1 =
          {
            no_guard = (ctx.no_guard);
            unfolding_ok = (ctx.unfolding_ok);
            error_context =
              (("is_type", (FStar_Pervasives_Native.Some (CtxTerm t))) ::
              (ctx.error_context))
          } in
        let uu___ =
          let uu___1 = aux t in
          fun ctx2 ->
            let uu___2 = uu___1 ctx2 in
            match uu___2 with
            | Error uu___3 ->
                let uu___4 =
                  let uu___5 =
                    let uu___6 =
                      FStarC_TypeChecker_Normalize.unfold_whnf g.tcenv t in
                    FStarC_Syntax_Util.unrefine uu___6 in
                  aux uu___5 in
                uu___4 ctx2
            | res -> res in
        uu___ ctx1
let rec (is_arrow :
  env ->
    FStarC_Syntax_Syntax.term ->
      (FStarC_Syntax_Syntax.binder * tot_or_ghost * FStarC_Syntax_Syntax.typ)
        result)
  =
  fun g ->
    fun t ->
      let rec aux t1 =
        let uu___ =
          let uu___1 = FStarC_Syntax_Subst.compress t1 in
          uu___1.FStarC_Syntax_Syntax.n in
        match uu___ with
        | FStarC_Syntax_Syntax.Tm_arrow
            { FStarC_Syntax_Syntax.bs1 = x::[];
              FStarC_Syntax_Syntax.comp = c;_}
            ->
            let uu___1 = FStarC_Syntax_Util.is_tot_or_gtot_comp c in
            if uu___1
            then
              let uu___2 = open_comp g x c in
              (match uu___2 with
               | (g1, x1, c1) ->
                   let eff =
                     let uu___3 = FStarC_Syntax_Util.is_total_comp c1 in
                     if uu___3 then E_Total else E_Ghost in
                   (fun uu___3 ->
                      Success
                        ((x1, eff, (FStarC_Syntax_Util.comp_result c1)),
                          FStar_Pervasives_Native.None)))
            else
              (let e_tag =
                 let uu___3 = c.FStarC_Syntax_Syntax.n in
                 match uu___3 with
                 | FStarC_Syntax_Syntax.Comp ct ->
                     let uu___4 =
                       (FStarC_Ident.lid_equals
                          ct.FStarC_Syntax_Syntax.effect_name
                          FStarC_Parser_Const.effect_Pure_lid)
                         ||
                         (FStarC_Ident.lid_equals
                            ct.FStarC_Syntax_Syntax.effect_name
                            FStarC_Parser_Const.effect_Lemma_lid) in
                     if uu___4
                     then FStar_Pervasives_Native.Some E_Total
                     else
                       (let uu___6 =
                          FStarC_Ident.lid_equals
                            ct.FStarC_Syntax_Syntax.effect_name
                            FStarC_Parser_Const.effect_Ghost_lid in
                        if uu___6
                        then FStar_Pervasives_Native.Some E_Ghost
                        else FStar_Pervasives_Native.None) in
               match e_tag with
               | FStar_Pervasives_Native.None ->
                   let uu___3 =
                     let uu___4 =
                       FStarC_Ident.string_of_lid
                         (FStarC_Syntax_Util.comp_effect_name c) in
                     FStarC_Compiler_Util.format1
                       "Expected total or gtot arrow, got %s" uu___4 in
                   fail uu___3
               | FStar_Pervasives_Native.Some e_tag1 ->
                   let uu___3 = arrow_formals_comp g t1 in
                   (match uu___3 with
                    | (g1, x1::[], c1) ->
                        let uu___4 = FStarC_Syntax_Util.comp_effect_args c1 in
                        (match uu___4 with
                         | (pre, uu___5)::(post, uu___6)::uu___7 ->
                             let arg_typ =
                               FStarC_Syntax_Util.refine
                                 x1.FStarC_Syntax_Syntax.binder_bv pre in
                             let res_typ =
                               let r =
                                 FStarC_Syntax_Syntax.new_bv
                                   FStar_Pervasives_Native.None
                                   (FStarC_Syntax_Util.comp_result c1) in
                               let post1 =
                                 let uu___8 =
                                   let uu___9 =
                                     let uu___10 =
                                       FStarC_Syntax_Syntax.bv_to_name r in
                                     (uu___10, FStar_Pervasives_Native.None) in
                                   [uu___9] in
                                 FStarC_Syntax_Syntax.mk_Tm_app post uu___8
                                   post.FStarC_Syntax_Syntax.pos in
                               FStarC_Syntax_Util.refine r post1 in
                             let xbv =
                               let uu___8 = x1.FStarC_Syntax_Syntax.binder_bv in
                               {
                                 FStarC_Syntax_Syntax.ppname =
                                   (uu___8.FStarC_Syntax_Syntax.ppname);
                                 FStarC_Syntax_Syntax.index =
                                   (uu___8.FStarC_Syntax_Syntax.index);
                                 FStarC_Syntax_Syntax.sort = arg_typ
                               } in
                             let x2 =
                               {
                                 FStarC_Syntax_Syntax.binder_bv = xbv;
                                 FStarC_Syntax_Syntax.binder_qual =
                                   (x1.FStarC_Syntax_Syntax.binder_qual);
                                 FStarC_Syntax_Syntax.binder_positivity =
                                   (x1.FStarC_Syntax_Syntax.binder_positivity);
                                 FStarC_Syntax_Syntax.binder_attrs =
                                   (x1.FStarC_Syntax_Syntax.binder_attrs)
                               } in
                             (fun uu___8 ->
                                Success
                                  ((x2, e_tag1, res_typ),
                                    FStar_Pervasives_Native.None)))))
        | FStarC_Syntax_Syntax.Tm_arrow
            { FStarC_Syntax_Syntax.bs1 = x::xs;
              FStarC_Syntax_Syntax.comp = c;_}
            ->
            let t2 =
              FStarC_Syntax_Syntax.mk
                (FStarC_Syntax_Syntax.Tm_arrow
                   {
                     FStarC_Syntax_Syntax.bs1 = xs;
                     FStarC_Syntax_Syntax.comp = c
                   }) t1.FStarC_Syntax_Syntax.pos in
            let uu___1 = open_term g x t2 in
            (match uu___1 with
             | (g1, x1, t3) ->
                 (fun uu___2 ->
                    Success ((x1, E_Total, t3), FStar_Pervasives_Native.None)))
        | FStarC_Syntax_Syntax.Tm_refine
            { FStarC_Syntax_Syntax.b = x;
              FStarC_Syntax_Syntax.phi = uu___1;_}
            -> is_arrow g x.FStarC_Syntax_Syntax.sort
        | FStarC_Syntax_Syntax.Tm_meta
            { FStarC_Syntax_Syntax.tm2 = t2;
              FStarC_Syntax_Syntax.meta = uu___1;_}
            -> aux t2
        | FStarC_Syntax_Syntax.Tm_ascribed
            { FStarC_Syntax_Syntax.tm = t2;
              FStarC_Syntax_Syntax.asc = uu___1;
              FStarC_Syntax_Syntax.eff_opt = uu___2;_}
            -> aux t2
        | uu___1 ->
            let uu___2 =
              let uu___3 =
                FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term
                  t1 in
              let uu___4 =
                FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t1 in
              FStarC_Compiler_Util.format2 "Expected an arrow, got (%s) %s"
                uu___3 uu___4 in
            fail uu___2 in
      fun ctx ->
        let ctx1 =
          {
            no_guard = (ctx.no_guard);
            unfolding_ok = (ctx.unfolding_ok);
            error_context = (("is_arrow", FStar_Pervasives_Native.None) ::
              (ctx.error_context))
          } in
        let uu___ =
          let uu___1 = aux t in
          fun ctx2 ->
            let uu___2 = uu___1 ctx2 in
            match uu___2 with
            | Error uu___3 ->
                let uu___4 =
                  let uu___5 =
                    FStarC_TypeChecker_Normalize.unfold_whnf g.tcenv t in
                  aux uu___5 in
                uu___4 ctx2
            | res -> res in
        uu___ ctx1
let (check_arg_qual :
  FStarC_Syntax_Syntax.aqual -> FStarC_Syntax_Syntax.bqual -> unit result) =
  fun a ->
    fun b ->
      match b with
      | FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Implicit uu___) ->
          (match a with
           | FStar_Pervasives_Native.Some
               { FStarC_Syntax_Syntax.aqual_implicit = true;
                 FStarC_Syntax_Syntax.aqual_attributes = uu___1;_}
               -> (fun uu___2 -> Success ((), FStar_Pervasives_Native.None))
           | uu___1 -> fail "missing arg qualifier implicit")
      | FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Meta uu___) ->
          (match a with
           | FStar_Pervasives_Native.Some
               { FStarC_Syntax_Syntax.aqual_implicit = true;
                 FStarC_Syntax_Syntax.aqual_attributes = uu___1;_}
               -> (fun uu___2 -> Success ((), FStar_Pervasives_Native.None))
           | uu___1 -> fail "missing arg qualifier implicit")
      | uu___ ->
          (match a with
           | FStar_Pervasives_Native.Some
               { FStarC_Syntax_Syntax.aqual_implicit = true;
                 FStarC_Syntax_Syntax.aqual_attributes = uu___1;_}
               -> fail "extra arg qualifier implicit"
           | uu___1 ->
               (fun uu___2 -> Success ((), FStar_Pervasives_Native.None)))
let (check_bqual :
  FStarC_Syntax_Syntax.bqual -> FStarC_Syntax_Syntax.bqual -> unit result) =
  fun b0 ->
    fun b1 ->
      match (b0, b1) with
      | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
          (fun uu___ -> Success ((), FStar_Pervasives_Native.None))
      | (FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Implicit b01),
         FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Implicit b11)) ->
          (fun uu___ -> Success ((), FStar_Pervasives_Native.None))
      | (FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Equality),
         FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Equality)) ->
          (fun uu___ -> Success ((), FStar_Pervasives_Native.None))
      | (FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Meta t1),
         FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Meta t2)) ->
          let uu___ = equal_term t1 t2 in
          if uu___
          then (fun uu___1 -> Success ((), FStar_Pervasives_Native.None))
          else fail "Binder qualifier mismatch"
      | uu___ -> fail "Binder qualifier mismatch"
let (check_aqual :
  FStarC_Syntax_Syntax.aqual -> FStarC_Syntax_Syntax.aqual -> unit result) =
  fun a0 ->
    fun a1 ->
      match (a0, a1) with
      | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
          (fun uu___ -> Success ((), FStar_Pervasives_Native.None))
      | (FStar_Pervasives_Native.Some
         { FStarC_Syntax_Syntax.aqual_implicit = b0;
           FStarC_Syntax_Syntax.aqual_attributes = uu___;_},
         FStar_Pervasives_Native.Some
         { FStarC_Syntax_Syntax.aqual_implicit = b1;
           FStarC_Syntax_Syntax.aqual_attributes = uu___1;_})
          ->
          if b0 = b1
          then (fun uu___2 -> Success ((), FStar_Pervasives_Native.None))
          else
            (let uu___3 =
               let uu___4 = FStarC_Compiler_Util.string_of_bool b0 in
               let uu___5 = FStarC_Compiler_Util.string_of_bool b1 in
               FStarC_Compiler_Util.format2
                 "Unequal arg qualifiers: lhs implicit=%s and rhs implicit=%s"
                 uu___4 uu___5 in
             fail uu___3)
      | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some
         { FStarC_Syntax_Syntax.aqual_implicit = false;
           FStarC_Syntax_Syntax.aqual_attributes = uu___;_})
          -> (fun uu___1 -> Success ((), FStar_Pervasives_Native.None))
      | (FStar_Pervasives_Native.Some
         { FStarC_Syntax_Syntax.aqual_implicit = false;
           FStarC_Syntax_Syntax.aqual_attributes = uu___;_},
         FStar_Pervasives_Native.None) ->
          (fun uu___1 -> Success ((), FStar_Pervasives_Native.None))
      | uu___ ->
          let uu___1 =
            let uu___2 =
              FStarC_Class_Show.show FStarC_Syntax_Print.showable_aqual a0 in
            let uu___3 =
              FStarC_Class_Show.show FStarC_Syntax_Print.showable_aqual a1 in
            FStarC_Compiler_Util.format2
              "Unequal arg qualifiers: lhs %s and rhs %s" uu___2 uu___3 in
          fail uu___1
let (check_positivity_qual :
  relation ->
    FStarC_Syntax_Syntax.positivity_qualifier FStar_Pervasives_Native.option
      ->
      FStarC_Syntax_Syntax.positivity_qualifier
        FStar_Pervasives_Native.option -> unit result)
  =
  fun rel ->
    fun p0 ->
      fun p1 ->
        let uu___ =
          FStarC_TypeChecker_Common.check_positivity_qual
            (uu___is_SUBTYPING rel) p0 p1 in
        if uu___
        then fun uu___1 -> Success ((), FStar_Pervasives_Native.None)
        else fail "Unequal positivity qualifiers"
let (mk_forall_l :
  FStarC_Syntax_Syntax.universes ->
    FStarC_Syntax_Syntax.binders ->
      FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  =
  fun us ->
    fun xs ->
      fun t ->
        FStarC_Compiler_List.fold_right2
          (fun u ->
             fun x ->
               fun t1 ->
                 FStarC_Syntax_Util.mk_forall u
                   x.FStarC_Syntax_Syntax.binder_bv t1) us xs t
let (close_guard :
  FStarC_Syntax_Syntax.binders ->
    FStarC_Syntax_Syntax.universes -> precondition -> precondition)
  =
  fun xs ->
    fun us ->
      fun g ->
        match g with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some t ->
            let uu___ = mk_forall_l us xs t in
            FStar_Pervasives_Native.Some uu___
let (close_guard_with_definition :
  FStarC_Syntax_Syntax.binder ->
    FStarC_Syntax_Syntax.universe ->
      FStarC_Syntax_Syntax.term -> precondition -> precondition)
  =
  fun x ->
    fun u ->
      fun t ->
        fun g ->
          match g with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some t1 ->
              let uu___ =
                let t2 =
                  let uu___1 =
                    let uu___2 =
                      FStarC_Syntax_Syntax.bv_to_name
                        x.FStarC_Syntax_Syntax.binder_bv in
                    FStarC_Syntax_Util.mk_eq2 u
                      (x.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort
                      uu___2 t1 in
                  FStarC_Syntax_Util.mk_imp uu___1 t1 in
                FStarC_Syntax_Util.mk_forall u
                  x.FStarC_Syntax_Syntax.binder_bv t2 in
              FStar_Pervasives_Native.Some uu___
let with_binders :
  'a .
    FStarC_Syntax_Syntax.binders ->
      FStarC_Syntax_Syntax.universes -> 'a result -> 'a result
  =
  fun xs ->
    fun us ->
      fun f ->
        fun ctx ->
          let uu___ = f ctx in
          match uu___ with
          | Success (t, g) ->
              let uu___1 = let uu___2 = close_guard xs us g in (t, uu___2) in
              Success uu___1
          | err -> err
let with_definition :
  'a .
    FStarC_Syntax_Syntax.binder ->
      FStarC_Syntax_Syntax.universe ->
        FStarC_Syntax_Syntax.term -> 'a result -> 'a result
  =
  fun x ->
    fun u ->
      fun t ->
        fun f ->
          fun ctx ->
            let uu___ = f ctx in
            match uu___ with
            | Success (a1, g) ->
                let uu___1 =
                  let uu___2 = close_guard_with_definition x u t g in
                  (a1, uu___2) in
                Success uu___1
            | err -> err
let (guard : FStarC_Syntax_Syntax.typ -> unit result) =
  fun t -> fun uu___ -> Success ((), (FStar_Pervasives_Native.Some t))
let (abs :
  FStarC_Syntax_Syntax.typ ->
    (FStarC_Syntax_Syntax.binder -> FStarC_Syntax_Syntax.term) ->
      FStarC_Syntax_Syntax.term)
  =
  fun a ->
    fun f ->
      let x = FStarC_Syntax_Syntax.new_bv FStar_Pervasives_Native.None a in
      let xb = FStarC_Syntax_Syntax.mk_binder x in
      let uu___ = f xb in
      FStarC_Syntax_Util.abs [xb] uu___ FStar_Pervasives_Native.None
let (weaken_subtyping_guard :
  FStarC_Syntax_Syntax.term -> precondition -> precondition) =
  fun p ->
    fun g ->
      FStarC_Compiler_Util.map_opt g (fun q -> FStarC_Syntax_Util.mk_imp p q)
let (strengthen_subtyping_guard :
  FStarC_Syntax_Syntax.term -> precondition -> precondition) =
  fun p ->
    fun g ->
      let uu___ =
        let uu___1 =
          FStarC_Compiler_Util.map_opt g
            (fun q -> FStarC_Syntax_Util.mk_conj p q) in
        FStarC_Compiler_Util.dflt p uu___1 in
      FStar_Pervasives_Native.Some uu___
let weaken :
  'a .
    FStarC_Syntax_Syntax.term -> 'a result -> context -> 'a success __result
  =
  fun p ->
    fun g ->
      fun ctx ->
        let uu___ = g ctx in
        match uu___ with
        | Success (x, q) ->
            let uu___1 =
              let uu___2 = weaken_subtyping_guard p q in (x, uu___2) in
            Success uu___1
        | err -> err
let weaken_with_guard_formula :
  'a .
    FStarC_TypeChecker_Common.guard_formula ->
      'a result -> context -> 'a success __result
  =
  fun p ->
    fun g ->
      match p with
      | FStarC_TypeChecker_Common.Trivial -> g
      | FStarC_TypeChecker_Common.NonTrivial p1 -> weaken p1 g
let (push_hypothesis : env -> FStarC_Syntax_Syntax.term -> env) =
  fun g ->
    fun h ->
      let bv =
        FStarC_Syntax_Syntax.new_bv
          (FStar_Pervasives_Native.Some (h.FStarC_Syntax_Syntax.pos)) h in
      let b = FStarC_Syntax_Syntax.mk_binder bv in
      let uu___ = fresh_binder g b in FStar_Pervasives_Native.fst uu___
let strengthen :
  'a .
    FStarC_Syntax_Syntax.term -> 'a result -> context -> 'a success __result
  =
  fun p ->
    fun g ->
      fun ctx ->
        let uu___ = g ctx in
        match uu___ with
        | Success (x, q) ->
            let uu___1 =
              let uu___2 = strengthen_subtyping_guard p q in (x, uu___2) in
            Success uu___1
        | err -> err
let no_guard : 'a . 'a result -> 'a result =
  fun g ->
    fun ctx ->
      let uu___ =
        g
          {
            no_guard = true;
            unfolding_ok = (ctx.unfolding_ok);
            error_context = (ctx.error_context)
          } in
      match uu___ with
      | Success (x, FStar_Pervasives_Native.None) ->
          Success (x, FStar_Pervasives_Native.None)
      | Success (x, FStar_Pervasives_Native.Some g1) ->
          let uu___1 =
            let uu___2 =
              let uu___3 =
                FStarC_Class_Show.show FStarC_Syntax_Print.showable_term g1 in
              FStarC_Compiler_Util.format1 "Unexpected guard: %s" uu___3 in
            fail uu___2 in
          uu___1 ctx
      | err -> err
let (equatable : env -> FStarC_Syntax_Syntax.term -> Prims.bool) =
  fun g ->
    fun t ->
      let uu___ = FStarC_Syntax_Util.leftmost_head t in
      FStarC_TypeChecker_Rel.may_relate_with_logical_guard g.tcenv true uu___
let (apply_predicate :
  FStarC_Syntax_Syntax.binder ->
    FStarC_Syntax_Syntax.term ->
      FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
        FStarC_Syntax_Syntax.term)
  =
  fun x ->
    fun p ->
      fun e ->
        FStarC_Syntax_Subst.subst
          [FStarC_Syntax_Syntax.NT ((x.FStarC_Syntax_Syntax.binder_bv), e)] p
let (curry_arrow :
  FStarC_Syntax_Syntax.binder ->
    FStarC_Syntax_Syntax.binders ->
      FStarC_Syntax_Syntax.comp ->
        FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  =
  fun x ->
    fun xs ->
      fun c ->
        let tail =
          FStarC_Syntax_Syntax.mk
            (FStarC_Syntax_Syntax.Tm_arrow
               { FStarC_Syntax_Syntax.bs1 = xs; FStarC_Syntax_Syntax.comp = c
               }) FStarC_Compiler_Range_Type.dummyRange in
        let uu___ =
          let uu___1 =
            let uu___2 = FStarC_Syntax_Syntax.mk_Total tail in
            {
              FStarC_Syntax_Syntax.bs1 = [x];
              FStarC_Syntax_Syntax.comp = uu___2
            } in
          FStarC_Syntax_Syntax.Tm_arrow uu___1 in
        FStarC_Syntax_Syntax.mk uu___ FStarC_Compiler_Range_Type.dummyRange
let (curry_abs :
  FStarC_Syntax_Syntax.binder ->
    FStarC_Syntax_Syntax.binder ->
      FStarC_Syntax_Syntax.binders ->
        FStarC_Syntax_Syntax.term ->
          FStarC_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option
            -> FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  =
  fun b0 ->
    fun b1 ->
      fun bs ->
        fun body ->
          fun ropt ->
            let tail =
              FStarC_Syntax_Syntax.mk
                (FStarC_Syntax_Syntax.Tm_abs
                   {
                     FStarC_Syntax_Syntax.bs = (b1 :: bs);
                     FStarC_Syntax_Syntax.body = body;
                     FStarC_Syntax_Syntax.rc_opt = ropt
                   }) body.FStarC_Syntax_Syntax.pos in
            FStarC_Syntax_Syntax.mk
              (FStarC_Syntax_Syntax.Tm_abs
                 {
                   FStarC_Syntax_Syntax.bs = [b0];
                   FStarC_Syntax_Syntax.body = tail;
                   FStarC_Syntax_Syntax.rc_opt = FStar_Pervasives_Native.None
                 }) body.FStarC_Syntax_Syntax.pos
let (is_gtot_comp :
  FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax -> Prims.bool) =
  fun c ->
    (FStarC_Syntax_Util.is_tot_or_gtot_comp c) &&
      (let uu___ = FStarC_Syntax_Util.is_total_comp c in
       Prims.op_Negation uu___)
let rec (context_included :
  FStarC_Syntax_Syntax.binding Prims.list ->
    FStarC_Syntax_Syntax.binding Prims.list -> Prims.bool)
  =
  fun g0 ->
    fun g1 ->
      let uu___ = FStarC_Compiler_Util.physical_equality g0 g1 in
      if uu___
      then true
      else
        (match (g0, g1) with
         | ([], uu___2) -> true
         | (b0::g0', b1::g1') ->
             (match (b0, b1) with
              | (FStarC_Syntax_Syntax.Binding_var x0,
                 FStarC_Syntax_Syntax.Binding_var x1) ->
                  if
                    x0.FStarC_Syntax_Syntax.index =
                      x1.FStarC_Syntax_Syntax.index
                  then
                    (equal_term x0.FStarC_Syntax_Syntax.sort
                       x1.FStarC_Syntax_Syntax.sort)
                      && (context_included g0' g1')
                  else context_included g0 g1'
              | (FStarC_Syntax_Syntax.Binding_lid uu___2,
                 FStarC_Syntax_Syntax.Binding_lid uu___3) -> true
              | (FStarC_Syntax_Syntax.Binding_univ uu___2,
                 FStarC_Syntax_Syntax.Binding_univ uu___3) -> true
              | uu___2 -> false)
         | uu___2 -> false)
let (curry_application :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
    (FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax *
      FStarC_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) ->
      (FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax *
        FStarC_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        Prims.list ->
        FStarC_Compiler_Range_Type.range ->
          FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  =
  fun hd ->
    fun arg ->
      fun args ->
        fun p ->
          let head =
            FStarC_Syntax_Syntax.mk
              (FStarC_Syntax_Syntax.Tm_app
                 {
                   FStarC_Syntax_Syntax.hd = hd;
                   FStarC_Syntax_Syntax.args = [arg]
                 }) p in
          let t =
            FStarC_Syntax_Syntax.mk
              (FStarC_Syntax_Syntax.Tm_app
                 {
                   FStarC_Syntax_Syntax.hd = head;
                   FStarC_Syntax_Syntax.args = args
                 }) p in
          t
let (lookup :
  env ->
    FStarC_Syntax_Syntax.term ->
      (tot_or_ghost * FStarC_Syntax_Syntax.typ) result)
  =
  fun g ->
    fun e ->
      let uu___ = FStarC_Syntax_TermHashTable.lookup e table in
      match uu___ with
      | FStar_Pervasives_Native.None ->
          (record_cache_miss (); fail "not in cache")
      | FStar_Pervasives_Native.Some he ->
          let uu___1 =
            context_included he.he_gamma
              (g.tcenv).FStarC_TypeChecker_Env.gamma in
          if uu___1
          then
            (record_cache_hit ();
             (let uu___4 = FStarC_Compiler_Effect.op_Bang dbg in
              if uu___4
              then
                let uu___5 =
                  FStarC_Class_Show.show
                    (FStarC_Class_Show.show_list
                       FStarC_Syntax_Print.showable_binding)
                    (g.tcenv).FStarC_TypeChecker_Env.gamma in
                let uu___6 =
                  FStarC_Class_Show.show FStarC_Syntax_Print.showable_term e in
                let uu___7 =
                  FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                    (FStar_Pervasives_Native.snd
                       (FStar_Pervasives_Native.fst he.he_res)) in
                let uu___8 =
                  FStarC_Class_Show.show
                    (FStarC_Class_Show.show_list
                       FStarC_Syntax_Print.showable_binding) he.he_gamma in
                FStarC_Compiler_Util.print4
                  "cache hit\n %s |- %s : %s\nmatching env %s\n" uu___5
                  uu___6 uu___7 uu___8
              else ());
             (fun uu___4 -> Success (he.he_res)))
          else fail "not in cache"
let (check_no_escape :
  FStarC_Syntax_Syntax.binders -> FStarC_Syntax_Syntax.term -> unit result) =
  fun bs ->
    fun t ->
      let xs = FStarC_Syntax_Free.names t in
      let uu___ =
        FStarC_Compiler_Util.for_all
          (fun b ->
             let uu___1 =
               FStarC_Class_Setlike.mem ()
                 (Obj.magic
                    (FStarC_Compiler_FlatSet.setlike_flat_set
                       FStarC_Syntax_Syntax.ord_bv))
                 b.FStarC_Syntax_Syntax.binder_bv (Obj.magic xs) in
             Prims.op_Negation uu___1) bs in
      if uu___
      then fun uu___1 -> Success ((), FStar_Pervasives_Native.None)
      else fail "Name escapes its scope"
let rec map :
  'a 'b . ('a -> 'b result) -> 'a Prims.list -> 'b Prims.list result =
  fun f ->
    fun l ->
      match l with
      | [] -> (fun uu___ -> Success ([], FStar_Pervasives_Native.None))
      | hd::tl ->
          let uu___ = f hd in
          (fun ctx0 ->
             let uu___1 = uu___ ctx0 in
             match uu___1 with
             | Success (x, g1) ->
                 let uu___2 =
                   let uu___3 =
                     let uu___4 = map f tl in
                     fun ctx01 ->
                       let uu___5 = uu___4 ctx01 in
                       match uu___5 with
                       | Success (x1, g11) ->
                           let uu___6 =
                             let uu___7 uu___8 =
                               Success
                                 ((x :: x1), FStar_Pervasives_Native.None) in
                             uu___7 ctx01 in
                           (match uu___6 with
                            | Success (y, g2) ->
                                let uu___7 =
                                  let uu___8 = and_pre g11 g2 in (y, uu___8) in
                                Success uu___7
                            | err -> err)
                       | Error err -> Error err in
                   uu___3 ctx0 in
                 (match uu___2 with
                  | Success (y, g2) ->
                      let uu___3 = let uu___4 = and_pre g1 g2 in (y, uu___4) in
                      Success uu___3
                  | err -> err)
             | Error err -> Error err)
let mapi :
  'a 'b .
    (Prims.int -> 'a -> 'b result) -> 'a Prims.list -> 'b Prims.list result
  =
  fun f ->
    fun l ->
      let rec aux i l1 =
        match l1 with
        | [] -> (fun uu___ -> Success ([], FStar_Pervasives_Native.None))
        | hd::tl ->
            let uu___ = f i hd in
            (fun ctx0 ->
               let uu___1 = uu___ ctx0 in
               match uu___1 with
               | Success (x, g1) ->
                   let uu___2 =
                     let uu___3 =
                       let uu___4 = aux (i + Prims.int_one) tl in
                       fun ctx01 ->
                         let uu___5 = uu___4 ctx01 in
                         match uu___5 with
                         | Success (x1, g11) ->
                             let uu___6 =
                               let uu___7 uu___8 =
                                 Success
                                   ((x :: x1), FStar_Pervasives_Native.None) in
                               uu___7 ctx01 in
                             (match uu___6 with
                              | Success (y, g2) ->
                                  let uu___7 =
                                    let uu___8 = and_pre g11 g2 in
                                    (y, uu___8) in
                                  Success uu___7
                              | err -> err)
                         | Error err -> Error err in
                     uu___3 ctx0 in
                   (match uu___2 with
                    | Success (y, g2) ->
                        let uu___3 =
                          let uu___4 = and_pre g1 g2 in (y, uu___4) in
                        Success uu___3
                    | err -> err)
               | Error err -> Error err) in
      aux Prims.int_zero l
let rec map2 :
  'a 'b 'c .
    ('a -> 'b -> 'c result) ->
      'a Prims.list -> 'b Prims.list -> 'c Prims.list result
  =
  fun f ->
    fun l1 ->
      fun l2 ->
        match (l1, l2) with
        | ([], []) ->
            (fun uu___ -> Success ([], FStar_Pervasives_Native.None))
        | (hd1::tl1, hd2::tl2) ->
            let uu___ = f hd1 hd2 in
            (fun ctx0 ->
               let uu___1 = uu___ ctx0 in
               match uu___1 with
               | Success (x, g1) ->
                   let uu___2 =
                     let uu___3 =
                       let uu___4 = map2 f tl1 tl2 in
                       fun ctx01 ->
                         let uu___5 = uu___4 ctx01 in
                         match uu___5 with
                         | Success (x1, g11) ->
                             let uu___6 =
                               let uu___7 uu___8 =
                                 Success
                                   ((x :: x1), FStar_Pervasives_Native.None) in
                               uu___7 ctx01 in
                             (match uu___6 with
                              | Success (y, g2) ->
                                  let uu___7 =
                                    let uu___8 = and_pre g11 g2 in
                                    (y, uu___8) in
                                  Success uu___7
                              | err -> err)
                         | Error err -> Error err in
                     uu___3 ctx0 in
                   (match uu___2 with
                    | Success (y, g2) ->
                        let uu___3 =
                          let uu___4 = and_pre g1 g2 in (y, uu___4) in
                        Success uu___3
                    | err -> err)
               | Error err -> Error err)
let rec fold :
  'a 'b . ('a -> 'b -> 'a result) -> 'a -> 'b Prims.list -> 'a result =
  fun f ->
    fun x ->
      fun l ->
        match l with
        | [] -> (fun uu___ -> Success (x, FStar_Pervasives_Native.None))
        | hd::tl ->
            let uu___ = f x hd in
            (fun ctx0 ->
               let uu___1 = uu___ ctx0 in
               match uu___1 with
               | Success (x1, g1) ->
                   let uu___2 = let uu___3 = fold f x1 tl in uu___3 ctx0 in
                   (match uu___2 with
                    | Success (y, g2) ->
                        let uu___3 =
                          let uu___4 = and_pre g1 g2 in (y, uu___4) in
                        Success uu___3
                    | err -> err)
               | Error err -> Error err)
let rec fold2 :
  'a 'b 'c .
    ('a -> 'b -> 'c -> 'a result) ->
      'a -> 'b Prims.list -> 'c Prims.list -> 'a result
  =
  fun f ->
    fun x ->
      fun l1 ->
        fun l2 ->
          match (l1, l2) with
          | ([], []) ->
              (fun uu___ -> Success (x, FStar_Pervasives_Native.None))
          | (hd1::tl1, hd2::tl2) ->
              let uu___ = f x hd1 hd2 in
              (fun ctx0 ->
                 let uu___1 = uu___ ctx0 in
                 match uu___1 with
                 | Success (x1, g1) ->
                     let uu___2 =
                       let uu___3 = fold2 f x1 tl1 tl2 in uu___3 ctx0 in
                     (match uu___2 with
                      | Success (y, g2) ->
                          let uu___3 =
                            let uu___4 = and_pre g1 g2 in (y, uu___4) in
                          Success uu___3
                      | err -> err)
                 | Error err -> Error err)
let rec iter2 :
  'a 'b .
    'a Prims.list ->
      'a Prims.list -> ('a -> 'a -> 'b -> 'b result) -> 'b -> 'b result
  =
  fun xs ->
    fun ys ->
      fun f ->
        fun b1 ->
          match (xs, ys) with
          | ([], []) ->
              (fun uu___ -> Success (b1, FStar_Pervasives_Native.None))
          | (x::xs1, y::ys1) ->
              let uu___ = f x y b1 in
              (fun ctx0 ->
                 let uu___1 = uu___ ctx0 in
                 match uu___1 with
                 | Success (x1, g1) ->
                     let uu___2 =
                       let uu___3 = iter2 xs1 ys1 f x1 in uu___3 ctx0 in
                     (match uu___2 with
                      | Success (y1, g2) ->
                          let uu___3 =
                            let uu___4 = and_pre g1 g2 in (y1, uu___4) in
                          Success uu___3
                      | err -> err)
                 | Error err -> Error err)
          | uu___ -> fail "Lists of differing length"
let (is_non_informative :
  FStarC_TypeChecker_Env.env -> FStarC_Syntax_Syntax.typ -> Prims.bool) =
  fun g -> fun t -> FStarC_TypeChecker_Normalize.non_info_norm g t
let (non_informative : env -> FStarC_Syntax_Syntax.typ -> Prims.bool) =
  fun g -> fun t -> is_non_informative g.tcenv t
let (as_comp :
  env ->
    (tot_or_ghost * FStarC_Syntax_Syntax.typ) -> FStarC_Syntax_Syntax.comp)
  =
  fun g ->
    fun et ->
      match et with
      | (E_Total, t) -> FStarC_Syntax_Syntax.mk_Total t
      | (E_Ghost, t) ->
          let uu___ = non_informative g t in
          if uu___
          then FStarC_Syntax_Syntax.mk_Total t
          else FStarC_Syntax_Syntax.mk_GTotal t
let (comp_as_tot_or_ghost_and_type :
  FStarC_Syntax_Syntax.comp ->
    (tot_or_ghost * FStarC_Syntax_Syntax.typ) FStar_Pervasives_Native.option)
  =
  fun c ->
    let uu___ = FStarC_Syntax_Util.is_total_comp c in
    if uu___
    then
      FStar_Pervasives_Native.Some
        (E_Total, (FStarC_Syntax_Util.comp_result c))
    else
      (let uu___2 = FStarC_Syntax_Util.is_tot_or_gtot_comp c in
       if uu___2
       then
         FStar_Pervasives_Native.Some
           (E_Ghost, (FStarC_Syntax_Util.comp_result c))
       else FStar_Pervasives_Native.None)
let (join_eff : tot_or_ghost -> tot_or_ghost -> tot_or_ghost) =
  fun e0 ->
    fun e1 ->
      match (e0, e1) with
      | (E_Ghost, uu___) -> E_Ghost
      | (uu___, E_Ghost) -> E_Ghost
      | uu___ -> E_Total
let (join_eff_l : tot_or_ghost Prims.list -> tot_or_ghost) =
  fun es -> FStar_List_Tot_Base.fold_right join_eff es E_Total
let (guard_not_allowed : Prims.bool result) =
  fun ctx -> Success ((ctx.no_guard), FStar_Pervasives_Native.None)
let (unfolding_ok : Prims.bool result) =
  fun ctx -> Success ((ctx.unfolding_ok), FStar_Pervasives_Native.None)
let debug : 'uuuuu . 'uuuuu -> (unit -> unit) -> unit =
  fun g ->
    fun f ->
      let uu___ = FStarC_Compiler_Effect.op_Bang dbg in
      if uu___ then f () else ()
let (showable_side : side FStarC_Class_Show.showable) =
  {
    FStarC_Class_Show.show =
      (fun uu___ ->
         match uu___ with
         | Left -> "Left"
         | Right -> "Right"
         | Both -> "Both"
         | Neither -> "Neither")
  }
let (boolean_negation_simp :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun b ->
    let uu___ =
      FStarC_Syntax_Hash.equal_term b FStarC_Syntax_Util.exp_false_bool in
    if uu___
    then FStar_Pervasives_Native.None
    else
      (let uu___2 = FStarC_Syntax_Util.mk_boolean_negation b in
       FStar_Pervasives_Native.Some uu___2)
let (combine_path_and_branch_condition :
  FStarC_Syntax_Syntax.term ->
    FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStarC_Syntax_Syntax.term ->
        (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.term))
  =
  fun path_condition ->
    fun branch_condition ->
      fun branch_equality ->
        let this_path_condition =
          let bc =
            match branch_condition with
            | FStar_Pervasives_Native.None -> branch_equality
            | FStar_Pervasives_Native.Some bc1 ->
                let uu___ =
                  let uu___1 = FStarC_Syntax_Util.b2t bc1 in
                  [uu___1; branch_equality] in
                FStarC_Syntax_Util.mk_conj_l uu___ in
          let uu___ = FStarC_Syntax_Util.b2t path_condition in
          FStarC_Syntax_Util.mk_conj uu___ bc in
        let next_path_condition =
          match branch_condition with
          | FStar_Pervasives_Native.None -> FStarC_Syntax_Util.exp_false_bool
          | FStar_Pervasives_Native.Some bc ->
              let uu___ =
                FStarC_Syntax_Hash.equal_term path_condition
                  FStarC_Syntax_Util.exp_true_bool in
              if uu___
              then FStarC_Syntax_Util.mk_boolean_negation bc
              else
                (let uu___2 = FStarC_Syntax_Util.mk_boolean_negation bc in
                 FStarC_Syntax_Util.mk_and path_condition uu___2) in
        (this_path_condition, next_path_condition)
let (maybe_relate_after_unfolding :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term -> side)
  =
  fun g ->
    fun t0 ->
      fun t1 ->
        let dd0 = FStarC_TypeChecker_Env.delta_depth_of_term g t0 in
        let dd1 = FStarC_TypeChecker_Env.delta_depth_of_term g t1 in
        if dd0 = dd1
        then Both
        else
          (let uu___1 =
             FStarC_TypeChecker_Common.delta_depth_greater_than dd0 dd1 in
           if uu___1 then Left else Right)
let rec (check_relation :
  env ->
    relation ->
      FStarC_Syntax_Syntax.typ -> FStarC_Syntax_Syntax.typ -> unit result)
  =
  fun g ->
    fun rel ->
      fun t0 ->
        fun t1 ->
          let err uu___ =
            match rel with
            | EQUALITY ->
                let uu___1 =
                  let uu___2 =
                    FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                      t0 in
                  let uu___3 =
                    FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                      t1 in
                  FStarC_Compiler_Util.format2 "not equal terms: %s <> %s"
                    uu___2 uu___3 in
                fail uu___1
            | uu___1 ->
                let uu___2 =
                  let uu___3 =
                    FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                      t0 in
                  let uu___4 =
                    FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                      t1 in
                  FStarC_Compiler_Util.format2 "%s is not a subtype of %s"
                    uu___3 uu___4 in
                fail uu___2 in
          let rel_to_string rel1 =
            match rel1 with | EQUALITY -> "=?=" | SUBTYPING uu___ -> "<:?" in
          (let uu___1 = FStarC_Compiler_Effect.op_Bang dbg in
           if uu___1
           then
             let uu___2 =
               FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term t0 in
             let uu___3 =
               FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t0 in
             let uu___4 =
               FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term t1 in
             let uu___5 =
               FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t1 in
             FStarC_Compiler_Util.print5
               "check_relation (%s) %s %s (%s) %s\n" uu___2 uu___3
               (rel_to_string rel) uu___4 uu___5
           else ());
          (fun ctx0 ->
             let uu___1 = guard_not_allowed ctx0 in
             match uu___1 with
             | Success (x, g1) ->
                 let uu___2 =
                   let uu___3 =
                     let guard_ok = Prims.op_Negation x in
                     let head_matches t01 t11 =
                       let head0 = FStarC_Syntax_Util.leftmost_head t01 in
                       let head1 = FStarC_Syntax_Util.leftmost_head t11 in
                       let uu___4 =
                         let uu___5 =
                           let uu___6 = FStarC_Syntax_Util.un_uinst head0 in
                           uu___6.FStarC_Syntax_Syntax.n in
                         let uu___6 =
                           let uu___7 = FStarC_Syntax_Util.un_uinst head1 in
                           uu___7.FStarC_Syntax_Syntax.n in
                         (uu___5, uu___6) in
                       match uu___4 with
                       | (FStarC_Syntax_Syntax.Tm_fvar fv0,
                          FStarC_Syntax_Syntax.Tm_fvar fv1) ->
                           FStarC_Syntax_Syntax.fv_eq fv0 fv1
                       | (FStarC_Syntax_Syntax.Tm_name x0,
                          FStarC_Syntax_Syntax.Tm_name x1) ->
                           FStarC_Syntax_Syntax.bv_eq x0 x1
                       | (FStarC_Syntax_Syntax.Tm_constant c0,
                          FStarC_Syntax_Syntax.Tm_constant c1) ->
                           equal_term head0 head1
                       | (FStarC_Syntax_Syntax.Tm_type uu___5,
                          FStarC_Syntax_Syntax.Tm_type uu___6) -> true
                       | (FStarC_Syntax_Syntax.Tm_arrow uu___5,
                          FStarC_Syntax_Syntax.Tm_arrow uu___6) -> true
                       | (FStarC_Syntax_Syntax.Tm_match uu___5,
                          FStarC_Syntax_Syntax.Tm_match uu___6) -> true
                       | uu___5 -> false in
                     let which_side_to_unfold t01 t11 =
                       maybe_relate_after_unfolding g.tcenv t01 t11 in
                     let maybe_unfold_side side1 t01 t11 =
                       FStarC_Profiling.profile
                         (fun uu___4 ->
                            match side1 with
                            | Neither -> FStar_Pervasives_Native.None
                            | Both ->
                                let uu___5 =
                                  let uu___6 =
                                    FStarC_TypeChecker_Normalize.maybe_unfold_head
                                      g.tcenv t01 in
                                  let uu___7 =
                                    FStarC_TypeChecker_Normalize.maybe_unfold_head
                                      g.tcenv t11 in
                                  (uu___6, uu___7) in
                                (match uu___5 with
                                 | (FStar_Pervasives_Native.Some t02,
                                    FStar_Pervasives_Native.Some t12) ->
                                     FStar_Pervasives_Native.Some (t02, t12)
                                 | (FStar_Pervasives_Native.Some t02,
                                    FStar_Pervasives_Native.None) ->
                                     FStar_Pervasives_Native.Some (t02, t11)
                                 | (FStar_Pervasives_Native.None,
                                    FStar_Pervasives_Native.Some t12) ->
                                     FStar_Pervasives_Native.Some (t01, t12)
                                 | uu___6 -> FStar_Pervasives_Native.None)
                            | Left ->
                                let uu___5 =
                                  FStarC_TypeChecker_Normalize.maybe_unfold_head
                                    g.tcenv t01 in
                                (match uu___5 with
                                 | FStar_Pervasives_Native.Some t02 ->
                                     FStar_Pervasives_Native.Some (t02, t11)
                                 | uu___6 -> FStar_Pervasives_Native.None)
                            | Right ->
                                let uu___5 =
                                  FStarC_TypeChecker_Normalize.maybe_unfold_head
                                    g.tcenv t11 in
                                (match uu___5 with
                                 | FStar_Pervasives_Native.Some t12 ->
                                     FStar_Pervasives_Native.Some (t01, t12)
                                 | uu___6 -> FStar_Pervasives_Native.None))
                         FStar_Pervasives_Native.None
                         "FStarC.TypeChecker.Core.maybe_unfold_side" in
                     let maybe_unfold t01 t11 ctx01 =
                       let uu___4 = unfolding_ok ctx01 in
                       match uu___4 with
                       | Success (x1, g11) ->
                           let uu___5 =
                             let uu___6 =
                               if x1
                               then
                                 let uu___7 =
                                   let uu___8 = which_side_to_unfold t01 t11 in
                                   maybe_unfold_side uu___8 t01 t11 in
                                 fun uu___8 ->
                                   Success
                                     (uu___7, FStar_Pervasives_Native.None)
                               else
                                 (fun uu___8 ->
                                    Success
                                      (FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None)) in
                             uu___6 ctx01 in
                           (match uu___5 with
                            | Success (y, g2) ->
                                let uu___6 =
                                  let uu___7 = and_pre g11 g2 in (y, uu___7) in
                                Success uu___6
                            | err1 -> err1)
                       | Error err1 -> Error err1 in
                     let emit_guard t01 t11 =
                       let uu___4 ctx =
                         let ctx1 =
                           {
                             no_guard = (ctx.no_guard);
                             unfolding_ok = (ctx.unfolding_ok);
                             error_context =
                               (("checking lhs while emitting guard",
                                  FStar_Pervasives_Native.None) ::
                               (ctx.error_context))
                           } in
                         let uu___5 = do_check g t01 in uu___5 ctx1 in
                       fun ctx01 ->
                         let uu___5 = uu___4 ctx01 in
                         match uu___5 with
                         | Success (x1, g11) ->
                             let uu___6 =
                               let uu___7 =
                                 match x1 with
                                 | (uu___8, t_typ) ->
                                     let uu___9 = universe_of g t_typ in
                                     (fun ctx02 ->
                                        let uu___10 = uu___9 ctx02 in
                                        match uu___10 with
                                        | Success (x2, g12) ->
                                            let uu___11 =
                                              let uu___12 =
                                                let uu___13 =
                                                  FStarC_Syntax_Util.mk_eq2
                                                    x2 t_typ t01 t11 in
                                                guard uu___13 in
                                              uu___12 ctx02 in
                                            (match uu___11 with
                                             | Success (y, g2) ->
                                                 let uu___12 =
                                                   let uu___13 =
                                                     and_pre g12 g2 in
                                                   ((), uu___13) in
                                                 Success uu___12
                                             | err1 -> err1)
                                        | Error err1 -> Error err1) in
                               uu___7 ctx01 in
                             (match uu___6 with
                              | Success (y, g2) ->
                                  let uu___7 =
                                    let uu___8 = and_pre g11 g2 in
                                    ((), uu___8) in
                                  Success uu___7
                              | err1 -> err1)
                         | Error err1 -> Error err1 in
                     let fallback t01 t11 =
                       if guard_ok
                       then
                         let uu___4 = (equatable g t01) || (equatable g t11) in
                         (if uu___4 then emit_guard t01 t11 else err ())
                       else err () in
                     let maybe_unfold_side_and_retry side1 t01 t11 ctx01 =
                       let uu___4 = unfolding_ok ctx01 in
                       match uu___4 with
                       | Success (x1, g11) ->
                           let uu___5 =
                             let uu___6 =
                               if x1
                               then
                                 let uu___7 = maybe_unfold_side side1 t01 t11 in
                                 match uu___7 with
                                 | FStar_Pervasives_Native.None ->
                                     fallback t01 t11
                                 | FStar_Pervasives_Native.Some (t02, t12) ->
                                     check_relation g rel t02 t12
                               else fallback t01 t11 in
                             uu___6 ctx01 in
                           (match uu___5 with
                            | Success (y, g2) ->
                                let uu___6 =
                                  let uu___7 = and_pre g11 g2 in ((), uu___7) in
                                Success uu___6
                            | err1 -> err1)
                       | Error err1 -> Error err1 in
                     let maybe_unfold_and_retry t01 t11 =
                       let uu___4 = which_side_to_unfold t01 t11 in
                       maybe_unfold_side_and_retry uu___4 t01 t11 in
                     let beta_iota_reduce t =
                       let t2 = FStarC_Syntax_Subst.compress t in
                       let t3 =
                         FStarC_TypeChecker_Normalize.normalize
                           [FStarC_TypeChecker_Env.HNF;
                           FStarC_TypeChecker_Env.Weak;
                           FStarC_TypeChecker_Env.Beta;
                           FStarC_TypeChecker_Env.Iota;
                           FStarC_TypeChecker_Env.Primops] g.tcenv t2 in
                       match t3.FStarC_Syntax_Syntax.n with
                       | FStarC_Syntax_Syntax.Tm_refine uu___4 ->
                           FStarC_Syntax_Util.flatten_refinement t3
                       | uu___4 -> t3 in
                     let beta_iota_reduce1 t =
                       FStarC_Profiling.profile
                         (fun uu___4 -> beta_iota_reduce t)
                         FStar_Pervasives_Native.None
                         "FStarC.TypeChecker.Core.beta_iota_reduce" in
                     let t01 =
                       let uu___4 =
                         let uu___5 = beta_iota_reduce1 t0 in
                         FStarC_Syntax_Subst.compress uu___5 in
                       FStarC_Syntax_Util.unlazy_emb uu___4 in
                     let t11 =
                       let uu___4 =
                         let uu___5 = beta_iota_reduce1 t1 in
                         FStarC_Syntax_Subst.compress uu___5 in
                       FStarC_Syntax_Util.unlazy_emb uu___4 in
                     let check_relation1 g2 rel1 t02 t12 ctx =
                       let ctx1 =
                         {
                           no_guard = (ctx.no_guard);
                           unfolding_ok = (ctx.unfolding_ok);
                           error_context =
                             (("check_relation",
                                (FStar_Pervasives_Native.Some
                                   (CtxRel (t02, rel1, t12)))) ::
                             (ctx.error_context))
                         } in
                       let uu___4 = check_relation g2 rel1 t02 t12 in
                       uu___4 ctx1 in
                     let uu___4 = equal_term t01 t11 in
                     if uu___4
                     then
                       fun uu___5 ->
                         Success ((), FStar_Pervasives_Native.None)
                     else
                       (match ((t01.FStarC_Syntax_Syntax.n),
                                (t11.FStarC_Syntax_Syntax.n))
                        with
                        | (FStarC_Syntax_Syntax.Tm_type u0,
                           FStarC_Syntax_Syntax.Tm_type u1) ->
                            let uu___6 =
                              FStarC_TypeChecker_Rel.teq_nosmt_force 
                                g.tcenv t01 t11 in
                            if uu___6
                            then
                              (fun uu___7 ->
                                 Success ((), FStar_Pervasives_Native.None))
                            else err ()
                        | (FStarC_Syntax_Syntax.Tm_meta
                           { FStarC_Syntax_Syntax.tm2 = t02;
                             FStarC_Syntax_Syntax.meta =
                               FStarC_Syntax_Syntax.Meta_pattern uu___6;_},
                           uu___7) -> check_relation1 g rel t02 t11
                        | (FStarC_Syntax_Syntax.Tm_meta
                           { FStarC_Syntax_Syntax.tm2 = t02;
                             FStarC_Syntax_Syntax.meta =
                               FStarC_Syntax_Syntax.Meta_named uu___6;_},
                           uu___7) -> check_relation1 g rel t02 t11
                        | (FStarC_Syntax_Syntax.Tm_meta
                           { FStarC_Syntax_Syntax.tm2 = t02;
                             FStarC_Syntax_Syntax.meta =
                               FStarC_Syntax_Syntax.Meta_labeled uu___6;_},
                           uu___7) -> check_relation1 g rel t02 t11
                        | (FStarC_Syntax_Syntax.Tm_meta
                           { FStarC_Syntax_Syntax.tm2 = t02;
                             FStarC_Syntax_Syntax.meta =
                               FStarC_Syntax_Syntax.Meta_desugared uu___6;_},
                           uu___7) -> check_relation1 g rel t02 t11
                        | (FStarC_Syntax_Syntax.Tm_ascribed
                           { FStarC_Syntax_Syntax.tm = t02;
                             FStarC_Syntax_Syntax.asc = uu___6;
                             FStarC_Syntax_Syntax.eff_opt = uu___7;_},
                           uu___8) -> check_relation1 g rel t02 t11
                        | (uu___6, FStarC_Syntax_Syntax.Tm_meta
                           { FStarC_Syntax_Syntax.tm2 = t12;
                             FStarC_Syntax_Syntax.meta =
                               FStarC_Syntax_Syntax.Meta_pattern uu___7;_})
                            -> check_relation1 g rel t01 t12
                        | (uu___6, FStarC_Syntax_Syntax.Tm_meta
                           { FStarC_Syntax_Syntax.tm2 = t12;
                             FStarC_Syntax_Syntax.meta =
                               FStarC_Syntax_Syntax.Meta_named uu___7;_})
                            -> check_relation1 g rel t01 t12
                        | (uu___6, FStarC_Syntax_Syntax.Tm_meta
                           { FStarC_Syntax_Syntax.tm2 = t12;
                             FStarC_Syntax_Syntax.meta =
                               FStarC_Syntax_Syntax.Meta_labeled uu___7;_})
                            -> check_relation1 g rel t01 t12
                        | (uu___6, FStarC_Syntax_Syntax.Tm_meta
                           { FStarC_Syntax_Syntax.tm2 = t12;
                             FStarC_Syntax_Syntax.meta =
                               FStarC_Syntax_Syntax.Meta_desugared uu___7;_})
                            -> check_relation1 g rel t01 t12
                        | (uu___6, FStarC_Syntax_Syntax.Tm_ascribed
                           { FStarC_Syntax_Syntax.tm = t12;
                             FStarC_Syntax_Syntax.asc = uu___7;
                             FStarC_Syntax_Syntax.eff_opt = uu___8;_})
                            -> check_relation1 g rel t01 t12
                        | (FStarC_Syntax_Syntax.Tm_uinst (f0, us0),
                           FStarC_Syntax_Syntax.Tm_uinst (f1, us1)) ->
                            let uu___6 = equal_term f0 f1 in
                            if uu___6
                            then
                              let uu___7 =
                                FStarC_TypeChecker_Rel.teq_nosmt_force
                                  g.tcenv t01 t11 in
                              (if uu___7
                               then
                                 fun uu___8 ->
                                   Success ((), FStar_Pervasives_Native.None)
                               else err ())
                            else maybe_unfold_and_retry t01 t11
                        | (FStarC_Syntax_Syntax.Tm_fvar uu___6,
                           FStarC_Syntax_Syntax.Tm_fvar uu___7) ->
                            maybe_unfold_and_retry t01 t11
                        | (FStarC_Syntax_Syntax.Tm_refine
                           { FStarC_Syntax_Syntax.b = x0;
                             FStarC_Syntax_Syntax.phi = f0;_},
                           FStarC_Syntax_Syntax.Tm_refine
                           { FStarC_Syntax_Syntax.b = x1;
                             FStarC_Syntax_Syntax.phi = f1;_})
                            ->
                            let uu___6 =
                              head_matches x0.FStarC_Syntax_Syntax.sort
                                x1.FStarC_Syntax_Syntax.sort in
                            if uu___6
                            then
                              let uu___7 =
                                check_relation1 g EQUALITY
                                  x0.FStarC_Syntax_Syntax.sort
                                  x1.FStarC_Syntax_Syntax.sort in
                              (fun ctx01 ->
                                 let uu___8 = uu___7 ctx01 in
                                 match uu___8 with
                                 | Success (x2, g11) ->
                                     let uu___9 =
                                       let uu___10 =
                                         let uu___11 =
                                           universe_of g
                                             x0.FStarC_Syntax_Syntax.sort in
                                         fun ctx02 ->
                                           let uu___12 = uu___11 ctx02 in
                                           match uu___12 with
                                           | Success (x3, g12) ->
                                               let uu___13 =
                                                 let uu___14 =
                                                   let uu___15 =
                                                     let uu___16 =
                                                       FStarC_Syntax_Syntax.mk_binder
                                                         x0 in
                                                     open_term g uu___16 f0 in
                                                   match uu___15 with
                                                   | (g2, b, f01) ->
                                                       let f11 =
                                                         FStarC_Syntax_Subst.subst
                                                           [FStarC_Syntax_Syntax.DB
                                                              (Prims.int_zero,
                                                                (b.FStarC_Syntax_Syntax.binder_bv))]
                                                           f1 in
                                                       (fun ctx03 ->
                                                          let uu___16 =
                                                            guard_not_allowed
                                                              ctx03 in
                                                          match uu___16 with
                                                          | Success (x4, g13)
                                                              ->
                                                              let uu___17 =
                                                                let uu___18 =
                                                                  if x4
                                                                  then
                                                                    let uu___19
                                                                    =
                                                                    check_relation1
                                                                    g2
                                                                    EQUALITY
                                                                    f01 f11 in
                                                                    with_binders
                                                                    [b] 
                                                                    [x3]
                                                                    uu___19
                                                                  else
                                                                    (
                                                                    match rel
                                                                    with
                                                                    | 
                                                                    EQUALITY
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    check_relation1
                                                                    g2
                                                                    EQUALITY
                                                                    f01 f11 in
                                                                    fun ctx
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    uu___21
                                                                    ctx in
                                                                    match uu___22
                                                                    with
                                                                    | 
                                                                    Error
                                                                    uu___23
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    FStarC_Syntax_Util.mk_iff
                                                                    f01 f11 in
                                                                    guard
                                                                    uu___25 in
                                                                    uu___24
                                                                    ctx
                                                                    | 
                                                                    res ->
                                                                    res in
                                                                    with_binders
                                                                    [b] 
                                                                    [x3]
                                                                    uu___20
                                                                    | 
                                                                    SUBTYPING
                                                                    (FStar_Pervasives_Native.Some
                                                                    tm) ->
                                                                    let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    FStarC_Syntax_Util.mk_imp
                                                                    f01 f11 in
                                                                    FStarC_Syntax_Subst.subst
                                                                    [
                                                                    FStarC_Syntax_Syntax.NT
                                                                    ((b.FStarC_Syntax_Syntax.binder_bv),
                                                                    tm)]
                                                                    uu___21 in
                                                                    guard
                                                                    uu___20
                                                                    | 
                                                                    SUBTYPING
                                                                    (FStar_Pervasives_Native.None)
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    FStarC_Syntax_Util.mk_imp
                                                                    f01 f11 in
                                                                    FStarC_Syntax_Util.mk_forall
                                                                    x3
                                                                    b.FStarC_Syntax_Syntax.binder_bv
                                                                    uu___21 in
                                                                    guard
                                                                    uu___20) in
                                                                uu___18 ctx03 in
                                                              (match uu___17
                                                               with
                                                               | Success
                                                                   (y, g21)
                                                                   ->
                                                                   let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    and_pre
                                                                    g13 g21 in
                                                                    ((),
                                                                    uu___19) in
                                                                   Success
                                                                    uu___18
                                                               | err1 -> err1)
                                                          | Error err1 ->
                                                              Error err1) in
                                                 uu___14 ctx02 in
                                               (match uu___13 with
                                                | Success (y, g2) ->
                                                    let uu___14 =
                                                      let uu___15 =
                                                        and_pre g12 g2 in
                                                      ((), uu___15) in
                                                    Success uu___14
                                                | err1 -> err1)
                                           | Error err1 -> Error err1 in
                                       uu___10 ctx01 in
                                     (match uu___9 with
                                      | Success (y, g2) ->
                                          let uu___10 =
                                            let uu___11 = and_pre g11 g2 in
                                            ((), uu___11) in
                                          Success uu___10
                                      | err1 -> err1)
                                 | Error err1 -> Error err1)
                            else
                              (let uu___8 =
                                 maybe_unfold x0.FStarC_Syntax_Syntax.sort
                                   x1.FStarC_Syntax_Syntax.sort in
                               fun ctx01 ->
                                 let uu___9 = uu___8 ctx01 in
                                 match uu___9 with
                                 | Success (x2, g11) ->
                                     let uu___10 =
                                       let uu___11 =
                                         match x2 with
                                         | FStar_Pervasives_Native.None ->
                                             ((let uu___13 =
                                                 FStarC_Compiler_Effect.op_Bang
                                                   dbg in
                                               if uu___13
                                               then
                                                 let uu___14 =
                                                   FStarC_Class_Show.show
                                                     FStarC_Syntax_Print.showable_term
                                                     x0.FStarC_Syntax_Syntax.sort in
                                                 let uu___15 =
                                                   FStarC_Class_Show.show
                                                     FStarC_Syntax_Print.showable_term
                                                     x1.FStarC_Syntax_Syntax.sort in
                                                 FStarC_Compiler_Util.print2
                                                   "Cannot match ref heads %s and %s\n"
                                                   uu___14 uu___15
                                               else ());
                                              fallback t01 t11)
                                         | FStar_Pervasives_Native.Some
                                             (t02, t12) ->
                                             let lhs =
                                               FStarC_Syntax_Syntax.mk
                                                 (FStarC_Syntax_Syntax.Tm_refine
                                                    {
                                                      FStarC_Syntax_Syntax.b
                                                        =
                                                        {
                                                          FStarC_Syntax_Syntax.ppname
                                                            =
                                                            (x0.FStarC_Syntax_Syntax.ppname);
                                                          FStarC_Syntax_Syntax.index
                                                            =
                                                            (x0.FStarC_Syntax_Syntax.index);
                                                          FStarC_Syntax_Syntax.sort
                                                            = t02
                                                        };
                                                      FStarC_Syntax_Syntax.phi
                                                        = f0
                                                    })
                                                 t02.FStarC_Syntax_Syntax.pos in
                                             let rhs =
                                               FStarC_Syntax_Syntax.mk
                                                 (FStarC_Syntax_Syntax.Tm_refine
                                                    {
                                                      FStarC_Syntax_Syntax.b
                                                        =
                                                        {
                                                          FStarC_Syntax_Syntax.ppname
                                                            =
                                                            (x1.FStarC_Syntax_Syntax.ppname);
                                                          FStarC_Syntax_Syntax.index
                                                            =
                                                            (x1.FStarC_Syntax_Syntax.index);
                                                          FStarC_Syntax_Syntax.sort
                                                            = t12
                                                        };
                                                      FStarC_Syntax_Syntax.phi
                                                        = f1
                                                    })
                                                 t12.FStarC_Syntax_Syntax.pos in
                                             let uu___12 =
                                               FStarC_Syntax_Util.flatten_refinement
                                                 lhs in
                                             let uu___13 =
                                               FStarC_Syntax_Util.flatten_refinement
                                                 rhs in
                                             check_relation1 g rel uu___12
                                               uu___13 in
                                       uu___11 ctx01 in
                                     (match uu___10 with
                                      | Success (y, g2) ->
                                          let uu___11 =
                                            let uu___12 = and_pre g11 g2 in
                                            ((), uu___12) in
                                          Success uu___11
                                      | err1 -> err1)
                                 | Error err1 -> Error err1)
                        | (FStarC_Syntax_Syntax.Tm_refine
                           { FStarC_Syntax_Syntax.b = x0;
                             FStarC_Syntax_Syntax.phi = f0;_},
                           uu___6) ->
                            let uu___7 =
                              head_matches x0.FStarC_Syntax_Syntax.sort t11 in
                            if uu___7
                            then
                              let uu___8 =
                                if rel = EQUALITY
                                then
                                  let uu___9 =
                                    universe_of g
                                      x0.FStarC_Syntax_Syntax.sort in
                                  fun ctx01 ->
                                    let uu___10 = uu___9 ctx01 in
                                    match uu___10 with
                                    | Success (x1, g11) ->
                                        let uu___11 =
                                          let uu___12 =
                                            let uu___13 =
                                              let uu___14 =
                                                FStarC_Syntax_Syntax.mk_binder
                                                  x0 in
                                              open_term g uu___14 f0 in
                                            match uu___13 with
                                            | (g2, b0, f01) ->
                                                (fun ctx02 ->
                                                   let uu___14 =
                                                     guard_not_allowed ctx02 in
                                                   match uu___14 with
                                                   | Success (x2, g12) ->
                                                       let uu___15 =
                                                         let uu___16 =
                                                           if x2
                                                           then
                                                             let uu___17 =
                                                               check_relation1
                                                                 g2 EQUALITY
                                                                 FStarC_Syntax_Util.t_true
                                                                 f01 in
                                                             with_binders
                                                               [b0] [x1]
                                                               uu___17
                                                           else
                                                             (let uu___18 =
                                                                let uu___19 =
                                                                  check_relation1
                                                                    g2
                                                                    EQUALITY
                                                                    FStarC_Syntax_Util.t_true
                                                                    f01 in
                                                                fun ctx ->
                                                                  let uu___20
                                                                    =
                                                                    uu___19
                                                                    ctx in
                                                                  match uu___20
                                                                  with
                                                                  | Error
                                                                    uu___21
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    guard f01 in
                                                                    uu___22
                                                                    ctx
                                                                  | res ->
                                                                    res in
                                                              with_binders
                                                                [b0] 
                                                                [x1] uu___18) in
                                                         uu___16 ctx02 in
                                                       (match uu___15 with
                                                        | Success (y, g21) ->
                                                            let uu___16 =
                                                              let uu___17 =
                                                                and_pre g12
                                                                  g21 in
                                                              ((), uu___17) in
                                                            Success uu___16
                                                        | err1 -> err1)
                                                   | Error err1 -> Error err1) in
                                          uu___12 ctx01 in
                                        (match uu___11 with
                                         | Success (y, g2) ->
                                             let uu___12 =
                                               let uu___13 = and_pre g11 g2 in
                                               ((), uu___13) in
                                             Success uu___12
                                         | err1 -> err1)
                                    | Error err1 -> Error err1
                                else
                                  (fun uu___10 ->
                                     Success
                                       ((), FStar_Pervasives_Native.None)) in
                              (fun ctx01 ->
                                 let uu___9 = uu___8 ctx01 in
                                 match uu___9 with
                                 | Success (x1, g11) ->
                                     let uu___10 =
                                       let uu___11 =
                                         check_relation1 g rel
                                           x0.FStarC_Syntax_Syntax.sort t11 in
                                       uu___11 ctx01 in
                                     (match uu___10 with
                                      | Success (y, g2) ->
                                          let uu___11 =
                                            let uu___12 = and_pre g11 g2 in
                                            ((), uu___12) in
                                          Success uu___11
                                      | err1 -> err1)
                                 | Error err1 -> Error err1)
                            else
                              (let uu___9 =
                                 maybe_unfold x0.FStarC_Syntax_Syntax.sort
                                   t11 in
                               fun ctx01 ->
                                 let uu___10 = uu___9 ctx01 in
                                 match uu___10 with
                                 | Success (x1, g11) ->
                                     let uu___11 =
                                       let uu___12 =
                                         match x1 with
                                         | FStar_Pervasives_Native.None ->
                                             fallback t01 t11
                                         | FStar_Pervasives_Native.Some
                                             (t02, t12) ->
                                             let lhs =
                                               FStarC_Syntax_Syntax.mk
                                                 (FStarC_Syntax_Syntax.Tm_refine
                                                    {
                                                      FStarC_Syntax_Syntax.b
                                                        =
                                                        {
                                                          FStarC_Syntax_Syntax.ppname
                                                            =
                                                            (x0.FStarC_Syntax_Syntax.ppname);
                                                          FStarC_Syntax_Syntax.index
                                                            =
                                                            (x0.FStarC_Syntax_Syntax.index);
                                                          FStarC_Syntax_Syntax.sort
                                                            = t02
                                                        };
                                                      FStarC_Syntax_Syntax.phi
                                                        = f0
                                                    })
                                                 t02.FStarC_Syntax_Syntax.pos in
                                             let uu___13 =
                                               FStarC_Syntax_Util.flatten_refinement
                                                 lhs in
                                             check_relation1 g rel uu___13
                                               t12 in
                                       uu___12 ctx01 in
                                     (match uu___11 with
                                      | Success (y, g2) ->
                                          let uu___12 =
                                            let uu___13 = and_pre g11 g2 in
                                            ((), uu___13) in
                                          Success uu___12
                                      | err1 -> err1)
                                 | Error err1 -> Error err1)
                        | (uu___6, FStarC_Syntax_Syntax.Tm_refine
                           { FStarC_Syntax_Syntax.b = x1;
                             FStarC_Syntax_Syntax.phi = f1;_})
                            ->
                            let uu___7 =
                              head_matches t01 x1.FStarC_Syntax_Syntax.sort in
                            if uu___7
                            then
                              let uu___8 =
                                universe_of g x1.FStarC_Syntax_Syntax.sort in
                              (fun ctx01 ->
                                 let uu___9 = uu___8 ctx01 in
                                 match uu___9 with
                                 | Success (x2, g11) ->
                                     let uu___10 =
                                       let uu___11 =
                                         let uu___12 =
                                           check_relation1 g EQUALITY t01
                                             x1.FStarC_Syntax_Syntax.sort in
                                         fun ctx02 ->
                                           let uu___13 = uu___12 ctx02 in
                                           match uu___13 with
                                           | Success (x3, g12) ->
                                               let uu___14 =
                                                 let uu___15 =
                                                   let uu___16 =
                                                     let uu___17 =
                                                       FStarC_Syntax_Syntax.mk_binder
                                                         x1 in
                                                     open_term g uu___17 f1 in
                                                   match uu___16 with
                                                   | (g2, b1, f11) ->
                                                       (fun ctx03 ->
                                                          let uu___17 =
                                                            guard_not_allowed
                                                              ctx03 in
                                                          match uu___17 with
                                                          | Success (x4, g13)
                                                              ->
                                                              let uu___18 =
                                                                let uu___19 =
                                                                  if x4
                                                                  then
                                                                    let uu___20
                                                                    =
                                                                    check_relation1
                                                                    g2
                                                                    EQUALITY
                                                                    FStarC_Syntax_Util.t_true
                                                                    f11 in
                                                                    with_binders
                                                                    [b1] 
                                                                    [x2]
                                                                    uu___20
                                                                  else
                                                                    (
                                                                    match rel
                                                                    with
                                                                    | 
                                                                    EQUALITY
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    check_relation1
                                                                    g2
                                                                    EQUALITY
                                                                    FStarC_Syntax_Util.t_true
                                                                    f11 in
                                                                    fun ctx
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    uu___22
                                                                    ctx in
                                                                    match uu___23
                                                                    with
                                                                    | 
                                                                    Error
                                                                    uu___24
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    guard f11 in
                                                                    uu___25
                                                                    ctx
                                                                    | 
                                                                    res ->
                                                                    res in
                                                                    with_binders
                                                                    [b1] 
                                                                    [x2]
                                                                    uu___21
                                                                    | 
                                                                    SUBTYPING
                                                                    (FStar_Pervasives_Native.Some
                                                                    tm) ->
                                                                    let uu___21
                                                                    =
                                                                    FStarC_Syntax_Subst.subst
                                                                    [
                                                                    FStarC_Syntax_Syntax.NT
                                                                    ((b1.FStarC_Syntax_Syntax.binder_bv),
                                                                    tm)] f11 in
                                                                    guard
                                                                    uu___21
                                                                    | 
                                                                    SUBTYPING
                                                                    (FStar_Pervasives_Native.None)
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    FStarC_Syntax_Util.mk_forall
                                                                    x2
                                                                    b1.FStarC_Syntax_Syntax.binder_bv
                                                                    f11 in
                                                                    guard
                                                                    uu___21) in
                                                                uu___19 ctx03 in
                                                              (match uu___18
                                                               with
                                                               | Success
                                                                   (y, g21)
                                                                   ->
                                                                   let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    and_pre
                                                                    g13 g21 in
                                                                    ((),
                                                                    uu___20) in
                                                                   Success
                                                                    uu___19
                                                               | err1 -> err1)
                                                          | Error err1 ->
                                                              Error err1) in
                                                 uu___15 ctx02 in
                                               (match uu___14 with
                                                | Success (y, g2) ->
                                                    let uu___15 =
                                                      let uu___16 =
                                                        and_pre g12 g2 in
                                                      ((), uu___16) in
                                                    Success uu___15
                                                | err1 -> err1)
                                           | Error err1 -> Error err1 in
                                       uu___11 ctx01 in
                                     (match uu___10 with
                                      | Success (y, g2) ->
                                          let uu___11 =
                                            let uu___12 = and_pre g11 g2 in
                                            ((), uu___12) in
                                          Success uu___11
                                      | err1 -> err1)
                                 | Error err1 -> Error err1)
                            else
                              (let uu___9 =
                                 maybe_unfold t01
                                   x1.FStarC_Syntax_Syntax.sort in
                               fun ctx01 ->
                                 let uu___10 = uu___9 ctx01 in
                                 match uu___10 with
                                 | Success (x2, g11) ->
                                     let uu___11 =
                                       let uu___12 =
                                         match x2 with
                                         | FStar_Pervasives_Native.None ->
                                             fallback t01 t11
                                         | FStar_Pervasives_Native.Some
                                             (t02, t12) ->
                                             let rhs =
                                               FStarC_Syntax_Syntax.mk
                                                 (FStarC_Syntax_Syntax.Tm_refine
                                                    {
                                                      FStarC_Syntax_Syntax.b
                                                        =
                                                        {
                                                          FStarC_Syntax_Syntax.ppname
                                                            =
                                                            (x1.FStarC_Syntax_Syntax.ppname);
                                                          FStarC_Syntax_Syntax.index
                                                            =
                                                            (x1.FStarC_Syntax_Syntax.index);
                                                          FStarC_Syntax_Syntax.sort
                                                            = t12
                                                        };
                                                      FStarC_Syntax_Syntax.phi
                                                        = f1
                                                    })
                                                 t12.FStarC_Syntax_Syntax.pos in
                                             let uu___13 =
                                               FStarC_Syntax_Util.flatten_refinement
                                                 rhs in
                                             check_relation1 g rel t02
                                               uu___13 in
                                       uu___12 ctx01 in
                                     (match uu___11 with
                                      | Success (y, g2) ->
                                          let uu___12 =
                                            let uu___13 = and_pre g11 g2 in
                                            ((), uu___13) in
                                          Success uu___12
                                      | err1 -> err1)
                                 | Error err1 -> Error err1)
                        | (FStarC_Syntax_Syntax.Tm_uinst uu___6, uu___7) ->
                            let head_matches1 = head_matches t01 t11 in
                            let uu___8 =
                              FStarC_Syntax_Util.leftmost_head_and_args t01 in
                            (match uu___8 with
                             | (head0, args0) ->
                                 let uu___9 =
                                   FStarC_Syntax_Util.leftmost_head_and_args
                                     t11 in
                                 (match uu___9 with
                                  | (head1, args1) ->
                                      if
                                        Prims.op_Negation
                                          (head_matches1 &&
                                             ((FStarC_Compiler_List.length
                                                 args0)
                                                =
                                                (FStarC_Compiler_List.length
                                                   args1)))
                                      then maybe_unfold_and_retry t01 t11
                                      else
                                        (let compare_head_and_args uu___11 =
                                           let uu___12 =
                                             let uu___13 =
                                               check_relation1 g EQUALITY
                                                 head0 head1 in
                                             fun ctx01 ->
                                               let uu___14 = uu___13 ctx01 in
                                               match uu___14 with
                                               | Success (x1, g11) ->
                                                   let uu___15 =
                                                     let uu___16 =
                                                       check_relation_args g
                                                         EQUALITY args0 args1 in
                                                     uu___16 ctx01 in
                                                   (match uu___15 with
                                                    | Success (y, g2) ->
                                                        let uu___16 =
                                                          let uu___17 =
                                                            and_pre g11 g2 in
                                                          ((), uu___17) in
                                                        Success uu___16
                                                    | err1 -> err1)
                                               | Error err1 -> Error err1 in
                                           fun ctx ->
                                             let uu___13 = uu___12 ctx in
                                             match uu___13 with
                                             | Error uu___14 ->
                                                 let uu___15 =
                                                   maybe_unfold_side_and_retry
                                                     Both t01 t11 in
                                                 uu___15 ctx
                                             | res -> res in
                                         let uu___11 =
                                           (guard_ok && (rel = EQUALITY)) &&
                                             ((equatable g t01) ||
                                                (equatable g t11)) in
                                         if uu___11
                                         then
                                           let uu___12 =
                                             let uu___13 =
                                               compare_head_and_args () in
                                             no_guard uu___13 in
                                           fun ctx ->
                                             let uu___13 = uu___12 ctx in
                                             match uu___13 with
                                             | Error uu___14 ->
                                                 let uu___15 =
                                                   emit_guard t01 t11 in
                                                 uu___15 ctx
                                             | res -> res
                                         else compare_head_and_args ())))
                        | (FStarC_Syntax_Syntax.Tm_fvar uu___6, uu___7) ->
                            let head_matches1 = head_matches t01 t11 in
                            let uu___8 =
                              FStarC_Syntax_Util.leftmost_head_and_args t01 in
                            (match uu___8 with
                             | (head0, args0) ->
                                 let uu___9 =
                                   FStarC_Syntax_Util.leftmost_head_and_args
                                     t11 in
                                 (match uu___9 with
                                  | (head1, args1) ->
                                      if
                                        Prims.op_Negation
                                          (head_matches1 &&
                                             ((FStarC_Compiler_List.length
                                                 args0)
                                                =
                                                (FStarC_Compiler_List.length
                                                   args1)))
                                      then maybe_unfold_and_retry t01 t11
                                      else
                                        (let compare_head_and_args uu___11 =
                                           let uu___12 =
                                             let uu___13 =
                                               check_relation1 g EQUALITY
                                                 head0 head1 in
                                             fun ctx01 ->
                                               let uu___14 = uu___13 ctx01 in
                                               match uu___14 with
                                               | Success (x1, g11) ->
                                                   let uu___15 =
                                                     let uu___16 =
                                                       check_relation_args g
                                                         EQUALITY args0 args1 in
                                                     uu___16 ctx01 in
                                                   (match uu___15 with
                                                    | Success (y, g2) ->
                                                        let uu___16 =
                                                          let uu___17 =
                                                            and_pre g11 g2 in
                                                          ((), uu___17) in
                                                        Success uu___16
                                                    | err1 -> err1)
                                               | Error err1 -> Error err1 in
                                           fun ctx ->
                                             let uu___13 = uu___12 ctx in
                                             match uu___13 with
                                             | Error uu___14 ->
                                                 let uu___15 =
                                                   maybe_unfold_side_and_retry
                                                     Both t01 t11 in
                                                 uu___15 ctx
                                             | res -> res in
                                         let uu___11 =
                                           (guard_ok && (rel = EQUALITY)) &&
                                             ((equatable g t01) ||
                                                (equatable g t11)) in
                                         if uu___11
                                         then
                                           let uu___12 =
                                             let uu___13 =
                                               compare_head_and_args () in
                                             no_guard uu___13 in
                                           fun ctx ->
                                             let uu___13 = uu___12 ctx in
                                             match uu___13 with
                                             | Error uu___14 ->
                                                 let uu___15 =
                                                   emit_guard t01 t11 in
                                                 uu___15 ctx
                                             | res -> res
                                         else compare_head_and_args ())))
                        | (FStarC_Syntax_Syntax.Tm_app uu___6, uu___7) ->
                            let head_matches1 = head_matches t01 t11 in
                            let uu___8 =
                              FStarC_Syntax_Util.leftmost_head_and_args t01 in
                            (match uu___8 with
                             | (head0, args0) ->
                                 let uu___9 =
                                   FStarC_Syntax_Util.leftmost_head_and_args
                                     t11 in
                                 (match uu___9 with
                                  | (head1, args1) ->
                                      if
                                        Prims.op_Negation
                                          (head_matches1 &&
                                             ((FStarC_Compiler_List.length
                                                 args0)
                                                =
                                                (FStarC_Compiler_List.length
                                                   args1)))
                                      then maybe_unfold_and_retry t01 t11
                                      else
                                        (let compare_head_and_args uu___11 =
                                           let uu___12 =
                                             let uu___13 =
                                               check_relation1 g EQUALITY
                                                 head0 head1 in
                                             fun ctx01 ->
                                               let uu___14 = uu___13 ctx01 in
                                               match uu___14 with
                                               | Success (x1, g11) ->
                                                   let uu___15 =
                                                     let uu___16 =
                                                       check_relation_args g
                                                         EQUALITY args0 args1 in
                                                     uu___16 ctx01 in
                                                   (match uu___15 with
                                                    | Success (y, g2) ->
                                                        let uu___16 =
                                                          let uu___17 =
                                                            and_pre g11 g2 in
                                                          ((), uu___17) in
                                                        Success uu___16
                                                    | err1 -> err1)
                                               | Error err1 -> Error err1 in
                                           fun ctx ->
                                             let uu___13 = uu___12 ctx in
                                             match uu___13 with
                                             | Error uu___14 ->
                                                 let uu___15 =
                                                   maybe_unfold_side_and_retry
                                                     Both t01 t11 in
                                                 uu___15 ctx
                                             | res -> res in
                                         let uu___11 =
                                           (guard_ok && (rel = EQUALITY)) &&
                                             ((equatable g t01) ||
                                                (equatable g t11)) in
                                         if uu___11
                                         then
                                           let uu___12 =
                                             let uu___13 =
                                               compare_head_and_args () in
                                             no_guard uu___13 in
                                           fun ctx ->
                                             let uu___13 = uu___12 ctx in
                                             match uu___13 with
                                             | Error uu___14 ->
                                                 let uu___15 =
                                                   emit_guard t01 t11 in
                                                 uu___15 ctx
                                             | res -> res
                                         else compare_head_and_args ())))
                        | (uu___6, FStarC_Syntax_Syntax.Tm_uinst uu___7) ->
                            let head_matches1 = head_matches t01 t11 in
                            let uu___8 =
                              FStarC_Syntax_Util.leftmost_head_and_args t01 in
                            (match uu___8 with
                             | (head0, args0) ->
                                 let uu___9 =
                                   FStarC_Syntax_Util.leftmost_head_and_args
                                     t11 in
                                 (match uu___9 with
                                  | (head1, args1) ->
                                      if
                                        Prims.op_Negation
                                          (head_matches1 &&
                                             ((FStarC_Compiler_List.length
                                                 args0)
                                                =
                                                (FStarC_Compiler_List.length
                                                   args1)))
                                      then maybe_unfold_and_retry t01 t11
                                      else
                                        (let compare_head_and_args uu___11 =
                                           let uu___12 =
                                             let uu___13 =
                                               check_relation1 g EQUALITY
                                                 head0 head1 in
                                             fun ctx01 ->
                                               let uu___14 = uu___13 ctx01 in
                                               match uu___14 with
                                               | Success (x1, g11) ->
                                                   let uu___15 =
                                                     let uu___16 =
                                                       check_relation_args g
                                                         EQUALITY args0 args1 in
                                                     uu___16 ctx01 in
                                                   (match uu___15 with
                                                    | Success (y, g2) ->
                                                        let uu___16 =
                                                          let uu___17 =
                                                            and_pre g11 g2 in
                                                          ((), uu___17) in
                                                        Success uu___16
                                                    | err1 -> err1)
                                               | Error err1 -> Error err1 in
                                           fun ctx ->
                                             let uu___13 = uu___12 ctx in
                                             match uu___13 with
                                             | Error uu___14 ->
                                                 let uu___15 =
                                                   maybe_unfold_side_and_retry
                                                     Both t01 t11 in
                                                 uu___15 ctx
                                             | res -> res in
                                         let uu___11 =
                                           (guard_ok && (rel = EQUALITY)) &&
                                             ((equatable g t01) ||
                                                (equatable g t11)) in
                                         if uu___11
                                         then
                                           let uu___12 =
                                             let uu___13 =
                                               compare_head_and_args () in
                                             no_guard uu___13 in
                                           fun ctx ->
                                             let uu___13 = uu___12 ctx in
                                             match uu___13 with
                                             | Error uu___14 ->
                                                 let uu___15 =
                                                   emit_guard t01 t11 in
                                                 uu___15 ctx
                                             | res -> res
                                         else compare_head_and_args ())))
                        | (uu___6, FStarC_Syntax_Syntax.Tm_fvar uu___7) ->
                            let head_matches1 = head_matches t01 t11 in
                            let uu___8 =
                              FStarC_Syntax_Util.leftmost_head_and_args t01 in
                            (match uu___8 with
                             | (head0, args0) ->
                                 let uu___9 =
                                   FStarC_Syntax_Util.leftmost_head_and_args
                                     t11 in
                                 (match uu___9 with
                                  | (head1, args1) ->
                                      if
                                        Prims.op_Negation
                                          (head_matches1 &&
                                             ((FStarC_Compiler_List.length
                                                 args0)
                                                =
                                                (FStarC_Compiler_List.length
                                                   args1)))
                                      then maybe_unfold_and_retry t01 t11
                                      else
                                        (let compare_head_and_args uu___11 =
                                           let uu___12 =
                                             let uu___13 =
                                               check_relation1 g EQUALITY
                                                 head0 head1 in
                                             fun ctx01 ->
                                               let uu___14 = uu___13 ctx01 in
                                               match uu___14 with
                                               | Success (x1, g11) ->
                                                   let uu___15 =
                                                     let uu___16 =
                                                       check_relation_args g
                                                         EQUALITY args0 args1 in
                                                     uu___16 ctx01 in
                                                   (match uu___15 with
                                                    | Success (y, g2) ->
                                                        let uu___16 =
                                                          let uu___17 =
                                                            and_pre g11 g2 in
                                                          ((), uu___17) in
                                                        Success uu___16
                                                    | err1 -> err1)
                                               | Error err1 -> Error err1 in
                                           fun ctx ->
                                             let uu___13 = uu___12 ctx in
                                             match uu___13 with
                                             | Error uu___14 ->
                                                 let uu___15 =
                                                   maybe_unfold_side_and_retry
                                                     Both t01 t11 in
                                                 uu___15 ctx
                                             | res -> res in
                                         let uu___11 =
                                           (guard_ok && (rel = EQUALITY)) &&
                                             ((equatable g t01) ||
                                                (equatable g t11)) in
                                         if uu___11
                                         then
                                           let uu___12 =
                                             let uu___13 =
                                               compare_head_and_args () in
                                             no_guard uu___13 in
                                           fun ctx ->
                                             let uu___13 = uu___12 ctx in
                                             match uu___13 with
                                             | Error uu___14 ->
                                                 let uu___15 =
                                                   emit_guard t01 t11 in
                                                 uu___15 ctx
                                             | res -> res
                                         else compare_head_and_args ())))
                        | (uu___6, FStarC_Syntax_Syntax.Tm_app uu___7) ->
                            let head_matches1 = head_matches t01 t11 in
                            let uu___8 =
                              FStarC_Syntax_Util.leftmost_head_and_args t01 in
                            (match uu___8 with
                             | (head0, args0) ->
                                 let uu___9 =
                                   FStarC_Syntax_Util.leftmost_head_and_args
                                     t11 in
                                 (match uu___9 with
                                  | (head1, args1) ->
                                      if
                                        Prims.op_Negation
                                          (head_matches1 &&
                                             ((FStarC_Compiler_List.length
                                                 args0)
                                                =
                                                (FStarC_Compiler_List.length
                                                   args1)))
                                      then maybe_unfold_and_retry t01 t11
                                      else
                                        (let compare_head_and_args uu___11 =
                                           let uu___12 =
                                             let uu___13 =
                                               check_relation1 g EQUALITY
                                                 head0 head1 in
                                             fun ctx01 ->
                                               let uu___14 = uu___13 ctx01 in
                                               match uu___14 with
                                               | Success (x1, g11) ->
                                                   let uu___15 =
                                                     let uu___16 =
                                                       check_relation_args g
                                                         EQUALITY args0 args1 in
                                                     uu___16 ctx01 in
                                                   (match uu___15 with
                                                    | Success (y, g2) ->
                                                        let uu___16 =
                                                          let uu___17 =
                                                            and_pre g11 g2 in
                                                          ((), uu___17) in
                                                        Success uu___16
                                                    | err1 -> err1)
                                               | Error err1 -> Error err1 in
                                           fun ctx ->
                                             let uu___13 = uu___12 ctx in
                                             match uu___13 with
                                             | Error uu___14 ->
                                                 let uu___15 =
                                                   maybe_unfold_side_and_retry
                                                     Both t01 t11 in
                                                 uu___15 ctx
                                             | res -> res in
                                         let uu___11 =
                                           (guard_ok && (rel = EQUALITY)) &&
                                             ((equatable g t01) ||
                                                (equatable g t11)) in
                                         if uu___11
                                         then
                                           let uu___12 =
                                             let uu___13 =
                                               compare_head_and_args () in
                                             no_guard uu___13 in
                                           fun ctx ->
                                             let uu___13 = uu___12 ctx in
                                             match uu___13 with
                                             | Error uu___14 ->
                                                 let uu___15 =
                                                   emit_guard t01 t11 in
                                                 uu___15 ctx
                                             | res -> res
                                         else compare_head_and_args ())))
                        | (FStarC_Syntax_Syntax.Tm_abs
                           { FStarC_Syntax_Syntax.bs = b0::b1::bs;
                             FStarC_Syntax_Syntax.body = body;
                             FStarC_Syntax_Syntax.rc_opt = ropt;_},
                           uu___6) ->
                            let t02 = curry_abs b0 b1 bs body ropt in
                            check_relation1 g rel t02 t11
                        | (uu___6, FStarC_Syntax_Syntax.Tm_abs
                           { FStarC_Syntax_Syntax.bs = b0::b1::bs;
                             FStarC_Syntax_Syntax.body = body;
                             FStarC_Syntax_Syntax.rc_opt = ropt;_})
                            ->
                            let t12 = curry_abs b0 b1 bs body ropt in
                            check_relation1 g rel t01 t12
                        | (FStarC_Syntax_Syntax.Tm_abs
                           { FStarC_Syntax_Syntax.bs = b0::[];
                             FStarC_Syntax_Syntax.body = body0;
                             FStarC_Syntax_Syntax.rc_opt = uu___6;_},
                           FStarC_Syntax_Syntax.Tm_abs
                           { FStarC_Syntax_Syntax.bs = b1::[];
                             FStarC_Syntax_Syntax.body = body1;
                             FStarC_Syntax_Syntax.rc_opt = uu___7;_})
                            ->
                            let uu___8 =
                              check_relation1 g EQUALITY
                                (b0.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort
                                (b1.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                            (fun ctx01 ->
                               let uu___9 = uu___8 ctx01 in
                               match uu___9 with
                               | Success (x1, g11) ->
                                   let uu___10 =
                                     let uu___11 =
                                       let uu___12 =
                                         check_bqual
                                           b0.FStarC_Syntax_Syntax.binder_qual
                                           b1.FStarC_Syntax_Syntax.binder_qual in
                                       fun ctx02 ->
                                         let uu___13 = uu___12 ctx02 in
                                         match uu___13 with
                                         | Success (x2, g12) ->
                                             let uu___14 =
                                               let uu___15 =
                                                 let uu___16 =
                                                   check_positivity_qual
                                                     EQUALITY
                                                     b0.FStarC_Syntax_Syntax.binder_positivity
                                                     b1.FStarC_Syntax_Syntax.binder_positivity in
                                                 fun ctx03 ->
                                                   let uu___17 =
                                                     uu___16 ctx03 in
                                                   match uu___17 with
                                                   | Success (x3, g13) ->
                                                       let uu___18 =
                                                         let uu___19 =
                                                           let uu___20 =
                                                             universe_of g
                                                               (b0.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                                                           fun ctx04 ->
                                                             let uu___21 =
                                                               uu___20 ctx04 in
                                                             match uu___21
                                                             with
                                                             | Success
                                                                 (x4, g14) ->
                                                                 let uu___22
                                                                   =
                                                                   let uu___23
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    open_term
                                                                    g b0
                                                                    body0 in
                                                                    match uu___24
                                                                    with
                                                                    | 
                                                                    (g2, b01,
                                                                    body01)
                                                                    ->
                                                                    let body11
                                                                    =
                                                                    FStarC_Syntax_Subst.subst
                                                                    [
                                                                    FStarC_Syntax_Syntax.DB
                                                                    (Prims.int_zero,
                                                                    (b01.FStarC_Syntax_Syntax.binder_bv))]
                                                                    body1 in
                                                                    let uu___25
                                                                    =
                                                                    check_relation1
                                                                    g2
                                                                    EQUALITY
                                                                    body01
                                                                    body11 in
                                                                    with_binders
                                                                    [b01]
                                                                    [x4]
                                                                    uu___25 in
                                                                   uu___23
                                                                    ctx04 in
                                                                 (match uu___22
                                                                  with
                                                                  | Success
                                                                    (y, g2)
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    and_pre
                                                                    g14 g2 in
                                                                    ((),
                                                                    uu___24) in
                                                                    Success
                                                                    uu___23
                                                                  | err1 ->
                                                                    err1)
                                                             | Error err1 ->
                                                                 Error err1 in
                                                         uu___19 ctx03 in
                                                       (match uu___18 with
                                                        | Success (y, g2) ->
                                                            let uu___19 =
                                                              let uu___20 =
                                                                and_pre g13
                                                                  g2 in
                                                              ((), uu___20) in
                                                            Success uu___19
                                                        | err1 -> err1)
                                                   | Error err1 -> Error err1 in
                                               uu___15 ctx02 in
                                             (match uu___14 with
                                              | Success (y, g2) ->
                                                  let uu___15 =
                                                    let uu___16 =
                                                      and_pre g12 g2 in
                                                    ((), uu___16) in
                                                  Success uu___15
                                              | err1 -> err1)
                                         | Error err1 -> Error err1 in
                                     uu___11 ctx01 in
                                   (match uu___10 with
                                    | Success (y, g2) ->
                                        let uu___11 =
                                          let uu___12 = and_pre g11 g2 in
                                          ((), uu___12) in
                                        Success uu___11
                                    | err1 -> err1)
                               | Error err1 -> Error err1)
                        | (FStarC_Syntax_Syntax.Tm_arrow
                           { FStarC_Syntax_Syntax.bs1 = x0::x1::xs;
                             FStarC_Syntax_Syntax.comp = c0;_},
                           uu___6) ->
                            let uu___7 = curry_arrow x0 (x1 :: xs) c0 in
                            check_relation1 g rel uu___7 t11
                        | (uu___6, FStarC_Syntax_Syntax.Tm_arrow
                           { FStarC_Syntax_Syntax.bs1 = x0::x1::xs;
                             FStarC_Syntax_Syntax.comp = c1;_})
                            ->
                            let uu___7 = curry_arrow x0 (x1 :: xs) c1 in
                            check_relation1 g rel t01 uu___7
                        | (FStarC_Syntax_Syntax.Tm_arrow
                           { FStarC_Syntax_Syntax.bs1 = x0::[];
                             FStarC_Syntax_Syntax.comp = c0;_},
                           FStarC_Syntax_Syntax.Tm_arrow
                           { FStarC_Syntax_Syntax.bs1 = x1::[];
                             FStarC_Syntax_Syntax.comp = c1;_})
                            ->
                            (fun ctx ->
                               let ctx1 =
                                 {
                                   no_guard = (ctx.no_guard);
                                   unfolding_ok = (ctx.unfolding_ok);
                                   error_context =
                                     (("subtype arrow",
                                        FStar_Pervasives_Native.None) ::
                                     (ctx.error_context))
                                 } in
                               let uu___6 =
                                 let uu___7 =
                                   check_bqual
                                     x0.FStarC_Syntax_Syntax.binder_qual
                                     x1.FStarC_Syntax_Syntax.binder_qual in
                                 fun ctx01 ->
                                   let uu___8 = uu___7 ctx01 in
                                   match uu___8 with
                                   | Success (x2, g11) ->
                                       let uu___9 =
                                         let uu___10 =
                                           let uu___11 =
                                             check_positivity_qual rel
                                               x0.FStarC_Syntax_Syntax.binder_positivity
                                               x1.FStarC_Syntax_Syntax.binder_positivity in
                                           fun ctx02 ->
                                             let uu___12 = uu___11 ctx02 in
                                             match uu___12 with
                                             | Success (x3, g12) ->
                                                 let uu___13 =
                                                   let uu___14 =
                                                     let uu___15 =
                                                       universe_of g
                                                         (x1.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                                                     fun ctx03 ->
                                                       let uu___16 =
                                                         uu___15 ctx03 in
                                                       match uu___16 with
                                                       | Success (x4, g13) ->
                                                           let uu___17 =
                                                             let uu___18 =
                                                               let uu___19 =
                                                                 open_comp g
                                                                   x1 c1 in
                                                               match uu___19
                                                               with
                                                               | (g_x1, x11,
                                                                  c11) ->
                                                                   let c01 =
                                                                    FStarC_Syntax_Subst.subst_comp
                                                                    [
                                                                    FStarC_Syntax_Syntax.DB
                                                                    (Prims.int_zero,
                                                                    (x11.FStarC_Syntax_Syntax.binder_bv))]
                                                                    c0 in
                                                                   let uu___20
                                                                    =
                                                                    let rel_arg
                                                                    =
                                                                    match rel
                                                                    with
                                                                    | 
                                                                    EQUALITY
                                                                    ->
                                                                    EQUALITY
                                                                    | 
                                                                    uu___21
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    x11.FStarC_Syntax_Syntax.binder_bv in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___23 in
                                                                    SUBTYPING
                                                                    uu___22 in
                                                                    let rel_comp
                                                                    =
                                                                    match rel
                                                                    with
                                                                    | 
                                                                    EQUALITY
                                                                    ->
                                                                    EQUALITY
                                                                    | 
                                                                    SUBTYPING
                                                                    e ->
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    FStarC_Syntax_Util.is_pure_or_ghost_comp
                                                                    c01 in
                                                                    if
                                                                    uu___22
                                                                    then
                                                                    op_let_Question
                                                                    e
                                                                    (fun e1
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    FStarC_Syntax_Util.args_of_binders
                                                                    [x11] in
                                                                    FStar_Pervasives_Native.snd
                                                                    uu___25 in
                                                                    FStarC_Syntax_Syntax.mk_Tm_app
                                                                    e1
                                                                    uu___24
                                                                    FStarC_Compiler_Range_Type.dummyRange in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___23)
                                                                    else
                                                                    FStar_Pervasives_Native.None in
                                                                    SUBTYPING
                                                                    uu___21 in
                                                                    let uu___21
                                                                    =
                                                                    check_relation1
                                                                    g rel
                                                                    (x11.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort
                                                                    (x0.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                                                                    fun ctx04
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    uu___21
                                                                    ctx04 in
                                                                    match uu___22
                                                                    with
                                                                    | 
                                                                    Success
                                                                    (x5, g14)
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    let uu___24
                                                                    ctx2 =
                                                                    let ctx3
                                                                    =
                                                                    {
                                                                    no_guard
                                                                    =
                                                                    (ctx2.no_guard);
                                                                    unfolding_ok
                                                                    =
                                                                    (ctx2.unfolding_ok);
                                                                    error_context
                                                                    =
                                                                    (("check_subcomp",
                                                                    FStar_Pervasives_Native.None)
                                                                    ::
                                                                    (ctx2.error_context))
                                                                    } in
                                                                    let uu___25
                                                                    =
                                                                    check_relation_comp
                                                                    g_x1
                                                                    rel_comp
                                                                    c01 c11 in
                                                                    uu___25
                                                                    ctx3 in
                                                                    uu___24
                                                                    ctx04 in
                                                                    (match uu___23
                                                                    with
                                                                    | 
                                                                    Success
                                                                    (y, g2)
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    and_pre
                                                                    g14 g2 in
                                                                    ((),
                                                                    uu___25) in
                                                                    Success
                                                                    uu___24
                                                                    | 
                                                                    err1 ->
                                                                    err1)
                                                                    | 
                                                                    Error
                                                                    err1 ->
                                                                    Error
                                                                    err1 in
                                                                   with_binders
                                                                    [x11]
                                                                    [x4]
                                                                    uu___20 in
                                                             uu___18 ctx03 in
                                                           (match uu___17
                                                            with
                                                            | Success 
                                                                (y, g2) ->
                                                                let uu___18 =
                                                                  let uu___19
                                                                    =
                                                                    and_pre
                                                                    g13 g2 in
                                                                  ((),
                                                                    uu___19) in
                                                                Success
                                                                  uu___18
                                                            | err1 -> err1)
                                                       | Error err1 ->
                                                           Error err1 in
                                                   uu___14 ctx02 in
                                                 (match uu___13 with
                                                  | Success (y, g2) ->
                                                      let uu___14 =
                                                        let uu___15 =
                                                          and_pre g12 g2 in
                                                        ((), uu___15) in
                                                      Success uu___14
                                                  | err1 -> err1)
                                             | Error err1 -> Error err1 in
                                         uu___10 ctx01 in
                                       (match uu___9 with
                                        | Success (y, g2) ->
                                            let uu___10 =
                                              let uu___11 = and_pre g11 g2 in
                                              ((), uu___11) in
                                            Success uu___10
                                        | err1 -> err1)
                                   | Error err1 -> Error err1 in
                               uu___6 ctx1)
                        | (FStarC_Syntax_Syntax.Tm_match
                           { FStarC_Syntax_Syntax.scrutinee = e0;
                             FStarC_Syntax_Syntax.ret_opt = uu___6;
                             FStarC_Syntax_Syntax.brs = brs0;
                             FStarC_Syntax_Syntax.rc_opt1 = uu___7;_},
                           FStarC_Syntax_Syntax.Tm_match
                           { FStarC_Syntax_Syntax.scrutinee = e1;
                             FStarC_Syntax_Syntax.ret_opt = uu___8;
                             FStarC_Syntax_Syntax.brs = brs1;
                             FStarC_Syntax_Syntax.rc_opt1 = uu___9;_})
                            ->
                            let relate_branch br0 br1 uu___10 =
                              match (br0, br1) with
                              | ((p0, FStar_Pervasives_Native.None, body0),
                                 (p1, FStar_Pervasives_Native.None, body1))
                                  ->
                                  let uu___11 =
                                    let uu___12 =
                                      FStarC_Syntax_Syntax.eq_pat p0 p1 in
                                    Prims.op_Negation uu___12 in
                                  if uu___11
                                  then fail "patterns not equal"
                                  else
                                    (let uu___13 =
                                       open_branches_eq_pat g
                                         (p0, FStar_Pervasives_Native.None,
                                           body0)
                                         (p1, FStar_Pervasives_Native.None,
                                           body1) in
                                     match uu___13 with
                                     | (g', (p01, uu___14, body01),
                                        (p11, uu___15, body11)) ->
                                         let uu___16 =
                                           FStarC_TypeChecker_PatternUtils.raw_pat_as_exp
                                             g.tcenv p01 in
                                         (match uu___16 with
                                          | FStar_Pervasives_Native.Some
                                              (uu___17, bvs0) ->
                                              let bs0 =
                                                FStarC_Compiler_List.map
                                                  FStarC_Syntax_Syntax.mk_binder
                                                  bvs0 in
                                              let uu___18 =
                                                check_binders g bs0 in
                                              (fun ctx01 ->
                                                 let uu___19 = uu___18 ctx01 in
                                                 match uu___19 with
                                                 | Success (x1, g11) ->
                                                     let uu___20 =
                                                       let uu___21 ctx =
                                                         let ctx1 =
                                                           {
                                                             no_guard =
                                                               (ctx.no_guard);
                                                             unfolding_ok =
                                                               (ctx.unfolding_ok);
                                                             error_context =
                                                               (("relate_branch",
                                                                  FStar_Pervasives_Native.None)
                                                               ::
                                                               (ctx.error_context))
                                                           } in
                                                         let uu___22 =
                                                           let uu___23 =
                                                             check_relation1
                                                               g' rel body01
                                                               body11 in
                                                           with_binders bs0
                                                             x1 uu___23 in
                                                         uu___22 ctx1 in
                                                       uu___21 ctx01 in
                                                     (match uu___20 with
                                                      | Success (y, g2) ->
                                                          let uu___21 =
                                                            let uu___22 =
                                                              and_pre g11 g2 in
                                                            ((), uu___22) in
                                                          Success uu___21
                                                      | err1 -> err1)
                                                 | Error err1 -> Error err1)
                                          | uu___17 ->
                                              fail
                                                "raw_pat_as_exp failed in check_equality match rule"))
                              | uu___11 ->
                                  fail
                                    "Core does not support branches with when" in
                            let uu___10 =
                              let uu___11 = check_relation1 g EQUALITY e0 e1 in
                              fun ctx01 ->
                                let uu___12 = uu___11 ctx01 in
                                match uu___12 with
                                | Success (x1, g11) ->
                                    let uu___13 =
                                      let uu___14 =
                                        iter2 brs0 brs1 relate_branch () in
                                      uu___14 ctx01 in
                                    (match uu___13 with
                                     | Success (y, g2) ->
                                         let uu___14 =
                                           let uu___15 = and_pre g11 g2 in
                                           ((), uu___15) in
                                         Success uu___14
                                     | err1 -> err1)
                                | Error err1 -> Error err1 in
                            (fun ctx ->
                               let uu___11 = uu___10 ctx in
                               match uu___11 with
                               | Error uu___12 ->
                                   let uu___13 = fallback t01 t11 in
                                   uu___13 ctx
                               | res -> res)
                        | uu___6 -> fallback t01 t11) in
                   uu___3 ctx0 in
                 (match uu___2 with
                  | Success (y, g2) ->
                      let uu___3 = let uu___4 = and_pre g1 g2 in ((), uu___4) in
                      Success uu___3
                  | err1 -> err1)
             | Error err1 -> Error err1)
and (check_relation_args :
  env ->
    relation ->
      FStarC_Syntax_Syntax.args -> FStarC_Syntax_Syntax.args -> unit result)
  =
  fun g ->
    fun rel ->
      fun a0 ->
        fun a1 ->
          if
            (FStarC_Compiler_List.length a0) =
              (FStarC_Compiler_List.length a1)
          then
            iter2 a0 a1
              (fun uu___ ->
                 fun uu___1 ->
                   fun uu___2 ->
                     match (uu___, uu___1) with
                     | ((t0, q0), (t1, q1)) ->
                         let uu___3 = check_aqual q0 q1 in
                         (fun ctx0 ->
                            let uu___4 = uu___3 ctx0 in
                            match uu___4 with
                            | Success (x, g1) ->
                                let uu___5 =
                                  let uu___6 = check_relation g rel t0 t1 in
                                  uu___6 ctx0 in
                                (match uu___5 with
                                 | Success (y, g2) ->
                                     let uu___6 =
                                       let uu___7 = and_pre g1 g2 in
                                       ((), uu___7) in
                                     Success uu___6
                                 | err -> err)
                            | Error err -> Error err)) ()
          else fail "Unequal number of arguments"
and (check_relation_comp :
  env ->
    relation ->
      FStarC_Syntax_Syntax.comp -> FStarC_Syntax_Syntax.comp -> unit result)
  =
  fun g ->
    fun rel ->
      fun c0 ->
        fun c1 ->
          let destruct_comp c =
            let uu___ = FStarC_Syntax_Util.is_total_comp c in
            if uu___
            then
              FStar_Pervasives_Native.Some
                (E_Total, (FStarC_Syntax_Util.comp_result c))
            else
              (let uu___2 = FStarC_Syntax_Util.is_tot_or_gtot_comp c in
               if uu___2
               then
                 FStar_Pervasives_Native.Some
                   (E_Ghost, (FStarC_Syntax_Util.comp_result c))
               else FStar_Pervasives_Native.None) in
          let uu___ =
            let uu___1 = destruct_comp c0 in
            let uu___2 = destruct_comp c1 in (uu___1, uu___2) in
          match uu___ with
          | (FStar_Pervasives_Native.None, uu___1) ->
              let uu___2 =
                let uu___3 =
                  FStarC_TypeChecker_TermEqAndSimplify.eq_comp g.tcenv c0 c1 in
                uu___3 = FStarC_TypeChecker_TermEqAndSimplify.Equal in
              if uu___2
              then (fun uu___3 -> Success ((), FStar_Pervasives_Native.None))
              else
                (let ct_eq res0 args0 res1 args1 =
                   let uu___4 = check_relation g EQUALITY res0 res1 in
                   fun ctx0 ->
                     let uu___5 = uu___4 ctx0 in
                     match uu___5 with
                     | Success (x, g1) ->
                         let uu___6 =
                           let uu___7 =
                             check_relation_args g EQUALITY args0 args1 in
                           uu___7 ctx0 in
                         (match uu___6 with
                          | Success (y, g2) ->
                              let uu___7 =
                                let uu___8 = and_pre g1 g2 in ((), uu___8) in
                              Success uu___7
                          | err -> err)
                     | Error err -> Error err in
                 let uu___4 =
                   FStarC_Syntax_Util.comp_eff_name_res_and_args c0 in
                 match uu___4 with
                 | (eff0, res0, args0) ->
                     let uu___5 =
                       FStarC_Syntax_Util.comp_eff_name_res_and_args c1 in
                     (match uu___5 with
                      | (eff1, res1, args1) ->
                          let uu___6 = FStarC_Ident.lid_equals eff0 eff1 in
                          if uu___6
                          then ct_eq res0 args0 res1 args1
                          else
                            (let ct0 =
                               FStarC_TypeChecker_Env.unfold_effect_abbrev
                                 g.tcenv c0 in
                             let ct1 =
                               FStarC_TypeChecker_Env.unfold_effect_abbrev
                                 g.tcenv c1 in
                             let uu___8 =
                               FStarC_Ident.lid_equals
                                 ct0.FStarC_Syntax_Syntax.effect_name
                                 ct1.FStarC_Syntax_Syntax.effect_name in
                             if uu___8
                             then
                               ct_eq ct0.FStarC_Syntax_Syntax.result_typ
                                 ct0.FStarC_Syntax_Syntax.effect_args
                                 ct1.FStarC_Syntax_Syntax.result_typ
                                 ct1.FStarC_Syntax_Syntax.effect_args
                             else
                               (let uu___10 =
                                  let uu___11 =
                                    FStarC_Ident.string_of_lid
                                      ct0.FStarC_Syntax_Syntax.effect_name in
                                  let uu___12 =
                                    FStarC_Ident.string_of_lid
                                      ct1.FStarC_Syntax_Syntax.effect_name in
                                  FStarC_Compiler_Util.format2
                                    "Subcomp failed: Unequal computation types %s and %s"
                                    uu___11 uu___12 in
                                fail uu___10))))
          | (uu___1, FStar_Pervasives_Native.None) ->
              let uu___2 =
                let uu___3 =
                  FStarC_TypeChecker_TermEqAndSimplify.eq_comp g.tcenv c0 c1 in
                uu___3 = FStarC_TypeChecker_TermEqAndSimplify.Equal in
              if uu___2
              then (fun uu___3 -> Success ((), FStar_Pervasives_Native.None))
              else
                (let ct_eq res0 args0 res1 args1 =
                   let uu___4 = check_relation g EQUALITY res0 res1 in
                   fun ctx0 ->
                     let uu___5 = uu___4 ctx0 in
                     match uu___5 with
                     | Success (x, g1) ->
                         let uu___6 =
                           let uu___7 =
                             check_relation_args g EQUALITY args0 args1 in
                           uu___7 ctx0 in
                         (match uu___6 with
                          | Success (y, g2) ->
                              let uu___7 =
                                let uu___8 = and_pre g1 g2 in ((), uu___8) in
                              Success uu___7
                          | err -> err)
                     | Error err -> Error err in
                 let uu___4 =
                   FStarC_Syntax_Util.comp_eff_name_res_and_args c0 in
                 match uu___4 with
                 | (eff0, res0, args0) ->
                     let uu___5 =
                       FStarC_Syntax_Util.comp_eff_name_res_and_args c1 in
                     (match uu___5 with
                      | (eff1, res1, args1) ->
                          let uu___6 = FStarC_Ident.lid_equals eff0 eff1 in
                          if uu___6
                          then ct_eq res0 args0 res1 args1
                          else
                            (let ct0 =
                               FStarC_TypeChecker_Env.unfold_effect_abbrev
                                 g.tcenv c0 in
                             let ct1 =
                               FStarC_TypeChecker_Env.unfold_effect_abbrev
                                 g.tcenv c1 in
                             let uu___8 =
                               FStarC_Ident.lid_equals
                                 ct0.FStarC_Syntax_Syntax.effect_name
                                 ct1.FStarC_Syntax_Syntax.effect_name in
                             if uu___8
                             then
                               ct_eq ct0.FStarC_Syntax_Syntax.result_typ
                                 ct0.FStarC_Syntax_Syntax.effect_args
                                 ct1.FStarC_Syntax_Syntax.result_typ
                                 ct1.FStarC_Syntax_Syntax.effect_args
                             else
                               (let uu___10 =
                                  let uu___11 =
                                    FStarC_Ident.string_of_lid
                                      ct0.FStarC_Syntax_Syntax.effect_name in
                                  let uu___12 =
                                    FStarC_Ident.string_of_lid
                                      ct1.FStarC_Syntax_Syntax.effect_name in
                                  FStarC_Compiler_Util.format2
                                    "Subcomp failed: Unequal computation types %s and %s"
                                    uu___11 uu___12 in
                                fail uu___10))))
          | (FStar_Pervasives_Native.Some (E_Total, t0),
             FStar_Pervasives_Native.Some (uu___1, t1)) ->
              check_relation g rel t0 t1
          | (FStar_Pervasives_Native.Some (E_Ghost, t0),
             FStar_Pervasives_Native.Some (E_Ghost, t1)) ->
              check_relation g rel t0 t1
          | (FStar_Pervasives_Native.Some (E_Ghost, t0),
             FStar_Pervasives_Native.Some (E_Total, t1)) ->
              let uu___1 = non_informative g t1 in
              if uu___1
              then check_relation g rel t0 t1
              else fail "Expected a Total computation, but got Ghost"
and (check_subtype :
  env ->
    FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStarC_Syntax_Syntax.typ ->
        FStarC_Syntax_Syntax.typ -> context -> unit success __result)
  =
  fun g ->
    fun e ->
      fun t0 ->
        fun t1 ->
          fun ctx ->
            FStarC_Profiling.profile
              (fun uu___ ->
                 let rel = SUBTYPING e in
                 let uu___1 ctx1 =
                   let ctx2 =
                     {
                       no_guard = (ctx1.no_guard);
                       unfolding_ok = (ctx1.unfolding_ok);
                       error_context =
                         (((if ctx.no_guard
                            then "check_subtype(no_guard)"
                            else "check_subtype"),
                            (FStar_Pervasives_Native.Some
                               (CtxRel (t0, rel, t1)))) ::
                         (ctx1.error_context))
                     } in
                   let uu___2 = check_relation g rel t0 t1 in uu___2 ctx2 in
                 uu___1 ctx) FStar_Pervasives_Native.None
              "FStarC.TypeChecker.Core.check_subtype"
and (memo_check :
  env ->
    FStarC_Syntax_Syntax.term ->
      (tot_or_ghost * FStarC_Syntax_Syntax.typ) result)
  =
  fun g ->
    fun e ->
      let check_then_memo g1 e1 ctx =
        let r = let uu___ = do_check_and_promote g1 e1 in uu___ ctx in
        match r with
        | Success (res, FStar_Pervasives_Native.None) ->
            (insert g1 e1 (res, FStar_Pervasives_Native.None); r)
        | Success (res, FStar_Pervasives_Native.Some guard1) ->
            (match g1.guard_handler with
             | FStar_Pervasives_Native.None ->
                 (insert g1 e1 (res, (FStar_Pervasives_Native.Some guard1));
                  r)
             | FStar_Pervasives_Native.Some gh ->
                 let uu___ = gh g1.tcenv guard1 in
                 if uu___
                 then
                   let r1 = (res, FStar_Pervasives_Native.None) in
                   (insert g1 e1 r1; Success r1)
                 else
                   (let uu___2 = fail "guard handler failed" in uu___2 ctx))
        | uu___ -> r in
      fun ctx ->
        if Prims.op_Negation g.should_read_cache
        then check_then_memo g e ctx
        else
          (let uu___1 = let uu___2 = lookup g e in uu___2 ctx in
           match uu___1 with
           | Error uu___2 -> check_then_memo g e ctx
           | Success (et, FStar_Pervasives_Native.None) ->
               Success (et, FStar_Pervasives_Native.None)
           | Success (et, FStar_Pervasives_Native.Some pre) ->
               (match g.guard_handler with
                | FStar_Pervasives_Native.None ->
                    Success (et, (FStar_Pervasives_Native.Some pre))
                | FStar_Pervasives_Native.Some uu___2 ->
                    check_then_memo
                      {
                        tcenv = (g.tcenv);
                        allow_universe_instantiation =
                          (g.allow_universe_instantiation);
                        max_binder_index = (g.max_binder_index);
                        guard_handler = (g.guard_handler);
                        should_read_cache = false
                      } e ctx))
and (check :
  Prims.string ->
    env ->
      FStarC_Syntax_Syntax.term ->
        (tot_or_ghost * FStarC_Syntax_Syntax.typ) result)
  =
  fun msg ->
    fun g ->
      fun e ->
        fun ctx ->
          let ctx1 =
            {
              no_guard = (ctx.no_guard);
              unfolding_ok = (ctx.unfolding_ok);
              error_context =
                ((msg, (FStar_Pervasives_Native.Some (CtxTerm e))) ::
                (ctx.error_context))
            } in
          let uu___ = memo_check g e in uu___ ctx1
and (do_check_and_promote :
  env ->
    FStarC_Syntax_Syntax.term ->
      (tot_or_ghost * FStarC_Syntax_Syntax.typ) result)
  =
  fun g ->
    fun e ->
      let uu___ = do_check g e in
      fun ctx0 ->
        let uu___1 = uu___ ctx0 in
        match uu___1 with
        | Success (x, g1) ->
            let uu___2 =
              let uu___3 =
                match x with
                | (eff, t) ->
                    let eff1 =
                      match eff with
                      | E_Total -> E_Total
                      | E_Ghost ->
                          let uu___4 = non_informative g t in
                          if uu___4 then E_Total else E_Ghost in
                    (fun uu___4 ->
                       Success ((eff1, t), FStar_Pervasives_Native.None)) in
              uu___3 ctx0 in
            (match uu___2 with
             | Success (y, g2) ->
                 let uu___3 = let uu___4 = and_pre g1 g2 in (y, uu___4) in
                 Success uu___3
             | err -> err)
        | Error err -> Error err
and (do_check :
  env ->
    FStarC_Syntax_Syntax.term ->
      (tot_or_ghost * FStarC_Syntax_Syntax.typ) result)
  =
  fun g ->
    fun e ->
      let e1 = FStarC_Syntax_Subst.compress e in
      match e1.FStarC_Syntax_Syntax.n with
      | FStarC_Syntax_Syntax.Tm_lazy
          { FStarC_Syntax_Syntax.blob = uu___;
            FStarC_Syntax_Syntax.lkind = FStarC_Syntax_Syntax.Lazy_embedding
              uu___1;
            FStarC_Syntax_Syntax.ltyp = uu___2;
            FStarC_Syntax_Syntax.rng = uu___3;_}
          -> let uu___4 = FStarC_Syntax_Util.unlazy e1 in do_check g uu___4
      | FStarC_Syntax_Syntax.Tm_lazy i ->
          (fun uu___ ->
             Success
               ((E_Total, (i.FStarC_Syntax_Syntax.ltyp)),
                 FStar_Pervasives_Native.None))
      | FStarC_Syntax_Syntax.Tm_meta
          { FStarC_Syntax_Syntax.tm2 = t;
            FStarC_Syntax_Syntax.meta = uu___;_}
          -> memo_check g t
      | FStarC_Syntax_Syntax.Tm_uvar (uv, s) ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStarC_Syntax_Util.ctx_uvar_typ uv in
              FStarC_Syntax_Subst.subst' s uu___2 in
            (E_Total, uu___1) in
          (fun uu___1 -> Success (uu___, FStar_Pervasives_Native.None))
      | FStarC_Syntax_Syntax.Tm_name x ->
          let uu___ = FStarC_TypeChecker_Env.try_lookup_bv g.tcenv x in
          (match uu___ with
           | FStar_Pervasives_Native.None ->
               let uu___1 =
                 let uu___2 =
                   FStarC_Class_Show.show FStarC_Syntax_Print.showable_bv x in
                 FStarC_Compiler_Util.format1 "Variable not found: %s" uu___2 in
               fail uu___1
           | FStar_Pervasives_Native.Some (t, uu___1) ->
               (fun uu___2 ->
                  Success ((E_Total, t), FStar_Pervasives_Native.None)))
      | FStarC_Syntax_Syntax.Tm_fvar f ->
          let uu___ =
            FStarC_TypeChecker_Env.try_lookup_lid g.tcenv
              (f.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v in
          (match uu___ with
           | FStar_Pervasives_Native.Some (([], t), uu___1) ->
               (fun uu___2 ->
                  Success ((E_Total, t), FStar_Pervasives_Native.None))
           | uu___1 -> fail "Missing universes instantiation")
      | FStarC_Syntax_Syntax.Tm_uinst
          ({ FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_fvar f;
             FStarC_Syntax_Syntax.pos = uu___;
             FStarC_Syntax_Syntax.vars = uu___1;
             FStarC_Syntax_Syntax.hash_code = uu___2;_},
           us)
          ->
          let uu___3 =
            FStarC_TypeChecker_Env.try_lookup_and_inst_lid g.tcenv us
              (f.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v in
          (match uu___3 with
           | FStar_Pervasives_Native.None ->
               let uu___4 =
                 let uu___5 =
                   FStarC_Ident.string_of_lid
                     (f.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v in
                 FStarC_Compiler_Util.format1 "Top-level name not found: %s"
                   uu___5 in
               fail uu___4
           | FStar_Pervasives_Native.Some (t, uu___4) ->
               (fun uu___5 ->
                  Success ((E_Total, t), FStar_Pervasives_Native.None)))
      | FStarC_Syntax_Syntax.Tm_constant c ->
          (match c with
           | FStarC_Const.Const_range_of -> fail "Unhandled constant"
           | FStarC_Const.Const_set_range_of -> fail "Unhandled constant"
           | FStarC_Const.Const_reify uu___ -> fail "Unhandled constant"
           | FStarC_Const.Const_reflect uu___ -> fail "Unhandled constant"
           | uu___ ->
               let t =
                 FStarC_TypeChecker_TcTerm.tc_constant g.tcenv
                   e1.FStarC_Syntax_Syntax.pos c in
               (fun uu___1 ->
                  Success ((E_Total, t), FStar_Pervasives_Native.None)))
      | FStarC_Syntax_Syntax.Tm_type u ->
          let uu___ =
            let uu___1 = mk_type (FStarC_Syntax_Syntax.U_succ u) in
            (E_Total, uu___1) in
          (fun uu___1 -> Success (uu___, FStar_Pervasives_Native.None))
      | FStarC_Syntax_Syntax.Tm_refine
          { FStarC_Syntax_Syntax.b = x; FStarC_Syntax_Syntax.phi = phi;_} ->
          let uu___ = check "refinement head" g x.FStarC_Syntax_Syntax.sort in
          (fun ctx0 ->
             let uu___1 = uu___ ctx0 in
             match uu___1 with
             | Success (x1, g1) ->
                 let uu___2 =
                   let uu___3 =
                     match x1 with
                     | (uu___4, t) ->
                         let uu___5 = is_type g t in
                         (fun ctx01 ->
                            let uu___6 = uu___5 ctx01 in
                            match uu___6 with
                            | Success (x2, g11) ->
                                let uu___7 =
                                  let uu___8 =
                                    let uu___9 =
                                      let uu___10 =
                                        FStarC_Syntax_Syntax.mk_binder x in
                                      open_term g uu___10 phi in
                                    match uu___9 with
                                    | (g', x3, phi1) ->
                                        let uu___10 =
                                          let uu___11 =
                                            check "refinement formula" g'
                                              phi1 in
                                          fun ctx02 ->
                                            let uu___12 = uu___11 ctx02 in
                                            match uu___12 with
                                            | Success (x4, g12) ->
                                                let uu___13 =
                                                  let uu___14 =
                                                    match x4 with
                                                    | (uu___15, t') ->
                                                        let uu___16 =
                                                          is_type g' t' in
                                                        (fun ctx03 ->
                                                           let uu___17 =
                                                             uu___16 ctx03 in
                                                           match uu___17 with
                                                           | Success
                                                               (x5, g13) ->
                                                               let uu___18 =
                                                                 let uu___19
                                                                   uu___20 =
                                                                   Success
                                                                    ((E_Total,
                                                                    t),
                                                                    FStar_Pervasives_Native.None) in
                                                                 uu___19
                                                                   ctx03 in
                                                               (match uu___18
                                                                with
                                                                | Success
                                                                    (y, g2)
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    and_pre
                                                                    g13 g2 in
                                                                    (y,
                                                                    uu___20) in
                                                                    Success
                                                                    uu___19
                                                                | err -> err)
                                                           | Error err ->
                                                               Error err) in
                                                  uu___14 ctx02 in
                                                (match uu___13 with
                                                 | Success (y, g2) ->
                                                     let uu___14 =
                                                       let uu___15 =
                                                         and_pre g12 g2 in
                                                       (y, uu___15) in
                                                     Success uu___14
                                                 | err -> err)
                                            | Error err -> Error err in
                                        with_binders [x3] [x2] uu___10 in
                                  uu___8 ctx01 in
                                (match uu___7 with
                                 | Success (y, g2) ->
                                     let uu___8 =
                                       let uu___9 = and_pre g11 g2 in
                                       (y, uu___9) in
                                     Success uu___8
                                 | err -> err)
                            | Error err -> Error err) in
                   uu___3 ctx0 in
                 (match uu___2 with
                  | Success (y, g2) ->
                      let uu___3 = let uu___4 = and_pre g1 g2 in (y, uu___4) in
                      Success uu___3
                  | err -> err)
             | Error err -> Error err)
      | FStarC_Syntax_Syntax.Tm_abs
          { FStarC_Syntax_Syntax.bs = xs; FStarC_Syntax_Syntax.body = body;
            FStarC_Syntax_Syntax.rc_opt = uu___;_}
          ->
          let uu___1 = open_term_binders g xs body in
          (match uu___1 with
           | (g', xs1, body1) ->
               let uu___2 ctx =
                 let ctx1 =
                   {
                     no_guard = (ctx.no_guard);
                     unfolding_ok = (ctx.unfolding_ok);
                     error_context =
                       (("abs binders", FStar_Pervasives_Native.None) ::
                       (ctx.error_context))
                   } in
                 let uu___3 = check_binders g xs1 in uu___3 ctx1 in
               (fun ctx0 ->
                  let uu___3 = uu___2 ctx0 in
                  match uu___3 with
                  | Success (x, g1) ->
                      let uu___4 =
                        let uu___5 =
                          let uu___6 =
                            let uu___7 = check "abs body" g' body1 in
                            fun ctx01 ->
                              let uu___8 = uu___7 ctx01 in
                              match uu___8 with
                              | Success (x1, g11) ->
                                  let uu___9 =
                                    let uu___10 =
                                      let uu___11 =
                                        let uu___12 =
                                          let uu___13 = as_comp g x1 in
                                          FStarC_Syntax_Util.arrow xs1
                                            uu___13 in
                                        (E_Total, uu___12) in
                                      fun uu___12 ->
                                        Success
                                          (uu___11,
                                            FStar_Pervasives_Native.None) in
                                    uu___10 ctx01 in
                                  (match uu___9 with
                                   | Success (y, g2) ->
                                       let uu___10 =
                                         let uu___11 = and_pre g11 g2 in
                                         (y, uu___11) in
                                       Success uu___10
                                   | err -> err)
                              | Error err -> Error err in
                          with_binders xs1 x uu___6 in
                        uu___5 ctx0 in
                      (match uu___4 with
                       | Success (y, g2) ->
                           let uu___5 =
                             let uu___6 = and_pre g1 g2 in (y, uu___6) in
                           Success uu___5
                       | err -> err)
                  | Error err -> Error err))
      | FStarC_Syntax_Syntax.Tm_arrow
          { FStarC_Syntax_Syntax.bs1 = xs; FStarC_Syntax_Syntax.comp = c;_}
          ->
          let uu___ = open_comp_binders g xs c in
          (match uu___ with
           | (g', xs1, c1) ->
               let uu___1 ctx =
                 let ctx1 =
                   {
                     no_guard = (ctx.no_guard);
                     unfolding_ok = (ctx.unfolding_ok);
                     error_context =
                       (("arrow binders", FStar_Pervasives_Native.None) ::
                       (ctx.error_context))
                   } in
                 let uu___2 = check_binders g xs1 in uu___2 ctx1 in
               (fun ctx0 ->
                  let uu___2 = uu___1 ctx0 in
                  match uu___2 with
                  | Success (x, g1) ->
                      let uu___3 =
                        let uu___4 =
                          let uu___5 =
                            let uu___6 ctx =
                              let ctx1 =
                                {
                                  no_guard = (ctx.no_guard);
                                  unfolding_ok = (ctx.unfolding_ok);
                                  error_context =
                                    (("arrow comp",
                                       FStar_Pervasives_Native.None) ::
                                    (ctx.error_context))
                                } in
                              let uu___7 = check_comp g' c1 in uu___7 ctx1 in
                            fun ctx01 ->
                              let uu___7 = uu___6 ctx01 in
                              match uu___7 with
                              | Success (x1, g11) ->
                                  let uu___8 =
                                    let uu___9 =
                                      let uu___10 =
                                        let uu___11 =
                                          mk_type
                                            (FStarC_Syntax_Syntax.U_max (x1
                                               :: x)) in
                                        (E_Total, uu___11) in
                                      fun uu___11 ->
                                        Success
                                          (uu___10,
                                            FStar_Pervasives_Native.None) in
                                    uu___9 ctx01 in
                                  (match uu___8 with
                                   | Success (y, g2) ->
                                       let uu___9 =
                                         let uu___10 = and_pre g11 g2 in
                                         (y, uu___10) in
                                       Success uu___9
                                   | err -> err)
                              | Error err -> Error err in
                          with_binders xs1 x uu___5 in
                        uu___4 ctx0 in
                      (match uu___3 with
                       | Success (y, g2) ->
                           let uu___4 =
                             let uu___5 = and_pre g1 g2 in (y, uu___5) in
                           Success uu___4
                       | err -> err)
                  | Error err -> Error err))
      | FStarC_Syntax_Syntax.Tm_app uu___ ->
          let rec check_app_arg uu___1 uu___2 =
            match (uu___1, uu___2) with
            | ((eff_hd, t_hd), (arg, arg_qual)) ->
                let uu___3 = is_arrow g t_hd in
                (fun ctx0 ->
                   let uu___4 = uu___3 ctx0 in
                   match uu___4 with
                   | Success (x, g1) ->
                       let uu___5 =
                         let uu___6 =
                           match x with
                           | (x1, eff_arr, t') ->
                               let uu___7 = check "app arg" g arg in
                               (fun ctx01 ->
                                  let uu___8 = uu___7 ctx01 in
                                  match uu___8 with
                                  | Success (x2, g11) ->
                                      let uu___9 =
                                        let uu___10 =
                                          match x2 with
                                          | (eff_arg, t_arg) ->
                                              let uu___11 ctx =
                                                let ctx1 =
                                                  {
                                                    no_guard = (ctx.no_guard);
                                                    unfolding_ok =
                                                      (ctx.unfolding_ok);
                                                    error_context =
                                                      (("app subtyping",
                                                         FStar_Pervasives_Native.None)
                                                      :: (ctx.error_context))
                                                  } in
                                                let uu___12 =
                                                  check_subtype g
                                                    (FStar_Pervasives_Native.Some
                                                       arg) t_arg
                                                    (x1.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                                                uu___12 ctx1 in
                                              (fun ctx02 ->
                                                 let uu___12 = uu___11 ctx02 in
                                                 match uu___12 with
                                                 | Success (x3, g12) ->
                                                     let uu___13 =
                                                       let uu___14 =
                                                         let uu___15 ctx =
                                                           let ctx1 =
                                                             {
                                                               no_guard =
                                                                 (ctx.no_guard);
                                                               unfolding_ok =
                                                                 (ctx.unfolding_ok);
                                                               error_context
                                                                 =
                                                                 (("app arg qual",
                                                                    FStar_Pervasives_Native.None)
                                                                 ::
                                                                 (ctx.error_context))
                                                             } in
                                                           let uu___16 =
                                                             check_arg_qual
                                                               arg_qual
                                                               x1.FStarC_Syntax_Syntax.binder_qual in
                                                           uu___16 ctx1 in
                                                         fun ctx03 ->
                                                           let uu___16 =
                                                             uu___15 ctx03 in
                                                           match uu___16 with
                                                           | Success
                                                               (x4, g13) ->
                                                               let uu___17 =
                                                                 let uu___18
                                                                   =
                                                                   let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    FStarC_Syntax_Subst.subst
                                                                    [
                                                                    FStarC_Syntax_Syntax.NT
                                                                    ((x1.FStarC_Syntax_Syntax.binder_bv),
                                                                    arg)] t' in
                                                                    ((join_eff
                                                                    eff_hd
                                                                    (join_eff
                                                                    eff_arr
                                                                    eff_arg)),
                                                                    uu___20) in
                                                                   fun
                                                                    uu___20
                                                                    ->
                                                                    Success
                                                                    (uu___19,
                                                                    FStar_Pervasives_Native.None) in
                                                                 uu___18
                                                                   ctx03 in
                                                               (match uu___17
                                                                with
                                                                | Success
                                                                    (y, g2)
                                                                    ->
                                                                    let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    and_pre
                                                                    g13 g2 in
                                                                    (y,
                                                                    uu___19) in
                                                                    Success
                                                                    uu___18
                                                                | err -> err)
                                                           | Error err ->
                                                               Error err in
                                                       uu___14 ctx02 in
                                                     (match uu___13 with
                                                      | Success (y, g2) ->
                                                          let uu___14 =
                                                            let uu___15 =
                                                              and_pre g12 g2 in
                                                            (y, uu___15) in
                                                          Success uu___14
                                                      | err -> err)
                                                 | Error err -> Error err) in
                                        uu___10 ctx01 in
                                      (match uu___9 with
                                       | Success (y, g2) ->
                                           let uu___10 =
                                             let uu___11 = and_pre g11 g2 in
                                             (y, uu___11) in
                                           Success uu___10
                                       | err -> err)
                                  | Error err -> Error err) in
                         uu___6 ctx0 in
                       (match uu___5 with
                        | Success (y, g2) ->
                            let uu___6 =
                              let uu___7 = and_pre g1 g2 in (y, uu___7) in
                            Success uu___6
                        | err -> err)
                   | Error err -> Error err) in
          let check_app hd args =
            let uu___1 = check "app head" g hd in
            fun ctx0 ->
              let uu___2 = uu___1 ctx0 in
              match uu___2 with
              | Success (x, g1) ->
                  let uu___3 =
                    let uu___4 =
                      match x with
                      | (eff_hd, t) -> fold check_app_arg (eff_hd, t) args in
                    uu___4 ctx0 in
                  (match uu___3 with
                   | Success (y, g2) ->
                       let uu___4 = let uu___5 = and_pre g1 g2 in (y, uu___5) in
                       Success uu___4
                   | err -> err)
              | Error err -> Error err in
          let uu___1 = FStarC_Syntax_Util.head_and_args_full e1 in
          (match uu___1 with
           | (hd, args) ->
               (match args with
                | (t1, FStar_Pervasives_Native.None)::(t2,
                                                       FStar_Pervasives_Native.None)::[]
                    when FStarC_TypeChecker_Util.short_circuit_head hd ->
                    let uu___2 = check "app head" g hd in
                    (fun ctx0 ->
                       let uu___3 = uu___2 ctx0 in
                       match uu___3 with
                       | Success (x, g1) ->
                           let uu___4 =
                             let uu___5 =
                               match x with
                               | (eff_hd, t_hd) ->
                                   let uu___6 = is_arrow g t_hd in
                                   (fun ctx01 ->
                                      let uu___7 = uu___6 ctx01 in
                                      match uu___7 with
                                      | Success (x1, g11) ->
                                          let uu___8 =
                                            let uu___9 =
                                              match x1 with
                                              | (x2, eff_arr1, s1) ->
                                                  let uu___10 =
                                                    check "app arg" g t1 in
                                                  (fun ctx02 ->
                                                     let uu___11 =
                                                       uu___10 ctx02 in
                                                     match uu___11 with
                                                     | Success (x3, g12) ->
                                                         let uu___12 =
                                                           let uu___13 =
                                                             match x3 with
                                                             | (eff_arg1,
                                                                t_t1) ->
                                                                 let uu___14
                                                                   ctx =
                                                                   let ctx1 =
                                                                    {
                                                                    no_guard
                                                                    =
                                                                    (ctx.no_guard);
                                                                    unfolding_ok
                                                                    =
                                                                    (ctx.unfolding_ok);
                                                                    error_context
                                                                    =
                                                                    (("operator arg1",
                                                                    FStar_Pervasives_Native.None)
                                                                    ::
                                                                    (ctx.error_context))
                                                                    } in
                                                                   let uu___15
                                                                    =
                                                                    check_subtype
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    t1) t_t1
                                                                    (x2.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                                                                   uu___15
                                                                    ctx1 in
                                                                 (fun ctx03
                                                                    ->
                                                                    let uu___15
                                                                    =
                                                                    uu___14
                                                                    ctx03 in
                                                                    match uu___15
                                                                    with
                                                                    | 
                                                                    Success
                                                                    (x4, g13)
                                                                    ->
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    let s11 =
                                                                    FStarC_Syntax_Subst.subst
                                                                    [
                                                                    FStarC_Syntax_Syntax.NT
                                                                    ((x2.FStarC_Syntax_Syntax.binder_bv),
                                                                    t1)] s1 in
                                                                    let uu___18
                                                                    =
                                                                    is_arrow
                                                                    g s11 in
                                                                    fun ctx04
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    uu___18
                                                                    ctx04 in
                                                                    match uu___19
                                                                    with
                                                                    | 
                                                                    Success
                                                                    (x5, g14)
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    match x5
                                                                    with
                                                                    | 
                                                                    (y,
                                                                    eff_arr2,
                                                                    s2) ->
                                                                    let guard_formula
                                                                    =
                                                                    FStarC_TypeChecker_Util.short_circuit
                                                                    hd
                                                                    [
                                                                    (t1,
                                                                    FStar_Pervasives_Native.None)] in
                                                                    let g' =
                                                                    match guard_formula
                                                                    with
                                                                    | 
                                                                    FStarC_TypeChecker_Common.Trivial
                                                                    -> g
                                                                    | 
                                                                    FStarC_TypeChecker_Common.NonTrivial
                                                                    gf ->
                                                                    push_hypothesis
                                                                    g gf in
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    check
                                                                    "app arg"
                                                                    g' t2 in
                                                                    weaken_with_guard_formula
                                                                    guard_formula
                                                                    uu___23 in
                                                                    (fun
                                                                    ctx05 ->
                                                                    let uu___23
                                                                    =
                                                                    uu___22
                                                                    ctx05 in
                                                                    match uu___23
                                                                    with
                                                                    | 
                                                                    Success
                                                                    (x6, g15)
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    match x6
                                                                    with
                                                                    | 
                                                                    (eff_arg2,
                                                                    t_t2) ->
                                                                    let uu___26
                                                                    ctx =
                                                                    let ctx1
                                                                    =
                                                                    {
                                                                    no_guard
                                                                    =
                                                                    (ctx.no_guard);
                                                                    unfolding_ok
                                                                    =
                                                                    (ctx.unfolding_ok);
                                                                    error_context
                                                                    =
                                                                    (("operator arg2",
                                                                    FStar_Pervasives_Native.None)
                                                                    ::
                                                                    (ctx.error_context))
                                                                    } in
                                                                    let uu___27
                                                                    =
                                                                    check_subtype
                                                                    g'
                                                                    (FStar_Pervasives_Native.Some
                                                                    t2) t_t2
                                                                    (y.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                                                                    uu___27
                                                                    ctx1 in
                                                                    (fun
                                                                    ctx06 ->
                                                                    let uu___27
                                                                    =
                                                                    uu___26
                                                                    ctx06 in
                                                                    match uu___27
                                                                    with
                                                                    | 
                                                                    Success
                                                                    (x7, g16)
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    let uu___29
                                                                    =
                                                                    let uu___30
                                                                    =
                                                                    let uu___31
                                                                    =
                                                                    FStarC_Syntax_Subst.subst
                                                                    [
                                                                    FStarC_Syntax_Syntax.NT
                                                                    ((y.FStarC_Syntax_Syntax.binder_bv),
                                                                    t2)] s2 in
                                                                    ((join_eff_l
                                                                    [eff_hd;
                                                                    eff_arr1;
                                                                    eff_arr2;
                                                                    eff_arg1;
                                                                    eff_arg2]),
                                                                    uu___31) in
                                                                    fun
                                                                    uu___31
                                                                    ->
                                                                    Success
                                                                    (uu___30,
                                                                    FStar_Pervasives_Native.None) in
                                                                    uu___29
                                                                    ctx06 in
                                                                    (match uu___28
                                                                    with
                                                                    | 
                                                                    Success
                                                                    (y1, g2)
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    let uu___30
                                                                    =
                                                                    and_pre
                                                                    g16 g2 in
                                                                    (y1,
                                                                    uu___30) in
                                                                    Success
                                                                    uu___29
                                                                    | 
                                                                    err ->
                                                                    err)
                                                                    | 
                                                                    Error err
                                                                    ->
                                                                    Error err) in
                                                                    uu___25
                                                                    ctx05 in
                                                                    (match uu___24
                                                                    with
                                                                    | 
                                                                    Success
                                                                    (y1, g2)
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    and_pre
                                                                    g15 g2 in
                                                                    (y1,
                                                                    uu___26) in
                                                                    Success
                                                                    uu___25
                                                                    | 
                                                                    err ->
                                                                    err)
                                                                    | 
                                                                    Error err
                                                                    ->
                                                                    Error err) in
                                                                    uu___21
                                                                    ctx04 in
                                                                    (match uu___20
                                                                    with
                                                                    | 
                                                                    Success
                                                                    (y, g2)
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    and_pre
                                                                    g14 g2 in
                                                                    (y,
                                                                    uu___22) in
                                                                    Success
                                                                    uu___21
                                                                    | 
                                                                    err ->
                                                                    err)
                                                                    | 
                                                                    Error err
                                                                    ->
                                                                    Error err in
                                                                    uu___17
                                                                    ctx03 in
                                                                    (match uu___16
                                                                    with
                                                                    | 
                                                                    Success
                                                                    (y, g2)
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    and_pre
                                                                    g13 g2 in
                                                                    (y,
                                                                    uu___18) in
                                                                    Success
                                                                    uu___17
                                                                    | 
                                                                    err ->
                                                                    err)
                                                                    | 
                                                                    Error err
                                                                    ->
                                                                    Error err) in
                                                           uu___13 ctx02 in
                                                         (match uu___12 with
                                                          | Success (y, g2)
                                                              ->
                                                              let uu___13 =
                                                                let uu___14 =
                                                                  and_pre g12
                                                                    g2 in
                                                                (y, uu___14) in
                                                              Success uu___13
                                                          | err -> err)
                                                     | Error err -> Error err) in
                                            uu___9 ctx01 in
                                          (match uu___8 with
                                           | Success (y, g2) ->
                                               let uu___9 =
                                                 let uu___10 = and_pre g11 g2 in
                                                 (y, uu___10) in
                                               Success uu___9
                                           | err -> err)
                                      | Error err -> Error err) in
                             uu___5 ctx0 in
                           (match uu___4 with
                            | Success (y, g2) ->
                                let uu___5 =
                                  let uu___6 = and_pre g1 g2 in (y, uu___6) in
                                Success uu___5
                            | err -> err)
                       | Error err -> Error err)
                | uu___2 -> check_app hd args))
      | FStarC_Syntax_Syntax.Tm_ascribed
          { FStarC_Syntax_Syntax.tm = e2;
            FStarC_Syntax_Syntax.asc = (FStar_Pervasives.Inl t, uu___, eq);
            FStarC_Syntax_Syntax.eff_opt = uu___1;_}
          ->
          let uu___2 = check "ascription head" g e2 in
          (fun ctx0 ->
             let uu___3 = uu___2 ctx0 in
             match uu___3 with
             | Success (x, g1) ->
                 let uu___4 =
                   let uu___5 =
                     match x with
                     | (eff, te) ->
                         let uu___6 = check "ascription type" g t in
                         (fun ctx01 ->
                            let uu___7 = uu___6 ctx01 in
                            match uu___7 with
                            | Success (x1, g11) ->
                                let uu___8 =
                                  let uu___9 =
                                    match x1 with
                                    | (uu___10, t') ->
                                        let uu___11 = is_type g t' in
                                        (fun ctx02 ->
                                           let uu___12 = uu___11 ctx02 in
                                           match uu___12 with
                                           | Success (x2, g12) ->
                                               let uu___13 =
                                                 let uu___14 =
                                                   let uu___15 ctx =
                                                     let ctx1 =
                                                       {
                                                         no_guard =
                                                           (ctx.no_guard);
                                                         unfolding_ok =
                                                           (ctx.unfolding_ok);
                                                         error_context =
                                                           (("ascription subtyping",
                                                              FStar_Pervasives_Native.None)
                                                           ::
                                                           (ctx.error_context))
                                                       } in
                                                     let uu___16 =
                                                       check_subtype g
                                                         (FStar_Pervasives_Native.Some
                                                            e2) te t in
                                                     uu___16 ctx1 in
                                                   fun ctx03 ->
                                                     let uu___16 =
                                                       uu___15 ctx03 in
                                                     match uu___16 with
                                                     | Success (x3, g13) ->
                                                         let uu___17 =
                                                           let uu___18
                                                             uu___19 =
                                                             Success
                                                               ((eff, t),
                                                                 FStar_Pervasives_Native.None) in
                                                           uu___18 ctx03 in
                                                         (match uu___17 with
                                                          | Success (y, g2)
                                                              ->
                                                              let uu___18 =
                                                                let uu___19 =
                                                                  and_pre g13
                                                                    g2 in
                                                                (y, uu___19) in
                                                              Success uu___18
                                                          | err -> err)
                                                     | Error err -> Error err in
                                                 uu___14 ctx02 in
                                               (match uu___13 with
                                                | Success (y, g2) ->
                                                    let uu___14 =
                                                      let uu___15 =
                                                        and_pre g12 g2 in
                                                      (y, uu___15) in
                                                    Success uu___14
                                                | err -> err)
                                           | Error err -> Error err) in
                                  uu___9 ctx01 in
                                (match uu___8 with
                                 | Success (y, g2) ->
                                     let uu___9 =
                                       let uu___10 = and_pre g11 g2 in
                                       (y, uu___10) in
                                     Success uu___9
                                 | err -> err)
                            | Error err -> Error err) in
                   uu___5 ctx0 in
                 (match uu___4 with
                  | Success (y, g2) ->
                      let uu___5 = let uu___6 = and_pre g1 g2 in (y, uu___6) in
                      Success uu___5
                  | err -> err)
             | Error err -> Error err)
      | FStarC_Syntax_Syntax.Tm_ascribed
          { FStarC_Syntax_Syntax.tm = e2;
            FStarC_Syntax_Syntax.asc =
              (FStar_Pervasives.Inr c, uu___, uu___1);
            FStarC_Syntax_Syntax.eff_opt = uu___2;_}
          ->
          let uu___3 = FStarC_Syntax_Util.is_tot_or_gtot_comp c in
          if uu___3
          then
            let uu___4 = check "ascription head" g e2 in
            (fun ctx0 ->
               let uu___5 = uu___4 ctx0 in
               match uu___5 with
               | Success (x, g1) ->
                   let uu___6 =
                     let uu___7 =
                       match x with
                       | (eff, te) ->
                           let uu___8 ctx =
                             let ctx1 =
                               {
                                 no_guard = (ctx.no_guard);
                                 unfolding_ok = (ctx.unfolding_ok);
                                 error_context =
                                   (("ascription comp",
                                      FStar_Pervasives_Native.None) ::
                                   (ctx.error_context))
                               } in
                             let uu___9 = check_comp g c in uu___9 ctx1 in
                           (fun ctx01 ->
                              let uu___9 = uu___8 ctx01 in
                              match uu___9 with
                              | Success (x1, g11) ->
                                  let uu___10 =
                                    let uu___11 =
                                      let c_e = as_comp g (eff, te) in
                                      let uu___12 ctx =
                                        let ctx1 =
                                          {
                                            no_guard = (ctx.no_guard);
                                            unfolding_ok = (ctx.unfolding_ok);
                                            error_context =
                                              (("ascription subtyping (comp)",
                                                 FStar_Pervasives_Native.None)
                                              :: (ctx.error_context))
                                          } in
                                        let uu___13 =
                                          check_relation_comp g
                                            (SUBTYPING
                                               (FStar_Pervasives_Native.Some
                                                  e2)) c_e c in
                                        uu___13 ctx1 in
                                      fun ctx02 ->
                                        let uu___13 = uu___12 ctx02 in
                                        match uu___13 with
                                        | Success (x2, g12) ->
                                            let uu___14 =
                                              let uu___15 =
                                                let uu___16 =
                                                  comp_as_tot_or_ghost_and_type
                                                    c in
                                                match uu___16 with
                                                | FStar_Pervasives_Native.Some
                                                    (eff1, t) ->
                                                    (fun uu___17 ->
                                                       Success
                                                         ((eff1, t),
                                                           FStar_Pervasives_Native.None)) in
                                              uu___15 ctx02 in
                                            (match uu___14 with
                                             | Success (y, g2) ->
                                                 let uu___15 =
                                                   let uu___16 =
                                                     and_pre g12 g2 in
                                                   (y, uu___16) in
                                                 Success uu___15
                                             | err -> err)
                                        | Error err -> Error err in
                                    uu___11 ctx01 in
                                  (match uu___10 with
                                   | Success (y, g2) ->
                                       let uu___11 =
                                         let uu___12 = and_pre g11 g2 in
                                         (y, uu___12) in
                                       Success uu___11
                                   | err -> err)
                              | Error err -> Error err) in
                     uu___7 ctx0 in
                   (match uu___6 with
                    | Success (y, g2) ->
                        let uu___7 =
                          let uu___8 = and_pre g1 g2 in (y, uu___8) in
                        Success uu___7
                    | err -> err)
               | Error err -> Error err)
          else
            (let uu___5 =
               let uu___6 =
                 FStarC_Class_Show.show FStarC_Syntax_Print.showable_comp c in
               FStarC_Compiler_Util.format1
                 "Effect ascriptions are not fully handled yet: %s" uu___6 in
             fail uu___5)
      | FStarC_Syntax_Syntax.Tm_let
          { FStarC_Syntax_Syntax.lbs = (false, lb::[]);
            FStarC_Syntax_Syntax.body1 = body;_}
          ->
          let uu___ = lb.FStarC_Syntax_Syntax.lbname in
          (match uu___ with
           | FStar_Pervasives.Inl x ->
               let uu___1 =
                 let uu___2 = FStarC_Syntax_Syntax.mk_binder x in
                 open_term g uu___2 body in
               (match uu___1 with
                | (g', x1, body1) ->
                    let uu___2 =
                      FStarC_Syntax_Util.is_pure_or_ghost_effect
                        lb.FStarC_Syntax_Syntax.lbeff in
                    if uu___2
                    then
                      let uu___3 =
                        check "let definition" g
                          lb.FStarC_Syntax_Syntax.lbdef in
                      (fun ctx0 ->
                         let uu___4 = uu___3 ctx0 in
                         match uu___4 with
                         | Success (x2, g1) ->
                             let uu___5 =
                               let uu___6 =
                                 match x2 with
                                 | (eff_def, tdef) ->
                                     let uu___7 =
                                       check "let type" g
                                         lb.FStarC_Syntax_Syntax.lbtyp in
                                     (fun ctx01 ->
                                        let uu___8 = uu___7 ctx01 in
                                        match uu___8 with
                                        | Success (x3, g11) ->
                                            let uu___9 =
                                              let uu___10 =
                                                match x3 with
                                                | (uu___11, ttyp) ->
                                                    let uu___12 =
                                                      is_type g ttyp in
                                                    (fun ctx02 ->
                                                       let uu___13 =
                                                         uu___12 ctx02 in
                                                       match uu___13 with
                                                       | Success (x4, g12) ->
                                                           let uu___14 =
                                                             let uu___15 =
                                                               let uu___16
                                                                 ctx =
                                                                 let ctx1 =
                                                                   {
                                                                    no_guard
                                                                    =
                                                                    (ctx.no_guard);
                                                                    unfolding_ok
                                                                    =
                                                                    (ctx.unfolding_ok);
                                                                    error_context
                                                                    =
                                                                    (("let subtyping",
                                                                    FStar_Pervasives_Native.None)
                                                                    ::
                                                                    (ctx.error_context))
                                                                   } in
                                                                 let uu___17
                                                                   =
                                                                   check_subtype
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    (lb.FStarC_Syntax_Syntax.lbdef))
                                                                    tdef
                                                                    lb.FStarC_Syntax_Syntax.lbtyp in
                                                                 uu___17 ctx1 in
                                                               fun ctx03 ->
                                                                 let uu___17
                                                                   =
                                                                   uu___16
                                                                    ctx03 in
                                                                 match uu___17
                                                                 with
                                                                 | Success
                                                                    (x5, g13)
                                                                    ->
                                                                    let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    check
                                                                    "let body"
                                                                    g' body1 in
                                                                    fun ctx04
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    uu___21
                                                                    ctx04 in
                                                                    match uu___22
                                                                    with
                                                                    | 
                                                                    Success
                                                                    (x6, g14)
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    match x6
                                                                    with
                                                                    | 
                                                                    (eff_body,
                                                                    t) ->
                                                                    let uu___25
                                                                    =
                                                                    check_no_escape
                                                                    [x1] t in
                                                                    (fun
                                                                    ctx05 ->
                                                                    let uu___26
                                                                    =
                                                                    uu___25
                                                                    ctx05 in
                                                                    match uu___26
                                                                    with
                                                                    | 
                                                                    Success
                                                                    (x7, g15)
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    let uu___28
                                                                    uu___29 =
                                                                    Success
                                                                    (((join_eff
                                                                    eff_def
                                                                    eff_body),
                                                                    t),
                                                                    FStar_Pervasives_Native.None) in
                                                                    uu___28
                                                                    ctx05 in
                                                                    (match uu___27
                                                                    with
                                                                    | 
                                                                    Success
                                                                    (y, g2)
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    let uu___29
                                                                    =
                                                                    and_pre
                                                                    g15 g2 in
                                                                    (y,
                                                                    uu___29) in
                                                                    Success
                                                                    uu___28
                                                                    | 
                                                                    err ->
                                                                    err)
                                                                    | 
                                                                    Error err
                                                                    ->
                                                                    Error err) in
                                                                    uu___24
                                                                    ctx04 in
                                                                    (match uu___23
                                                                    with
                                                                    | 
                                                                    Success
                                                                    (y, g2)
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    and_pre
                                                                    g14 g2 in
                                                                    (y,
                                                                    uu___25) in
                                                                    Success
                                                                    uu___24
                                                                    | 
                                                                    err ->
                                                                    err)
                                                                    | 
                                                                    Error err
                                                                    ->
                                                                    Error err in
                                                                    with_definition
                                                                    x1 x4
                                                                    lb.FStarC_Syntax_Syntax.lbdef
                                                                    uu___20 in
                                                                    uu___19
                                                                    ctx03 in
                                                                    (match uu___18
                                                                    with
                                                                    | 
                                                                    Success
                                                                    (y, g2)
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    and_pre
                                                                    g13 g2 in
                                                                    (y,
                                                                    uu___20) in
                                                                    Success
                                                                    uu___19
                                                                    | 
                                                                    err ->
                                                                    err)
                                                                 | Error err
                                                                    ->
                                                                    Error err in
                                                             uu___15 ctx02 in
                                                           (match uu___14
                                                            with
                                                            | Success 
                                                                (y, g2) ->
                                                                let uu___15 =
                                                                  let uu___16
                                                                    =
                                                                    and_pre
                                                                    g12 g2 in
                                                                  (y,
                                                                    uu___16) in
                                                                Success
                                                                  uu___15
                                                            | err -> err)
                                                       | Error err ->
                                                           Error err) in
                                              uu___10 ctx01 in
                                            (match uu___9 with
                                             | Success (y, g2) ->
                                                 let uu___10 =
                                                   let uu___11 =
                                                     and_pre g11 g2 in
                                                   (y, uu___11) in
                                                 Success uu___10
                                             | err -> err)
                                        | Error err -> Error err) in
                               uu___6 ctx0 in
                             (match uu___5 with
                              | Success (y, g2) ->
                                  let uu___6 =
                                    let uu___7 = and_pre g1 g2 in (y, uu___7) in
                                  Success uu___6
                              | err -> err)
                         | Error err -> Error err)
                    else
                      (let uu___4 =
                         let uu___5 =
                           FStarC_Class_Show.show
                             FStarC_Ident.showable_lident
                             lb.FStarC_Syntax_Syntax.lbeff in
                         FStarC_Compiler_Util.format1
                           "Let binding is effectful (lbeff = %s)" uu___5 in
                       fail uu___4)))
      | FStarC_Syntax_Syntax.Tm_match
          { FStarC_Syntax_Syntax.scrutinee = sc;
            FStarC_Syntax_Syntax.ret_opt = FStar_Pervasives_Native.None;
            FStarC_Syntax_Syntax.brs = branches;
            FStarC_Syntax_Syntax.rc_opt1 = rc_opt;_}
          ->
          let uu___ = check "scrutinee" g sc in
          (fun ctx0 ->
             let uu___1 = uu___ ctx0 in
             match uu___1 with
             | Success (x, g1) ->
                 let uu___2 =
                   let uu___3 =
                     match x with
                     | (eff_sc, t_sc) ->
                         let uu___4 ctx =
                           let ctx1 =
                             {
                               no_guard = (ctx.no_guard);
                               unfolding_ok = (ctx.unfolding_ok);
                               error_context =
                                 (("universe_of",
                                    (FStar_Pervasives_Native.Some
                                       (CtxTerm t_sc))) ::
                                 (ctx.error_context))
                             } in
                           let uu___5 = universe_of g t_sc in uu___5 ctx1 in
                         (fun ctx01 ->
                            let uu___5 = uu___4 ctx01 in
                            match uu___5 with
                            | Success (x1, g11) ->
                                let uu___6 =
                                  let uu___7 =
                                    let rec check_branches path_condition
                                      branch_typ_opt branches1 =
                                      match branches1 with
                                      | [] ->
                                          (match branch_typ_opt with
                                           | FStar_Pervasives_Native.None ->
                                               fail
                                                 "could not compute a type for the match"
                                           | FStar_Pervasives_Native.Some et
                                               ->
                                               let uu___8 =
                                                 boolean_negation_simp
                                                   path_condition in
                                               (match uu___8 with
                                                | FStar_Pervasives_Native.None
                                                    ->
                                                    (fun uu___9 ->
                                                       Success
                                                         (et,
                                                           FStar_Pervasives_Native.None))
                                                | FStar_Pervasives_Native.Some
                                                    g2 ->
                                                    let uu___9 =
                                                      let uu___10 =
                                                        FStarC_Syntax_Util.b2t
                                                          g2 in
                                                      guard uu___10 in
                                                    (fun ctx02 ->
                                                       let uu___10 =
                                                         uu___9 ctx02 in
                                                       match uu___10 with
                                                       | Success (x2, g12) ->
                                                           let uu___11 =
                                                             let uu___12
                                                               uu___13 =
                                                               Success
                                                                 (et,
                                                                   FStar_Pervasives_Native.None) in
                                                             uu___12 ctx02 in
                                                           (match uu___11
                                                            with
                                                            | Success
                                                                (y, g21) ->
                                                                let uu___12 =
                                                                  let uu___13
                                                                    =
                                                                    and_pre
                                                                    g12 g21 in
                                                                  (y,
                                                                    uu___13) in
                                                                Success
                                                                  uu___12
                                                            | err -> err)
                                                       | Error err ->
                                                           Error err)))
                                      | (p, FStar_Pervasives_Native.None, b)::rest
                                          ->
                                          let uu___8 =
                                            open_branch g
                                              (p,
                                                FStar_Pervasives_Native.None,
                                                b) in
                                          (match uu___8 with
                                           | (uu___9, (p1, uu___10, b1)) ->
                                               let uu___11 ctx =
                                                 let ctx1 =
                                                   {
                                                     no_guard =
                                                       (ctx.no_guard);
                                                     unfolding_ok =
                                                       (ctx.unfolding_ok);
                                                     error_context =
                                                       (("check_pat",
                                                          FStar_Pervasives_Native.None)
                                                       ::
                                                       (ctx.error_context))
                                                   } in
                                                 let uu___12 =
                                                   check_pat g p1 t_sc in
                                                 uu___12 ctx1 in
                                               (fun ctx02 ->
                                                  let uu___12 = uu___11 ctx02 in
                                                  match uu___12 with
                                                  | Success (x2, g12) ->
                                                      let uu___13 =
                                                        let uu___14 =
                                                          match x2 with
                                                          | (bs, us) ->
                                                              let uu___15 =
                                                                pattern_branch_condition
                                                                  g sc p1 in
                                                              (fun ctx03 ->
                                                                 let uu___16
                                                                   =
                                                                   uu___15
                                                                    ctx03 in
                                                                 match uu___16
                                                                 with
                                                                 | Success
                                                                    (x3, g13)
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    let pat_sc_eq
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    FStarC_TypeChecker_PatternUtils.raw_pat_as_exp
                                                                    g.tcenv
                                                                    p1 in
                                                                    FStarC_Compiler_Util.must
                                                                    uu___21 in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu___20 in
                                                                    FStarC_Syntax_Util.mk_eq2
                                                                    x1 t_sc
                                                                    sc
                                                                    uu___19 in
                                                                    let uu___19
                                                                    =
                                                                    combine_path_and_branch_condition
                                                                    path_condition
                                                                    x3
                                                                    pat_sc_eq in
                                                                    match uu___19
                                                                    with
                                                                    | 
                                                                    (this_path_condition,
                                                                    next_path_condition)
                                                                    ->
                                                                    let g' =
                                                                    push_binders
                                                                    g bs in
                                                                    let g'1 =
                                                                    push_hypothesis
                                                                    g'
                                                                    this_path_condition in
                                                                    let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    ctx =
                                                                    let ctx1
                                                                    =
                                                                    {
                                                                    no_guard
                                                                    =
                                                                    (ctx.no_guard);
                                                                    unfolding_ok
                                                                    =
                                                                    (ctx.unfolding_ok);
                                                                    error_context
                                                                    =
                                                                    (("branch",
                                                                    (FStar_Pervasives_Native.Some
                                                                    (CtxTerm
                                                                    b1))) ::
                                                                    (ctx.error_context))
                                                                    } in
                                                                    let uu___24
                                                                    =
                                                                    check
                                                                    "branch"
                                                                    g'1 b1 in
                                                                    uu___24
                                                                    ctx1 in
                                                                    fun ctx04
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    uu___23
                                                                    ctx04 in
                                                                    match uu___24
                                                                    with
                                                                    | 
                                                                    Success
                                                                    (x4, g14)
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    match x4
                                                                    with
                                                                    | 
                                                                    (eff_br,
                                                                    tbr) ->
                                                                    (match branch_typ_opt
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    check_no_escape
                                                                    bs tbr in
                                                                    (fun
                                                                    ctx05 ->
                                                                    let uu___28
                                                                    =
                                                                    uu___27
                                                                    ctx05 in
                                                                    match uu___28
                                                                    with
                                                                    | 
                                                                    Success
                                                                    (x5, g15)
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    let uu___30
                                                                    uu___31 =
                                                                    Success
                                                                    ((eff_br,
                                                                    tbr),
                                                                    FStar_Pervasives_Native.None) in
                                                                    uu___30
                                                                    ctx05 in
                                                                    (match uu___29
                                                                    with
                                                                    | 
                                                                    Success
                                                                    (y, g2)
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    let uu___31
                                                                    =
                                                                    and_pre
                                                                    g15 g2 in
                                                                    (y,
                                                                    uu___31) in
                                                                    Success
                                                                    uu___30
                                                                    | 
                                                                    err ->
                                                                    err)
                                                                    | 
                                                                    Error err
                                                                    ->
                                                                    Error err)
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (acc_eff,
                                                                    expect_tbr)
                                                                    ->
                                                                    let uu___27
                                                                    ctx =
                                                                    let ctx1
                                                                    =
                                                                    {
                                                                    no_guard
                                                                    =
                                                                    (ctx.no_guard);
                                                                    unfolding_ok
                                                                    =
                                                                    (ctx.unfolding_ok);
                                                                    error_context
                                                                    =
                                                                    (("check_branch_subtype",
                                                                    (FStar_Pervasives_Native.Some
                                                                    (CtxRel
                                                                    (tbr,
                                                                    (SUBTYPING
                                                                    (FStar_Pervasives_Native.Some
                                                                    b1)),
                                                                    expect_tbr))))
                                                                    ::
                                                                    (ctx.error_context))
                                                                    } in
                                                                    let uu___28
                                                                    =
                                                                    check_subtype
                                                                    g'1
                                                                    (FStar_Pervasives_Native.Some
                                                                    b1) tbr
                                                                    expect_tbr in
                                                                    uu___28
                                                                    ctx1 in
                                                                    (fun
                                                                    ctx05 ->
                                                                    let uu___28
                                                                    =
                                                                    uu___27
                                                                    ctx05 in
                                                                    match uu___28
                                                                    with
                                                                    | 
                                                                    Success
                                                                    (x5, g15)
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    let uu___30
                                                                    uu___31 =
                                                                    Success
                                                                    (((join_eff
                                                                    eff_br
                                                                    acc_eff),
                                                                    expect_tbr),
                                                                    FStar_Pervasives_Native.None) in
                                                                    uu___30
                                                                    ctx05 in
                                                                    (match uu___29
                                                                    with
                                                                    | 
                                                                    Success
                                                                    (y, g2)
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    let uu___31
                                                                    =
                                                                    and_pre
                                                                    g15 g2 in
                                                                    (y,
                                                                    uu___31) in
                                                                    Success
                                                                    uu___30
                                                                    | 
                                                                    err ->
                                                                    err)
                                                                    | 
                                                                    Error err
                                                                    ->
                                                                    Error err)) in
                                                                    uu___26
                                                                    ctx04 in
                                                                    (match uu___25
                                                                    with
                                                                    | 
                                                                    Success
                                                                    (y, g2)
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    and_pre
                                                                    g14 g2 in
                                                                    (y,
                                                                    uu___27) in
                                                                    Success
                                                                    uu___26
                                                                    | 
                                                                    err ->
                                                                    err)
                                                                    | 
                                                                    Error err
                                                                    ->
                                                                    Error err in
                                                                    weaken
                                                                    this_path_condition
                                                                    uu___22 in
                                                                    with_binders
                                                                    bs us
                                                                    uu___21 in
                                                                    (fun
                                                                    ctx04 ->
                                                                    let uu___21
                                                                    =
                                                                    uu___20
                                                                    ctx04 in
                                                                    match uu___21
                                                                    with
                                                                    | 
                                                                    Success
                                                                    (x4, g14)
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    match x4
                                                                    with
                                                                    | 
                                                                    (eff_br,
                                                                    tbr) ->
                                                                    (match 
                                                                    p1.FStarC_Syntax_Syntax.v
                                                                    with
                                                                    | 
                                                                    FStarC_Syntax_Syntax.Pat_var
                                                                    uu___24
                                                                    ->
                                                                    (match rest
                                                                    with
                                                                    | 
                                                                    uu___25::uu___26
                                                                    ->
                                                                    fail
                                                                    "Redundant branches after wildcard"
                                                                    | 
                                                                    uu___25
                                                                    ->
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    Success
                                                                    ((eff_br,
                                                                    tbr),
                                                                    FStar_Pervasives_Native.None)))
                                                                    | 
                                                                    uu___24
                                                                    ->
                                                                    check_branches
                                                                    next_path_condition
                                                                    (FStar_Pervasives_Native.Some
                                                                    (eff_br,
                                                                    tbr))
                                                                    rest) in
                                                                    uu___23
                                                                    ctx04 in
                                                                    (match uu___22
                                                                    with
                                                                    | 
                                                                    Success
                                                                    (y, g2)
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    and_pre
                                                                    g14 g2 in
                                                                    (y,
                                                                    uu___24) in
                                                                    Success
                                                                    uu___23
                                                                    | 
                                                                    err ->
                                                                    err)
                                                                    | 
                                                                    Error err
                                                                    ->
                                                                    Error err) in
                                                                    uu___18
                                                                    ctx03 in
                                                                    (match uu___17
                                                                    with
                                                                    | 
                                                                    Success
                                                                    (y, g2)
                                                                    ->
                                                                    let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    and_pre
                                                                    g13 g2 in
                                                                    (y,
                                                                    uu___19) in
                                                                    Success
                                                                    uu___18
                                                                    | 
                                                                    err ->
                                                                    err)
                                                                 | Error err
                                                                    ->
                                                                    Error err) in
                                                        uu___14 ctx02 in
                                                      (match uu___13 with
                                                       | Success (y, g2) ->
                                                           let uu___14 =
                                                             let uu___15 =
                                                               and_pre g12 g2 in
                                                             (y, uu___15) in
                                                           Success uu___14
                                                       | err -> err)
                                                  | Error err -> Error err)) in
                                    let uu___8 =
                                      match rc_opt with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStarC_Syntax_Syntax.residual_effect
                                              = uu___9;
                                            FStarC_Syntax_Syntax.residual_typ
                                              = FStar_Pervasives_Native.Some
                                              t;
                                            FStarC_Syntax_Syntax.residual_flags
                                              = uu___10;_}
                                          ->
                                          let uu___11 ctx =
                                            let ctx1 =
                                              {
                                                no_guard = (ctx.no_guard);
                                                unfolding_ok =
                                                  (ctx.unfolding_ok);
                                                error_context =
                                                  (("residual type",
                                                     (FStar_Pervasives_Native.Some
                                                        (CtxTerm t))) ::
                                                  (ctx.error_context))
                                              } in
                                            let uu___12 = universe_of g t in
                                            uu___12 ctx1 in
                                          (fun ctx02 ->
                                             let uu___12 = uu___11 ctx02 in
                                             match uu___12 with
                                             | Success (x2, g12) ->
                                                 let uu___13 =
                                                   let uu___14 uu___15 =
                                                     Success
                                                       ((FStar_Pervasives_Native.Some
                                                           (E_Total, t)),
                                                         FStar_Pervasives_Native.None) in
                                                   uu___14 ctx02 in
                                                 (match uu___13 with
                                                  | Success (y, g2) ->
                                                      let uu___14 =
                                                        let uu___15 =
                                                          and_pre g12 g2 in
                                                        (y, uu___15) in
                                                      Success uu___14
                                                  | err -> err)
                                             | Error err -> Error err)
                                      | uu___9 ->
                                          (fun uu___10 ->
                                             Success
                                               (FStar_Pervasives_Native.None,
                                                 FStar_Pervasives_Native.None)) in
                                    fun ctx02 ->
                                      let uu___9 = uu___8 ctx02 in
                                      match uu___9 with
                                      | Success (x2, g12) ->
                                          let uu___10 =
                                            let uu___11 =
                                              let uu___12 =
                                                let ctx =
                                                  match x2 with
                                                  | FStar_Pervasives_Native.None
                                                      ->
                                                      FStar_Pervasives_Native.None
                                                  | FStar_Pervasives_Native.Some
                                                      (uu___13, t) ->
                                                      FStar_Pervasives_Native.Some
                                                        (CtxTerm t) in
                                                fun ctx1 ->
                                                  let ctx2 =
                                                    {
                                                      no_guard =
                                                        (ctx1.no_guard);
                                                      unfolding_ok =
                                                        (ctx1.unfolding_ok);
                                                      error_context =
                                                        (("check_branches",
                                                           ctx) ::
                                                        (ctx1.error_context))
                                                    } in
                                                  let uu___13 =
                                                    check_branches
                                                      FStarC_Syntax_Util.exp_true_bool
                                                      x2 branches in
                                                  uu___13 ctx2 in
                                              fun ctx03 ->
                                                let uu___13 = uu___12 ctx03 in
                                                match uu___13 with
                                                | Success (x3, g13) ->
                                                    let uu___14 =
                                                      let uu___15 =
                                                        match x3 with
                                                        | (eff_br, t_br) ->
                                                            (fun uu___16 ->
                                                               Success
                                                                 (((join_eff
                                                                    eff_sc
                                                                    eff_br),
                                                                    t_br),
                                                                   FStar_Pervasives_Native.None)) in
                                                      uu___15 ctx03 in
                                                    (match uu___14 with
                                                     | Success (y, g2) ->
                                                         let uu___15 =
                                                           let uu___16 =
                                                             and_pre g13 g2 in
                                                           (y, uu___16) in
                                                         Success uu___15
                                                     | err -> err)
                                                | Error err -> Error err in
                                            uu___11 ctx02 in
                                          (match uu___10 with
                                           | Success (y, g2) ->
                                               let uu___11 =
                                                 let uu___12 = and_pre g12 g2 in
                                                 (y, uu___12) in
                                               Success uu___11
                                           | err -> err)
                                      | Error err -> Error err in
                                  uu___7 ctx01 in
                                (match uu___6 with
                                 | Success (y, g2) ->
                                     let uu___7 =
                                       let uu___8 = and_pre g11 g2 in
                                       (y, uu___8) in
                                     Success uu___7
                                 | err -> err)
                            | Error err -> Error err) in
                   uu___3 ctx0 in
                 (match uu___2 with
                  | Success (y, g2) ->
                      let uu___3 = let uu___4 = and_pre g1 g2 in (y, uu___4) in
                      Success uu___3
                  | err -> err)
             | Error err -> Error err)
      | FStarC_Syntax_Syntax.Tm_match
          { FStarC_Syntax_Syntax.scrutinee = sc;
            FStarC_Syntax_Syntax.ret_opt = FStar_Pervasives_Native.Some
              (as_x,
               (FStar_Pervasives.Inl returns_ty,
                FStar_Pervasives_Native.None, eq));
            FStarC_Syntax_Syntax.brs = branches;
            FStarC_Syntax_Syntax.rc_opt1 = rc_opt;_}
          ->
          let uu___ = check "scrutinee" g sc in
          (fun ctx0 ->
             let uu___1 = uu___ ctx0 in
             match uu___1 with
             | Success (x, g1) ->
                 let uu___2 =
                   let uu___3 =
                     match x with
                     | (eff_sc, t_sc) ->
                         let uu___4 ctx =
                           let ctx1 =
                             {
                               no_guard = (ctx.no_guard);
                               unfolding_ok = (ctx.unfolding_ok);
                               error_context =
                                 (("universe_of",
                                    (FStar_Pervasives_Native.Some
                                       (CtxTerm t_sc))) ::
                                 (ctx.error_context))
                             } in
                           let uu___5 = universe_of g t_sc in uu___5 ctx1 in
                         (fun ctx01 ->
                            let uu___5 = uu___4 ctx01 in
                            match uu___5 with
                            | Success (x1, g11) ->
                                let uu___6 =
                                  let uu___7 =
                                    let as_x1 =
                                      {
                                        FStarC_Syntax_Syntax.binder_bv =
                                          (let uu___8 =
                                             as_x.FStarC_Syntax_Syntax.binder_bv in
                                           {
                                             FStarC_Syntax_Syntax.ppname =
                                               (uu___8.FStarC_Syntax_Syntax.ppname);
                                             FStarC_Syntax_Syntax.index =
                                               (uu___8.FStarC_Syntax_Syntax.index);
                                             FStarC_Syntax_Syntax.sort = t_sc
                                           });
                                        FStarC_Syntax_Syntax.binder_qual =
                                          (as_x.FStarC_Syntax_Syntax.binder_qual);
                                        FStarC_Syntax_Syntax.binder_positivity
                                          =
                                          (as_x.FStarC_Syntax_Syntax.binder_positivity);
                                        FStarC_Syntax_Syntax.binder_attrs =
                                          (as_x.FStarC_Syntax_Syntax.binder_attrs)
                                      } in
                                    let uu___8 = open_term g as_x1 returns_ty in
                                    match uu___8 with
                                    | (g_as_x, as_x2, returns_ty1) ->
                                        let uu___9 =
                                          let uu___10 =
                                            check "return type" g_as_x
                                              returns_ty1 in
                                          with_binders [as_x2] [x1] uu___10 in
                                        (fun ctx02 ->
                                           let uu___10 = uu___9 ctx02 in
                                           match uu___10 with
                                           | Success (x2, g12) ->
                                               let uu___11 =
                                                 let uu___12 =
                                                   match x2 with
                                                   | (_eff_t, returns_ty_t)
                                                       ->
                                                       let uu___13 =
                                                         is_type g_as_x
                                                           returns_ty_t in
                                                       (fun ctx03 ->
                                                          let uu___14 =
                                                            uu___13 ctx03 in
                                                          match uu___14 with
                                                          | Success (x3, g13)
                                                              ->
                                                              let uu___15 =
                                                                let uu___16 =
                                                                  let rec check_branches
                                                                    path_condition
                                                                    branches1
                                                                    acc_eff =
                                                                    match branches1
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    let uu___17
                                                                    =
                                                                    boolean_negation_simp
                                                                    path_condition in
                                                                    (match uu___17
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    Success
                                                                    (acc_eff,
                                                                    FStar_Pervasives_Native.None))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    g2 ->
                                                                    let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    FStarC_Syntax_Util.b2t
                                                                    g2 in
                                                                    guard
                                                                    uu___19 in
                                                                    (fun
                                                                    ctx04 ->
                                                                    let uu___19
                                                                    =
                                                                    uu___18
                                                                    ctx04 in
                                                                    match uu___19
                                                                    with
                                                                    | 
                                                                    Success
                                                                    (x4, g14)
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    let uu___21
                                                                    uu___22 =
                                                                    Success
                                                                    (acc_eff,
                                                                    FStar_Pervasives_Native.None) in
                                                                    uu___21
                                                                    ctx04 in
                                                                    (match uu___20
                                                                    with
                                                                    | 
                                                                    Success
                                                                    (y, g21)
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    and_pre
                                                                    g14 g21 in
                                                                    (y,
                                                                    uu___22) in
                                                                    Success
                                                                    uu___21
                                                                    | 
                                                                    err ->
                                                                    err)
                                                                    | 
                                                                    Error err
                                                                    ->
                                                                    Error err))
                                                                    | 
                                                                    (p,
                                                                    FStar_Pervasives_Native.None,
                                                                    b)::rest
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    open_branch
                                                                    g
                                                                    (p,
                                                                    FStar_Pervasives_Native.None,
                                                                    b) in
                                                                    (match uu___17
                                                                    with
                                                                    | 
                                                                    (uu___18,
                                                                    (p1,
                                                                    uu___19,
                                                                    b1)) ->
                                                                    let uu___20
                                                                    ctx =
                                                                    let ctx1
                                                                    =
                                                                    {
                                                                    no_guard
                                                                    =
                                                                    (ctx.no_guard);
                                                                    unfolding_ok
                                                                    =
                                                                    (ctx.unfolding_ok);
                                                                    error_context
                                                                    =
                                                                    (("check_pat",
                                                                    FStar_Pervasives_Native.None)
                                                                    ::
                                                                    (ctx.error_context))
                                                                    } in
                                                                    let uu___21
                                                                    =
                                                                    check_pat
                                                                    g p1 t_sc in
                                                                    uu___21
                                                                    ctx1 in
                                                                    (fun
                                                                    ctx04 ->
                                                                    let uu___21
                                                                    =
                                                                    uu___20
                                                                    ctx04 in
                                                                    match uu___21
                                                                    with
                                                                    | 
                                                                    Success
                                                                    (x4, g14)
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    match x4
                                                                    with
                                                                    | 
                                                                    (bs, us)
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    pattern_branch_condition
                                                                    g sc p1 in
                                                                    (fun
                                                                    ctx05 ->
                                                                    let uu___25
                                                                    =
                                                                    uu___24
                                                                    ctx05 in
                                                                    match uu___25
                                                                    with
                                                                    | 
                                                                    Success
                                                                    (x5, g15)
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    let pat_sc_eq
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    let uu___29
                                                                    =
                                                                    let uu___30
                                                                    =
                                                                    FStarC_TypeChecker_PatternUtils.raw_pat_as_exp
                                                                    g.tcenv
                                                                    p1 in
                                                                    FStarC_Compiler_Util.must
                                                                    uu___30 in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu___29 in
                                                                    FStarC_Syntax_Util.mk_eq2
                                                                    x1 t_sc
                                                                    sc
                                                                    uu___28 in
                                                                    let uu___28
                                                                    =
                                                                    combine_path_and_branch_condition
                                                                    path_condition
                                                                    x5
                                                                    pat_sc_eq in
                                                                    match uu___28
                                                                    with
                                                                    | 
                                                                    (this_path_condition,
                                                                    next_path_condition)
                                                                    ->
                                                                    let g' =
                                                                    push_binders
                                                                    g bs in
                                                                    let g'1 =
                                                                    push_hypothesis
                                                                    g'
                                                                    this_path_condition in
                                                                    let uu___29
                                                                    =
                                                                    let uu___30
                                                                    =
                                                                    let uu___31
                                                                    =
                                                                    let uu___32
                                                                    =
                                                                    check
                                                                    "branch"
                                                                    g'1 b1 in
                                                                    fun ctx06
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    uu___32
                                                                    ctx06 in
                                                                    match uu___33
                                                                    with
                                                                    | 
                                                                    Success
                                                                    (x6, g16)
                                                                    ->
                                                                    let uu___34
                                                                    =
                                                                    let uu___35
                                                                    =
                                                                    match x6
                                                                    with
                                                                    | 
                                                                    (eff_br,
                                                                    tbr) ->
                                                                    let expect_tbr
                                                                    =
                                                                    FStarC_Syntax_Subst.subst
                                                                    [
                                                                    FStarC_Syntax_Syntax.NT
                                                                    ((as_x2.FStarC_Syntax_Syntax.binder_bv),
                                                                    sc)]
                                                                    returns_ty1 in
                                                                    let rel =
                                                                    if eq
                                                                    then
                                                                    EQUALITY
                                                                    else
                                                                    SUBTYPING
                                                                    (FStar_Pervasives_Native.Some
                                                                    b1) in
                                                                    let uu___36
                                                                    ctx =
                                                                    let ctx1
                                                                    =
                                                                    {
                                                                    no_guard
                                                                    =
                                                                    (ctx.no_guard);
                                                                    unfolding_ok
                                                                    =
                                                                    (ctx.unfolding_ok);
                                                                    error_context
                                                                    =
                                                                    (("branch check relation",
                                                                    FStar_Pervasives_Native.None)
                                                                    ::
                                                                    (ctx.error_context))
                                                                    } in
                                                                    let uu___37
                                                                    =
                                                                    check_relation
                                                                    g'1 rel
                                                                    tbr
                                                                    expect_tbr in
                                                                    uu___37
                                                                    ctx1 in
                                                                    (fun
                                                                    ctx07 ->
                                                                    let uu___37
                                                                    =
                                                                    uu___36
                                                                    ctx07 in
                                                                    match uu___37
                                                                    with
                                                                    | 
                                                                    Success
                                                                    (x7, g17)
                                                                    ->
                                                                    let uu___38
                                                                    =
                                                                    let uu___39
                                                                    uu___40 =
                                                                    Success
                                                                    (((join_eff
                                                                    eff_br
                                                                    acc_eff),
                                                                    expect_tbr),
                                                                    FStar_Pervasives_Native.None) in
                                                                    uu___39
                                                                    ctx07 in
                                                                    (match uu___38
                                                                    with
                                                                    | 
                                                                    Success
                                                                    (y, g2)
                                                                    ->
                                                                    let uu___39
                                                                    =
                                                                    let uu___40
                                                                    =
                                                                    and_pre
                                                                    g17 g2 in
                                                                    (y,
                                                                    uu___40) in
                                                                    Success
                                                                    uu___39
                                                                    | 
                                                                    err ->
                                                                    err)
                                                                    | 
                                                                    Error err
                                                                    ->
                                                                    Error err) in
                                                                    uu___35
                                                                    ctx06 in
                                                                    (match uu___34
                                                                    with
                                                                    | 
                                                                    Success
                                                                    (y, g2)
                                                                    ->
                                                                    let uu___35
                                                                    =
                                                                    let uu___36
                                                                    =
                                                                    and_pre
                                                                    g16 g2 in
                                                                    (y,
                                                                    uu___36) in
                                                                    Success
                                                                    uu___35
                                                                    | 
                                                                    err ->
                                                                    err)
                                                                    | 
                                                                    Error err
                                                                    ->
                                                                    Error err in
                                                                    weaken
                                                                    this_path_condition
                                                                    uu___31 in
                                                                    with_binders
                                                                    bs us
                                                                    uu___30 in
                                                                    (fun
                                                                    ctx06 ->
                                                                    let uu___30
                                                                    =
                                                                    uu___29
                                                                    ctx06 in
                                                                    match uu___30
                                                                    with
                                                                    | 
                                                                    Success
                                                                    (x6, g16)
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    let uu___32
                                                                    =
                                                                    match x6
                                                                    with
                                                                    | 
                                                                    (eff_br,
                                                                    tbr) ->
                                                                    (match 
                                                                    p1.FStarC_Syntax_Syntax.v
                                                                    with
                                                                    | 
                                                                    FStarC_Syntax_Syntax.Pat_var
                                                                    uu___33
                                                                    ->
                                                                    (match rest
                                                                    with
                                                                    | 
                                                                    uu___34::uu___35
                                                                    ->
                                                                    fail
                                                                    "Redundant branches after wildcard"
                                                                    | 
                                                                    uu___34
                                                                    ->
                                                                    (fun
                                                                    uu___35
                                                                    ->
                                                                    Success
                                                                    (eff_br,
                                                                    FStar_Pervasives_Native.None)))
                                                                    | 
                                                                    uu___33
                                                                    ->
                                                                    check_branches
                                                                    next_path_condition
                                                                    rest
                                                                    eff_br) in
                                                                    uu___32
                                                                    ctx06 in
                                                                    (match uu___31
                                                                    with
                                                                    | 
                                                                    Success
                                                                    (y, g2)
                                                                    ->
                                                                    let uu___32
                                                                    =
                                                                    let uu___33
                                                                    =
                                                                    and_pre
                                                                    g16 g2 in
                                                                    (y,
                                                                    uu___33) in
                                                                    Success
                                                                    uu___32
                                                                    | 
                                                                    err ->
                                                                    err)
                                                                    | 
                                                                    Error err
                                                                    ->
                                                                    Error err) in
                                                                    uu___27
                                                                    ctx05 in
                                                                    (match uu___26
                                                                    with
                                                                    | 
                                                                    Success
                                                                    (y, g2)
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    and_pre
                                                                    g15 g2 in
                                                                    (y,
                                                                    uu___28) in
                                                                    Success
                                                                    uu___27
                                                                    | 
                                                                    err ->
                                                                    err)
                                                                    | 
                                                                    Error err
                                                                    ->
                                                                    Error err) in
                                                                    uu___23
                                                                    ctx04 in
                                                                    (match uu___22
                                                                    with
                                                                    | 
                                                                    Success
                                                                    (y, g2)
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    and_pre
                                                                    g14 g2 in
                                                                    (y,
                                                                    uu___24) in
                                                                    Success
                                                                    uu___23
                                                                    | 
                                                                    err ->
                                                                    err)
                                                                    | 
                                                                    Error err
                                                                    ->
                                                                    Error err)) in
                                                                  let uu___17
                                                                    =
                                                                    check_branches
                                                                    FStarC_Syntax_Util.exp_true_bool
                                                                    branches
                                                                    E_Total in
                                                                  fun ctx04
                                                                    ->
                                                                    let uu___18
                                                                    =
                                                                    uu___17
                                                                    ctx04 in
                                                                    match uu___18
                                                                    with
                                                                    | 
                                                                    Success
                                                                    (x4, g14)
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    let ty =
                                                                    FStarC_Syntax_Subst.subst
                                                                    [
                                                                    FStarC_Syntax_Syntax.NT
                                                                    ((as_x2.FStarC_Syntax_Syntax.binder_bv),
                                                                    sc)]
                                                                    returns_ty1 in
                                                                    fun
                                                                    uu___21
                                                                    ->
                                                                    Success
                                                                    ((x4, ty),
                                                                    FStar_Pervasives_Native.None) in
                                                                    uu___20
                                                                    ctx04 in
                                                                    (match uu___19
                                                                    with
                                                                    | 
                                                                    Success
                                                                    (y, g2)
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    and_pre
                                                                    g14 g2 in
                                                                    (y,
                                                                    uu___21) in
                                                                    Success
                                                                    uu___20
                                                                    | 
                                                                    err ->
                                                                    err)
                                                                    | 
                                                                    Error err
                                                                    ->
                                                                    Error err in
                                                                uu___16 ctx03 in
                                                              (match uu___15
                                                               with
                                                               | Success
                                                                   (y, g2) ->
                                                                   let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    and_pre
                                                                    g13 g2 in
                                                                    (y,
                                                                    uu___17) in
                                                                   Success
                                                                    uu___16
                                                               | err -> err)
                                                          | Error err ->
                                                              Error err) in
                                                 uu___12 ctx02 in
                                               (match uu___11 with
                                                | Success (y, g2) ->
                                                    let uu___12 =
                                                      let uu___13 =
                                                        and_pre g12 g2 in
                                                      (y, uu___13) in
                                                    Success uu___12
                                                | err -> err)
                                           | Error err -> Error err) in
                                  uu___7 ctx01 in
                                (match uu___6 with
                                 | Success (y, g2) ->
                                     let uu___7 =
                                       let uu___8 = and_pre g11 g2 in
                                       (y, uu___8) in
                                     Success uu___7
                                 | err -> err)
                            | Error err -> Error err) in
                   uu___3 ctx0 in
                 (match uu___2 with
                  | Success (y, g2) ->
                      let uu___3 = let uu___4 = and_pre g1 g2 in (y, uu___4) in
                      Success uu___3
                  | err -> err)
             | Error err -> Error err)
      | FStarC_Syntax_Syntax.Tm_match uu___ ->
          fail "Match with effect returns ascription, or tactic handler"
      | uu___ ->
          let uu___1 =
            let uu___2 =
              FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term e1 in
            FStarC_Compiler_Util.format1 "Unexpected term: %s" uu___2 in
          fail uu___1
and (check_binders :
  env ->
    FStarC_Syntax_Syntax.binders ->
      FStarC_Syntax_Syntax.universe Prims.list result)
  =
  fun g_initial ->
    fun xs ->
      let rec aux g xs1 =
        match xs1 with
        | [] -> (fun uu___ -> Success ([], FStar_Pervasives_Native.None))
        | x::xs2 ->
            let uu___ =
              check "binder sort" g
                (x.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
            (fun ctx0 ->
               let uu___1 = uu___ ctx0 in
               match uu___1 with
               | Success (x1, g1) ->
                   let uu___2 =
                     let uu___3 =
                       match x1 with
                       | (uu___4, t) ->
                           let uu___5 = is_type g t in
                           (fun ctx01 ->
                              let uu___6 = uu___5 ctx01 in
                              match uu___6 with
                              | Success (x2, g11) ->
                                  let uu___7 =
                                    let uu___8 =
                                      let uu___9 =
                                        let uu___10 =
                                          let uu___11 = push_binder g x in
                                          aux uu___11 xs2 in
                                        fun ctx02 ->
                                          let uu___11 = uu___10 ctx02 in
                                          match uu___11 with
                                          | Success (x3, g12) ->
                                              let uu___12 =
                                                let uu___13 uu___14 =
                                                  Success
                                                    ((x2 :: x3),
                                                      FStar_Pervasives_Native.None) in
                                                uu___13 ctx02 in
                                              (match uu___12 with
                                               | Success (y, g2) ->
                                                   let uu___13 =
                                                     let uu___14 =
                                                       and_pre g12 g2 in
                                                     (y, uu___14) in
                                                   Success uu___13
                                               | err -> err)
                                          | Error err -> Error err in
                                      with_binders [x] [x2] uu___9 in
                                    uu___8 ctx01 in
                                  (match uu___7 with
                                   | Success (y, g2) ->
                                       let uu___8 =
                                         let uu___9 = and_pre g11 g2 in
                                         (y, uu___9) in
                                       Success uu___8
                                   | err -> err)
                              | Error err -> Error err) in
                     uu___3 ctx0 in
                   (match uu___2 with
                    | Success (y, g2) ->
                        let uu___3 =
                          let uu___4 = and_pre g1 g2 in (y, uu___4) in
                        Success uu___3
                    | err -> err)
               | Error err -> Error err) in
      aux g_initial xs
and (check_comp :
  env -> FStarC_Syntax_Syntax.comp -> FStarC_Syntax_Syntax.universe result) =
  fun g ->
    fun c ->
      match c.FStarC_Syntax_Syntax.n with
      | FStarC_Syntax_Syntax.Total t ->
          let uu___ =
            check "(G)Tot comp result" g (FStarC_Syntax_Util.comp_result c) in
          (fun ctx0 ->
             let uu___1 = uu___ ctx0 in
             match uu___1 with
             | Success (x, g1) ->
                 let uu___2 =
                   let uu___3 = match x with | (uu___4, t1) -> is_type g t1 in
                   uu___3 ctx0 in
                 (match uu___2 with
                  | Success (y, g2) ->
                      let uu___3 = let uu___4 = and_pre g1 g2 in (y, uu___4) in
                      Success uu___3
                  | err -> err)
             | Error err -> Error err)
      | FStarC_Syntax_Syntax.GTotal t ->
          let uu___ =
            check "(G)Tot comp result" g (FStarC_Syntax_Util.comp_result c) in
          (fun ctx0 ->
             let uu___1 = uu___ ctx0 in
             match uu___1 with
             | Success (x, g1) ->
                 let uu___2 =
                   let uu___3 = match x with | (uu___4, t1) -> is_type g t1 in
                   uu___3 ctx0 in
                 (match uu___2 with
                  | Success (y, g2) ->
                      let uu___3 = let uu___4 = and_pre g1 g2 in (y, uu___4) in
                      Success uu___3
                  | err -> err)
             | Error err -> Error err)
      | FStarC_Syntax_Syntax.Comp ct ->
          if
            (FStarC_Compiler_List.length ct.FStarC_Syntax_Syntax.comp_univs)
              <> Prims.int_one
          then fail "Unexpected/missing universe instantitation in comp"
          else
            (let u =
               FStarC_Compiler_List.hd ct.FStarC_Syntax_Syntax.comp_univs in
             let effect_app_tm =
               let head =
                 let uu___1 =
                   FStarC_Syntax_Syntax.fvar
                     ct.FStarC_Syntax_Syntax.effect_name
                     FStar_Pervasives_Native.None in
                 FStarC_Syntax_Syntax.mk_Tm_uinst uu___1 [u] in
               let uu___1 =
                 let uu___2 =
                   FStarC_Syntax_Syntax.as_arg
                     ct.FStarC_Syntax_Syntax.result_typ in
                 uu___2 :: (ct.FStarC_Syntax_Syntax.effect_args) in
               FStarC_Syntax_Syntax.mk_Tm_app head uu___1
                 (ct.FStarC_Syntax_Syntax.result_typ).FStarC_Syntax_Syntax.pos in
             let uu___1 = check "effectful comp" g effect_app_tm in
             fun ctx0 ->
               let uu___2 = uu___1 ctx0 in
               match uu___2 with
               | Success (x, g1) ->
                   let uu___3 =
                     let uu___4 =
                       match x with
                       | (uu___5, t) ->
                           let uu___6 ctx =
                             let ctx1 =
                               {
                                 no_guard = (ctx.no_guard);
                                 unfolding_ok = (ctx.unfolding_ok);
                                 error_context =
                                   (("comp fully applied",
                                      FStar_Pervasives_Native.None) ::
                                   (ctx.error_context))
                               } in
                             let uu___7 =
                               check_subtype g FStar_Pervasives_Native.None t
                                 FStarC_Syntax_Syntax.teff in
                             uu___7 ctx1 in
                           (fun ctx01 ->
                              let uu___7 = uu___6 ctx01 in
                              match uu___7 with
                              | Success (x1, g11) ->
                                  let uu___8 =
                                    let uu___9 =
                                      let c_lid =
                                        FStarC_TypeChecker_Env.norm_eff_name
                                          g.tcenv
                                          ct.FStarC_Syntax_Syntax.effect_name in
                                      let is_total =
                                        let uu___10 =
                                          FStarC_TypeChecker_Env.lookup_effect_quals
                                            g.tcenv c_lid in
                                        FStarC_Compiler_List.existsb
                                          (fun q ->
                                             q =
                                               FStarC_Syntax_Syntax.TotalEffect)
                                          uu___10 in
                                      if Prims.op_Negation is_total
                                      then
                                        fun uu___10 ->
                                          Success
                                            (FStarC_Syntax_Syntax.U_zero,
                                              FStar_Pervasives_Native.None)
                                      else
                                        (let uu___11 =
                                           FStarC_Syntax_Util.is_pure_or_ghost_effect
                                             c_lid in
                                         if uu___11
                                         then
                                           fun uu___12 ->
                                             Success
                                               (u,
                                                 FStar_Pervasives_Native.None)
                                         else
                                           (let uu___13 =
                                              FStarC_TypeChecker_Env.effect_repr
                                                g.tcenv c u in
                                            match uu___13 with
                                            | FStar_Pervasives_Native.None ->
                                                let uu___14 =
                                                  let uu___15 =
                                                    FStarC_Ident.string_of_lid
                                                      (FStarC_Syntax_Util.comp_effect_name
                                                         c) in
                                                  let uu___16 =
                                                    FStarC_Ident.string_of_lid
                                                      c_lid in
                                                  FStarC_Compiler_Util.format2
                                                    "Total effect %s (normalized to %s) does not have a representation"
                                                    uu___15 uu___16 in
                                                fail uu___14
                                            | FStar_Pervasives_Native.Some tm
                                                -> universe_of g tm)) in
                                    uu___9 ctx01 in
                                  (match uu___8 with
                                   | Success (y, g2) ->
                                       let uu___9 =
                                         let uu___10 = and_pre g11 g2 in
                                         (y, uu___10) in
                                       Success uu___9
                                   | err -> err)
                              | Error err -> Error err) in
                     uu___4 ctx0 in
                   (match uu___3 with
                    | Success (y, g2) ->
                        let uu___4 =
                          let uu___5 = and_pre g1 g2 in (y, uu___5) in
                        Success uu___4
                    | err -> err)
               | Error err -> Error err)
and (universe_of :
  env -> FStarC_Syntax_Syntax.typ -> FStarC_Syntax_Syntax.universe result) =
  fun g ->
    fun t ->
      let uu___ = check "universe of" g t in
      fun ctx0 ->
        let uu___1 = uu___ ctx0 in
        match uu___1 with
        | Success (x, g1) ->
            let uu___2 =
              let uu___3 = match x with | (uu___4, t1) -> is_type g t1 in
              uu___3 ctx0 in
            (match uu___2 with
             | Success (y, g2) ->
                 let uu___3 = let uu___4 = and_pre g1 g2 in (y, uu___4) in
                 Success uu___3
             | err -> err)
        | Error err -> Error err
and (check_pat :
  env ->
    FStarC_Syntax_Syntax.pat ->
      FStarC_Syntax_Syntax.typ ->
        (FStarC_Syntax_Syntax.binders * FStarC_Syntax_Syntax.universes)
          result)
  =
  fun g ->
    fun p ->
      fun t_sc ->
        let unrefine_tsc t_sc1 =
          let uu___ =
            FStarC_TypeChecker_Normalize.normalize_refinement
              FStarC_TypeChecker_Normalize.whnf_steps g.tcenv t_sc1 in
          FStarC_Syntax_Util.unrefine uu___ in
        match p.FStarC_Syntax_Syntax.v with
        | FStarC_Syntax_Syntax.Pat_constant c ->
            let e =
              match c with
              | FStarC_Const.Const_int
                  (repr, FStar_Pervasives_Native.Some sw) ->
                  FStarC_ToSyntax_ToSyntax.desugar_machine_integer
                    (g.tcenv).FStarC_TypeChecker_Env.dsenv repr sw
                    p.FStarC_Syntax_Syntax.p
              | uu___ ->
                  FStarC_Syntax_Syntax.mk
                    (FStarC_Syntax_Syntax.Tm_constant c)
                    p.FStarC_Syntax_Syntax.p in
            let uu___ = check "pat_const" g e in
            (fun ctx0 ->
               let uu___1 = uu___ ctx0 in
               match uu___1 with
               | Success (x, g1) ->
                   let uu___2 =
                     let uu___3 =
                       match x with
                       | (uu___4, t_const) ->
                           let uu___5 ctx =
                             let ctx1 =
                               {
                                 no_guard = (ctx.no_guard);
                                 unfolding_ok = (ctx.unfolding_ok);
                                 error_context =
                                   (("check_pat constant",
                                      FStar_Pervasives_Native.None) ::
                                   (ctx.error_context))
                               } in
                             let uu___6 =
                               let uu___7 = unrefine_tsc t_sc in
                               check_subtype g
                                 (FStar_Pervasives_Native.Some e) t_const
                                 uu___7 in
                             uu___6 ctx1 in
                           (fun ctx01 ->
                              let uu___6 = uu___5 ctx01 in
                              match uu___6 with
                              | Success (x1, g11) ->
                                  let uu___7 =
                                    let uu___8 uu___9 =
                                      Success
                                        (([], []),
                                          FStar_Pervasives_Native.None) in
                                    uu___8 ctx01 in
                                  (match uu___7 with
                                   | Success (y, g2) ->
                                       let uu___8 =
                                         let uu___9 = and_pre g11 g2 in
                                         (y, uu___9) in
                                       Success uu___8
                                   | err -> err)
                              | Error err -> Error err) in
                     uu___3 ctx0 in
                   (match uu___2 with
                    | Success (y, g2) ->
                        let uu___3 =
                          let uu___4 = and_pre g1 g2 in (y, uu___4) in
                        Success uu___3
                    | err -> err)
               | Error err -> Error err)
        | FStarC_Syntax_Syntax.Pat_var bv ->
            let b =
              FStarC_Syntax_Syntax.mk_binder
                {
                  FStarC_Syntax_Syntax.ppname =
                    (bv.FStarC_Syntax_Syntax.ppname);
                  FStarC_Syntax_Syntax.index =
                    (bv.FStarC_Syntax_Syntax.index);
                  FStarC_Syntax_Syntax.sort = t_sc
                } in
            let uu___ ctx =
              let ctx1 =
                {
                  no_guard = (ctx.no_guard);
                  unfolding_ok = (ctx.unfolding_ok);
                  error_context =
                    (("check_pat_binder", FStar_Pervasives_Native.None) ::
                    (ctx.error_context))
                } in
              let uu___1 = check_binders g [b] in uu___1 ctx1 in
            (fun ctx0 ->
               let uu___1 = uu___ ctx0 in
               match uu___1 with
               | Success (x, g1) ->
                   let uu___2 =
                     let uu___3 =
                       match x with
                       | u::[] ->
                           (fun uu___4 ->
                              Success
                                (([b], [u]), FStar_Pervasives_Native.None)) in
                     uu___3 ctx0 in
                   (match uu___2 with
                    | Success (y, g2) ->
                        let uu___3 =
                          let uu___4 = and_pre g1 g2 in (y, uu___4) in
                        Success uu___3
                    | err -> err)
               | Error err -> Error err)
        | FStarC_Syntax_Syntax.Pat_cons (fv, usopt, pats) ->
            let us =
              if FStarC_Compiler_Util.is_none usopt
              then []
              else FStarC_Compiler_Util.must usopt in
            let uu___ =
              let uu___1 =
                let uu___2 = FStarC_Syntax_Syntax.lid_of_fv fv in
                FStarC_TypeChecker_Env.lookup_and_inst_datacon g.tcenv us
                  uu___2 in
              FStarC_Syntax_Util.arrow_formals uu___1 in
            (match uu___ with
             | (formals, t_pat) ->
                 let uu___1 =
                   let pats1 =
                     FStarC_Compiler_List.map FStar_Pervasives_Native.fst
                       pats in
                   let uu___2 =
                     let uu___3 =
                       FStarC_Compiler_Util.prefix_until
                         (fun p1 ->
                            match p1.FStarC_Syntax_Syntax.v with
                            | FStarC_Syntax_Syntax.Pat_dot_term uu___4 ->
                                false
                            | uu___4 -> true) pats1 in
                     FStarC_Compiler_Util.map_option
                       (fun uu___4 ->
                          match uu___4 with
                          | (dot_pats, pat, rest_pats) ->
                              (dot_pats, (pat :: rest_pats))) uu___3 in
                   FStarC_Compiler_Util.dflt (pats1, []) uu___2 in
                 (match uu___1 with
                  | (dot_pats, rest_pats) ->
                      let uu___2 =
                        FStarC_Compiler_List.splitAt
                          (FStarC_Compiler_List.length dot_pats) formals in
                      (match uu___2 with
                       | (dot_formals, rest_formals) ->
                           let uu___3 =
                             fold2
                               (fun ss ->
                                  fun uu___4 ->
                                    fun p1 ->
                                      match uu___4 with
                                      | { FStarC_Syntax_Syntax.binder_bv = f;
                                          FStarC_Syntax_Syntax.binder_qual =
                                            uu___5;
                                          FStarC_Syntax_Syntax.binder_positivity
                                            = uu___6;
                                          FStarC_Syntax_Syntax.binder_attrs =
                                            uu___7;_}
                                          ->
                                          let expected_t =
                                            FStarC_Syntax_Subst.subst ss
                                              f.FStarC_Syntax_Syntax.sort in
                                          let uu___8 =
                                            match p1.FStarC_Syntax_Syntax.v
                                            with
                                            | FStarC_Syntax_Syntax.Pat_dot_term
                                                (FStar_Pervasives_Native.Some
                                                t) ->
                                                (fun uu___9 ->
                                                   Success
                                                     (t,
                                                       FStar_Pervasives_Native.None))
                                            | uu___9 ->
                                                fail
                                                  "check_pat in core has unset dot pattern" in
                                          (fun ctx0 ->
                                             let uu___9 = uu___8 ctx0 in
                                             match uu___9 with
                                             | Success (x, g1) ->
                                                 let uu___10 =
                                                   let uu___11 =
                                                     let uu___12 =
                                                       check "pat dot term" g
                                                         x in
                                                     fun ctx01 ->
                                                       let uu___13 =
                                                         uu___12 ctx01 in
                                                       match uu___13 with
                                                       | Success (x1, g11) ->
                                                           let uu___14 =
                                                             let uu___15 =
                                                               match x1 with
                                                               | (uu___16,
                                                                  p_t) ->
                                                                   let uu___17
                                                                    ctx =
                                                                    let ctx1
                                                                    =
                                                                    {
                                                                    no_guard
                                                                    =
                                                                    (ctx.no_guard);
                                                                    unfolding_ok
                                                                    =
                                                                    (ctx.unfolding_ok);
                                                                    error_context
                                                                    =
                                                                    (("check_pat cons",
                                                                    FStar_Pervasives_Native.None)
                                                                    ::
                                                                    (ctx.error_context))
                                                                    } in
                                                                    let uu___18
                                                                    =
                                                                    check_subtype
                                                                    g
                                                                    (FStar_Pervasives_Native.Some
                                                                    x) p_t
                                                                    expected_t in
                                                                    uu___18
                                                                    ctx1 in
                                                                   (fun ctx02
                                                                    ->
                                                                    let uu___18
                                                                    =
                                                                    uu___17
                                                                    ctx02 in
                                                                    match uu___18
                                                                    with
                                                                    | 
                                                                    Success
                                                                    (x2, g12)
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    let uu___20
                                                                    uu___21 =
                                                                    Success
                                                                    ((FStar_List_Tot_Base.op_At
                                                                    ss
                                                                    [
                                                                    FStarC_Syntax_Syntax.NT
                                                                    (f, x)]),
                                                                    FStar_Pervasives_Native.None) in
                                                                    uu___20
                                                                    ctx02 in
                                                                    (match uu___19
                                                                    with
                                                                    | 
                                                                    Success
                                                                    (y, g2)
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    and_pre
                                                                    g12 g2 in
                                                                    (y,
                                                                    uu___21) in
                                                                    Success
                                                                    uu___20
                                                                    | 
                                                                    err ->
                                                                    err)
                                                                    | 
                                                                    Error err
                                                                    ->
                                                                    Error err) in
                                                             uu___15 ctx01 in
                                                           (match uu___14
                                                            with
                                                            | Success 
                                                                (y, g2) ->
                                                                let uu___15 =
                                                                  let uu___16
                                                                    =
                                                                    and_pre
                                                                    g11 g2 in
                                                                  (y,
                                                                    uu___16) in
                                                                Success
                                                                  uu___15
                                                            | err -> err)
                                                       | Error err ->
                                                           Error err in
                                                   uu___11 ctx0 in
                                                 (match uu___10 with
                                                  | Success (y, g2) ->
                                                      let uu___11 =
                                                        let uu___12 =
                                                          and_pre g1 g2 in
                                                        (y, uu___12) in
                                                      Success uu___11
                                                  | err -> err)
                                             | Error err -> Error err)) []
                               dot_formals dot_pats in
                           (fun ctx0 ->
                              let uu___4 = uu___3 ctx0 in
                              match uu___4 with
                              | Success (x, g1) ->
                                  let uu___5 =
                                    let uu___6 =
                                      let uu___7 =
                                        fold2
                                          (fun uu___8 ->
                                             fun uu___9 ->
                                               fun p1 ->
                                                 match (uu___8, uu___9) with
                                                 | ((g2, ss, bs, us1),
                                                    {
                                                      FStarC_Syntax_Syntax.binder_bv
                                                        = f;
                                                      FStarC_Syntax_Syntax.binder_qual
                                                        = uu___10;
                                                      FStarC_Syntax_Syntax.binder_positivity
                                                        = uu___11;
                                                      FStarC_Syntax_Syntax.binder_attrs
                                                        = uu___12;_})
                                                     ->
                                                     let expected_t =
                                                       FStarC_Syntax_Subst.subst
                                                         ss
                                                         f.FStarC_Syntax_Syntax.sort in
                                                     let uu___13 =
                                                       let uu___14 =
                                                         check_pat g2 p1
                                                           expected_t in
                                                       with_binders bs us1
                                                         uu___14 in
                                                     (fun ctx01 ->
                                                        let uu___14 =
                                                          uu___13 ctx01 in
                                                        match uu___14 with
                                                        | Success (x1, g11)
                                                            ->
                                                            let uu___15 =
                                                              let uu___16 =
                                                                match x1 with
                                                                | (bs_p,
                                                                   us_p) ->
                                                                    let p_e =
                                                                    let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    FStarC_TypeChecker_PatternUtils.raw_pat_as_exp
                                                                    g2.tcenv
                                                                    p1 in
                                                                    FStarC_Compiler_Util.must
                                                                    uu___18 in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu___17 in
                                                                    let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    push_binders
                                                                    g2 bs_p in
                                                                    (uu___18,
                                                                    (FStar_List_Tot_Base.op_At
                                                                    ss
                                                                    [
                                                                    FStarC_Syntax_Syntax.NT
                                                                    (f, p_e)]),
                                                                    (FStar_List_Tot_Base.op_At
                                                                    bs bs_p),
                                                                    (FStar_List_Tot_Base.op_At
                                                                    us1 us_p)) in
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    Success
                                                                    (uu___17,
                                                                    FStar_Pervasives_Native.None)) in
                                                              uu___16 ctx01 in
                                                            (match uu___15
                                                             with
                                                             | Success
                                                                 (y, g21) ->
                                                                 let uu___16
                                                                   =
                                                                   let uu___17
                                                                    =
                                                                    and_pre
                                                                    g11 g21 in
                                                                   (y,
                                                                    uu___17) in
                                                                 Success
                                                                   uu___16
                                                             | err -> err)
                                                        | Error err ->
                                                            Error err))
                                          (g, x, [], []) rest_formals
                                          rest_pats in
                                      fun ctx01 ->
                                        let uu___8 = uu___7 ctx01 in
                                        match uu___8 with
                                        | Success (x1, g11) ->
                                            let uu___9 =
                                              let uu___10 =
                                                match x1 with
                                                | (uu___11, ss, bs, us1) ->
                                                    let t_pat1 =
                                                      FStarC_Syntax_Subst.subst
                                                        ss t_pat in
                                                    let uu___12 =
                                                      let uu___13 =
                                                        let uu___14 =
                                                          unrefine_tsc t_sc in
                                                        check_scrutinee_pattern_type_compatible
                                                          g uu___14 t_pat1 in
                                                      no_guard uu___13 in
                                                    (fun ctx02 ->
                                                       let uu___13 =
                                                         uu___12 ctx02 in
                                                       match uu___13 with
                                                       | Success (x2, g12) ->
                                                           let uu___14 =
                                                             let uu___15
                                                               uu___16 =
                                                               Success
                                                                 ((bs, us1),
                                                                   FStar_Pervasives_Native.None) in
                                                             uu___15 ctx02 in
                                                           (match uu___14
                                                            with
                                                            | Success 
                                                                (y, g2) ->
                                                                let uu___15 =
                                                                  let uu___16
                                                                    =
                                                                    and_pre
                                                                    g12 g2 in
                                                                  (y,
                                                                    uu___16) in
                                                                Success
                                                                  uu___15
                                                            | err -> err)
                                                       | Error err ->
                                                           Error err) in
                                              uu___10 ctx01 in
                                            (match uu___9 with
                                             | Success (y, g2) ->
                                                 let uu___10 =
                                                   let uu___11 =
                                                     and_pre g11 g2 in
                                                   (y, uu___11) in
                                                 Success uu___10
                                             | err -> err)
                                        | Error err -> Error err in
                                    uu___6 ctx0 in
                                  (match uu___5 with
                                   | Success (y, g2) ->
                                       let uu___6 =
                                         let uu___7 = and_pre g1 g2 in
                                         (y, uu___7) in
                                       Success uu___6
                                   | err -> err)
                              | Error err -> Error err))))
        | uu___ -> fail "check_pat called with a dot pattern"
and (check_scrutinee_pattern_type_compatible :
  env ->
    FStarC_Syntax_Syntax.typ ->
      FStarC_Syntax_Syntax.typ -> precondition result)
  =
  fun g ->
    fun t_sc ->
      fun t_pat ->
        let err s =
          let uu___ =
            let uu___1 =
              FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t_sc in
            let uu___2 =
              FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t_pat in
            FStarC_Compiler_Util.format3
              "Scrutinee type %s and Pattern type %s are not compatible because %s"
              uu___1 uu___2 s in
          fail uu___ in
        let uu___ = FStarC_Syntax_Util.head_and_args t_sc in
        match uu___ with
        | (head_sc, args_sc) ->
            let uu___1 = FStarC_Syntax_Util.head_and_args t_pat in
            (match uu___1 with
             | (head_pat, args_pat) ->
                 let uu___2 =
                   let uu___3 =
                     let uu___4 =
                       let uu___5 = FStarC_Syntax_Subst.compress head_sc in
                       uu___5.FStarC_Syntax_Syntax.n in
                     let uu___5 =
                       let uu___6 = FStarC_Syntax_Subst.compress head_pat in
                       uu___6.FStarC_Syntax_Syntax.n in
                     (uu___4, uu___5) in
                   match uu___3 with
                   | (FStarC_Syntax_Syntax.Tm_fvar fv_head,
                      FStarC_Syntax_Syntax.Tm_fvar fv_pat) when
                       let uu___4 = FStarC_Syntax_Syntax.lid_of_fv fv_head in
                       let uu___5 = FStarC_Syntax_Syntax.lid_of_fv fv_pat in
                       FStarC_Ident.lid_equals uu___4 uu___5 ->
                       (fun uu___4 ->
                          Success (fv_head, FStar_Pervasives_Native.None))
                   | (FStarC_Syntax_Syntax.Tm_uinst
                      ({
                         FStarC_Syntax_Syntax.n =
                           FStarC_Syntax_Syntax.Tm_fvar fv_head;
                         FStarC_Syntax_Syntax.pos = uu___4;
                         FStarC_Syntax_Syntax.vars = uu___5;
                         FStarC_Syntax_Syntax.hash_code = uu___6;_},
                       us_head),
                      FStarC_Syntax_Syntax.Tm_uinst
                      ({
                         FStarC_Syntax_Syntax.n =
                           FStarC_Syntax_Syntax.Tm_fvar fv_pat;
                         FStarC_Syntax_Syntax.pos = uu___7;
                         FStarC_Syntax_Syntax.vars = uu___8;
                         FStarC_Syntax_Syntax.hash_code = uu___9;_},
                       us_pat)) when
                       let uu___10 = FStarC_Syntax_Syntax.lid_of_fv fv_head in
                       let uu___11 = FStarC_Syntax_Syntax.lid_of_fv fv_pat in
                       FStarC_Ident.lid_equals uu___10 uu___11 ->
                       let uu___10 =
                         FStarC_TypeChecker_Rel.teq_nosmt_force g.tcenv
                           head_sc head_pat in
                       if uu___10
                       then
                         (fun uu___11 ->
                            Success (fv_head, FStar_Pervasives_Native.None))
                       else err "Incompatible universe instantiations"
                   | (uu___4, uu___5) ->
                       let uu___6 =
                         let uu___7 =
                           FStarC_Class_Tagged.tag_of
                             FStarC_Syntax_Syntax.tagged_term head_sc in
                         let uu___8 =
                           FStarC_Class_Tagged.tag_of
                             FStarC_Syntax_Syntax.tagged_term head_pat in
                         FStarC_Compiler_Util.format2
                           "Head constructors(%s and %s) not fvar" uu___7
                           uu___8 in
                       err uu___6 in
                 (fun ctx0 ->
                    let uu___3 = uu___2 ctx0 in
                    match uu___3 with
                    | Success (x, g1) ->
                        let uu___4 =
                          let uu___5 =
                            let uu___6 =
                              let uu___7 =
                                let uu___8 = FStarC_Syntax_Syntax.lid_of_fv x in
                                FStarC_TypeChecker_Env.is_type_constructor
                                  g.tcenv uu___8 in
                              if uu___7
                              then
                                fun uu___8 ->
                                  Success (x, FStar_Pervasives_Native.None)
                              else
                                (let uu___9 =
                                   let uu___10 =
                                     FStarC_Class_Show.show
                                       FStarC_Syntax_Print.showable_fv x in
                                   FStarC_Compiler_Util.format1
                                     "%s is not a type constructor" uu___10 in
                                 err uu___9) in
                            fun ctx01 ->
                              let uu___7 = uu___6 ctx01 in
                              match uu___7 with
                              | Success (x1, g11) ->
                                  let uu___8 =
                                    let uu___9 =
                                      let uu___10 =
                                        if
                                          (FStarC_Compiler_List.length
                                             args_sc)
                                            =
                                            (FStarC_Compiler_List.length
                                               args_pat)
                                        then
                                          fun uu___11 ->
                                            Success
                                              (x,
                                                FStar_Pervasives_Native.None)
                                        else
                                          (let uu___12 =
                                             let uu___13 =
                                               FStarC_Compiler_Util.string_of_int
                                                 (FStarC_Compiler_List.length
                                                    args_sc) in
                                             let uu___14 =
                                               FStarC_Compiler_Util.string_of_int
                                                 (FStarC_Compiler_List.length
                                                    args_pat) in
                                             FStarC_Compiler_Util.format2
                                               "Number of arguments don't match (%s and %s)"
                                               uu___13 uu___14 in
                                           err uu___12) in
                                      fun ctx02 ->
                                        let uu___11 = uu___10 ctx02 in
                                        match uu___11 with
                                        | Success (x2, g12) ->
                                            let uu___12 =
                                              let uu___13 =
                                                let uu___14 =
                                                  let uu___15 =
                                                    let uu___16 =
                                                      FStarC_Syntax_Syntax.lid_of_fv
                                                        x in
                                                    FStarC_TypeChecker_Env.num_inductive_ty_params
                                                      g.tcenv uu___16 in
                                                  match uu___15 with
                                                  | FStar_Pervasives_Native.None
                                                      -> (args_sc, args_pat)
                                                  | FStar_Pervasives_Native.Some
                                                      n ->
                                                      let uu___16 =
                                                        let uu___17 =
                                                          FStarC_Compiler_Util.first_N
                                                            n args_sc in
                                                        FStar_Pervasives_Native.fst
                                                          uu___17 in
                                                      let uu___17 =
                                                        let uu___18 =
                                                          FStarC_Compiler_Util.first_N
                                                            n args_pat in
                                                        FStar_Pervasives_Native.fst
                                                          uu___18 in
                                                      (uu___16, uu___17) in
                                                match uu___14 with
                                                | (params_sc, params_pat) ->
                                                    let uu___15 =
                                                      iter2 params_sc
                                                        params_pat
                                                        (fun uu___16 ->
                                                           fun uu___17 ->
                                                             fun uu___18 ->
                                                               match 
                                                                 (uu___16,
                                                                   uu___17)
                                                               with
                                                               | ((t_sc1,
                                                                   uu___19),
                                                                  (t_pat1,
                                                                   uu___20))
                                                                   ->
                                                                   check_relation
                                                                    g
                                                                    EQUALITY
                                                                    t_sc1
                                                                    t_pat1)
                                                        () in
                                                    (fun ctx03 ->
                                                       let uu___16 =
                                                         uu___15 ctx03 in
                                                       match uu___16 with
                                                       | Success (x3, g13) ->
                                                           let uu___17 =
                                                             let uu___18
                                                               uu___19 =
                                                               Success
                                                                 (FStar_Pervasives_Native.None,
                                                                   FStar_Pervasives_Native.None) in
                                                             uu___18 ctx03 in
                                                           (match uu___17
                                                            with
                                                            | Success 
                                                                (y, g2) ->
                                                                let uu___18 =
                                                                  let uu___19
                                                                    =
                                                                    and_pre
                                                                    g13 g2 in
                                                                  (y,
                                                                    uu___19) in
                                                                Success
                                                                  uu___18
                                                            | err1 -> err1)
                                                       | Error err1 ->
                                                           Error err1) in
                                              uu___13 ctx02 in
                                            (match uu___12 with
                                             | Success (y, g2) ->
                                                 let uu___13 =
                                                   let uu___14 =
                                                     and_pre g12 g2 in
                                                   (y, uu___14) in
                                                 Success uu___13
                                             | err1 -> err1)
                                        | Error err1 -> Error err1 in
                                    uu___9 ctx01 in
                                  (match uu___8 with
                                   | Success (y, g2) ->
                                       let uu___9 =
                                         let uu___10 = and_pre g11 g2 in
                                         (y, uu___10) in
                                       Success uu___9
                                   | err1 -> err1)
                              | Error err1 -> Error err1 in
                          uu___5 ctx0 in
                        (match uu___4 with
                         | Success (y, g2) ->
                             let uu___5 =
                               let uu___6 = and_pre g1 g2 in (y, uu___6) in
                             Success uu___5
                         | err1 -> err1)
                    | Error err1 -> Error err1))
and (pattern_branch_condition :
  env ->
    FStarC_Syntax_Syntax.term ->
      FStarC_Syntax_Syntax.pat ->
        FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option result)
  =
  fun g ->
    fun scrutinee ->
      fun pat ->
        match pat.FStarC_Syntax_Syntax.v with
        | FStarC_Syntax_Syntax.Pat_var uu___ ->
            (fun uu___1 ->
               Success
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None))
        | FStarC_Syntax_Syntax.Pat_constant c ->
            let const_exp =
              let uu___ =
                FStarC_TypeChecker_PatternUtils.raw_pat_as_exp g.tcenv pat in
              match uu___ with
              | FStar_Pervasives_Native.None -> failwith "Impossible"
              | FStar_Pervasives_Native.Some (e, uu___1) -> e in
            let uu___ = check "constant pattern" g const_exp in
            (fun ctx0 ->
               let uu___1 = uu___ ctx0 in
               match uu___1 with
               | Success (x, g1) ->
                   let uu___2 =
                     let uu___3 =
                       match x with
                       | (uu___4, t_const) ->
                           let uu___5 =
                             let uu___6 =
                               FStarC_Syntax_Util.mk_decidable_eq t_const
                                 scrutinee const_exp in
                             FStar_Pervasives_Native.Some uu___6 in
                           (fun uu___6 ->
                              Success (uu___5, FStar_Pervasives_Native.None)) in
                     uu___3 ctx0 in
                   (match uu___2 with
                    | Success (y, g2) ->
                        let uu___3 =
                          let uu___4 = and_pre g1 g2 in (y, uu___4) in
                        Success uu___3
                    | err -> err)
               | Error err -> Error err)
        | FStarC_Syntax_Syntax.Pat_cons (fv, us_opt, sub_pats) ->
            let wild_pat pos =
              let uu___ =
                let uu___1 =
                  FStarC_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    FStarC_Syntax_Syntax.tun in
                FStarC_Syntax_Syntax.Pat_var uu___1 in
              FStarC_Syntax_Syntax.withinfo uu___ pos in
            let mk_head_discriminator uu___ =
              let pat1 =
                let uu___1 =
                  let uu___2 =
                    let uu___3 =
                      FStarC_Compiler_List.map
                        (fun uu___4 ->
                           match uu___4 with
                           | (s, b) ->
                               let uu___5 = wild_pat s.FStarC_Syntax_Syntax.p in
                               (uu___5, b)) sub_pats in
                    (fv, us_opt, uu___3) in
                  FStarC_Syntax_Syntax.Pat_cons uu___2 in
                FStarC_Syntax_Syntax.withinfo uu___1
                  pat.FStarC_Syntax_Syntax.p in
              let branch1 =
                (pat1, FStar_Pervasives_Native.None,
                  FStarC_Syntax_Util.exp_true_bool) in
              let branch2 =
                let uu___1 =
                  let uu___2 =
                    let uu___3 =
                      FStarC_Syntax_Syntax.new_bv
                        FStar_Pervasives_Native.None FStarC_Syntax_Syntax.tun in
                    FStarC_Syntax_Syntax.Pat_var uu___3 in
                  FStarC_Syntax_Syntax.withinfo uu___2
                    pat1.FStarC_Syntax_Syntax.p in
                (uu___1, FStar_Pervasives_Native.None,
                  FStarC_Syntax_Util.exp_false_bool) in
              FStarC_Syntax_Syntax.mk
                (FStarC_Syntax_Syntax.Tm_match
                   {
                     FStarC_Syntax_Syntax.scrutinee = scrutinee;
                     FStarC_Syntax_Syntax.ret_opt =
                       FStar_Pervasives_Native.None;
                     FStarC_Syntax_Syntax.brs = [branch1; branch2];
                     FStarC_Syntax_Syntax.rc_opt1 =
                       FStar_Pervasives_Native.None
                   }) scrutinee.FStarC_Syntax_Syntax.pos in
            let mk_ith_projector i =
              let uu___ =
                let bv =
                  FStarC_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    FStarC_Syntax_Syntax.tun in
                let uu___1 =
                  FStarC_Syntax_Syntax.withinfo
                    (FStarC_Syntax_Syntax.Pat_var bv)
                    scrutinee.FStarC_Syntax_Syntax.pos in
                (bv, uu___1) in
              match uu___ with
              | (ith_pat_var, ith_pat) ->
                  let sub_pats1 =
                    FStarC_Compiler_List.mapi
                      (fun j ->
                         fun uu___1 ->
                           match uu___1 with
                           | (s, b) ->
                               if i <> j
                               then
                                 let uu___2 =
                                   wild_pat s.FStarC_Syntax_Syntax.p in
                                 (uu___2, b)
                               else (ith_pat, b)) sub_pats in
                  let pat1 =
                    FStarC_Syntax_Syntax.withinfo
                      (FStarC_Syntax_Syntax.Pat_cons (fv, us_opt, sub_pats1))
                      pat.FStarC_Syntax_Syntax.p in
                  let branch = FStarC_Syntax_Syntax.bv_to_name ith_pat_var in
                  let eqn =
                    FStarC_Syntax_Subst.close_branch
                      (pat1, FStar_Pervasives_Native.None, branch) in
                  FStarC_Syntax_Syntax.mk
                    (FStarC_Syntax_Syntax.Tm_match
                       {
                         FStarC_Syntax_Syntax.scrutinee = scrutinee;
                         FStarC_Syntax_Syntax.ret_opt =
                           FStar_Pervasives_Native.None;
                         FStarC_Syntax_Syntax.brs = [eqn];
                         FStarC_Syntax_Syntax.rc_opt1 =
                           FStar_Pervasives_Native.None
                       }) scrutinee.FStarC_Syntax_Syntax.pos in
            let discrimination =
              let uu___ =
                let uu___1 =
                  FStarC_TypeChecker_Env.typ_of_datacon g.tcenv
                    (fv.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v in
                FStarC_TypeChecker_Env.datacons_of_typ g.tcenv uu___1 in
              match uu___ with
              | (is_induc, datacons) ->
                  if
                    (Prims.op_Negation is_induc) ||
                      ((FStarC_Compiler_List.length datacons) > Prims.int_one)
                  then
                    let discriminator =
                      FStarC_Syntax_Util.mk_discriminator
                        (fv.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v in
                    let uu___1 =
                      FStarC_TypeChecker_Env.try_lookup_lid g.tcenv
                        discriminator in
                    (match uu___1 with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | uu___2 ->
                         let uu___3 = mk_head_discriminator () in
                         FStar_Pervasives_Native.Some uu___3)
                  else FStar_Pervasives_Native.None in
            let uu___ =
              mapi
                (fun i ->
                   fun uu___1 ->
                     match uu___1 with
                     | (pi, uu___2) ->
                         (match pi.FStarC_Syntax_Syntax.v with
                          | FStarC_Syntax_Syntax.Pat_dot_term uu___3 ->
                              (fun uu___4 ->
                                 Success
                                   (FStar_Pervasives_Native.None,
                                     FStar_Pervasives_Native.None))
                          | FStarC_Syntax_Syntax.Pat_var uu___3 ->
                              (fun uu___4 ->
                                 Success
                                   (FStar_Pervasives_Native.None,
                                     FStar_Pervasives_Native.None))
                          | uu___3 ->
                              let scrutinee_sub_term = mk_ith_projector i in
                              let uu___4 = mk_ith_projector i in
                              pattern_branch_condition g uu___4 pi)) sub_pats in
            (fun ctx0 ->
               let uu___1 = uu___ ctx0 in
               match uu___1 with
               | Success (x, g1) ->
                   let uu___2 =
                     let uu___3 =
                       let guards =
                         FStarC_Compiler_List.collect
                           (fun uu___4 ->
                              match uu___4 with
                              | FStar_Pervasives_Native.None -> []
                              | FStar_Pervasives_Native.Some t -> [t])
                           (discrimination :: x) in
                       match guards with
                       | [] ->
                           (fun uu___4 ->
                              Success
                                (FStar_Pervasives_Native.None,
                                  FStar_Pervasives_Native.None))
                       | guards1 ->
                           let uu___4 =
                             let uu___5 = FStarC_Syntax_Util.mk_and_l guards1 in
                             FStar_Pervasives_Native.Some uu___5 in
                           (fun uu___5 ->
                              Success (uu___4, FStar_Pervasives_Native.None)) in
                     uu___3 ctx0 in
                   (match uu___2 with
                    | Success (y, g2) ->
                        let uu___3 =
                          let uu___4 = and_pre g1 g2 in (y, uu___4) in
                        Success uu___3
                    | err -> err)
               | Error err -> Error err)
let (initial_env :
  FStarC_TypeChecker_Env.env ->
    guard_handler_t FStar_Pervasives_Native.option -> env)
  =
  fun g ->
    fun gh ->
      let max_index =
        FStarC_Compiler_List.fold_left
          (fun index ->
             fun b ->
               match b with
               | FStarC_Syntax_Syntax.Binding_var x ->
                   if x.FStarC_Syntax_Syntax.index > index
                   then x.FStarC_Syntax_Syntax.index
                   else index
               | uu___ -> index) Prims.int_zero
          g.FStarC_TypeChecker_Env.gamma in
      {
        tcenv = g;
        allow_universe_instantiation = false;
        max_binder_index = max_index;
        guard_handler = gh;
        should_read_cache = true
      }
let (check_term_top :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.term ->
      FStarC_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
        Prims.bool ->
          guard_handler_t FStar_Pervasives_Native.option ->
            (tot_or_ghost * FStarC_Syntax_Syntax.typ) result)
  =
  fun g ->
    fun e ->
      fun topt ->
        fun must_tot ->
          fun gh ->
            let g1 = initial_env g gh in
            let uu___ = check "top" g1 e in
            fun ctx0 ->
              let uu___1 = uu___ ctx0 in
              match uu___1 with
              | Success (x, g11) ->
                  let uu___2 =
                    let uu___3 =
                      match topt with
                      | FStar_Pervasives_Native.None ->
                          if must_tot
                          then
                            let uu___4 = x in
                            (match uu___4 with
                             | (eff, t) ->
                                 let uu___5 =
                                   (eff = E_Ghost) &&
                                     (let uu___6 = non_informative g1 t in
                                      Prims.op_Negation uu___6) in
                                 if uu___5
                                 then
                                   fail "expected total effect, found ghost"
                                 else
                                   (fun uu___7 ->
                                      Success
                                        ((E_Total, t),
                                          FStar_Pervasives_Native.None)))
                          else
                            (fun uu___5 ->
                               Success (x, FStar_Pervasives_Native.None))
                      | FStar_Pervasives_Native.Some t ->
                          let uu___4 =
                            if
                              must_tot ||
                                ((FStar_Pervasives_Native.fst x) = E_Total)
                            then
                              let uu___5 = FStarC_Syntax_Syntax.mk_Total t in
                              (uu___5, E_Total)
                            else
                              (let uu___6 = FStarC_Syntax_Syntax.mk_GTotal t in
                               (uu___6, E_Ghost)) in
                          (match uu___4 with
                           | (target_comp, eff) ->
                               let uu___5 ctx =
                                 let ctx1 =
                                   {
                                     no_guard = (ctx.no_guard);
                                     unfolding_ok = (ctx.unfolding_ok);
                                     error_context =
                                       (("top-level subtyping",
                                          FStar_Pervasives_Native.None) ::
                                       (ctx.error_context))
                                   } in
                                 let uu___6 =
                                   let uu___7 = as_comp g1 x in
                                   check_relation_comp
                                     {
                                       tcenv = (g1.tcenv);
                                       allow_universe_instantiation = true;
                                       max_binder_index =
                                         (g1.max_binder_index);
                                       guard_handler = (g1.guard_handler);
                                       should_read_cache =
                                         (g1.should_read_cache)
                                     }
                                     (SUBTYPING
                                        (FStar_Pervasives_Native.Some e))
                                     uu___7 target_comp in
                                 uu___6 ctx1 in
                               (fun ctx01 ->
                                  let uu___6 = uu___5 ctx01 in
                                  match uu___6 with
                                  | Success (x1, g12) ->
                                      let uu___7 =
                                        let uu___8 uu___9 =
                                          Success
                                            ((eff, t),
                                              FStar_Pervasives_Native.None) in
                                        uu___8 ctx01 in
                                      (match uu___7 with
                                       | Success (y, g2) ->
                                           let uu___8 =
                                             let uu___9 = and_pre g12 g2 in
                                             (y, uu___9) in
                                           Success uu___8
                                       | err -> err)
                                  | Error err -> Error err)) in
                    uu___3 ctx0 in
                  (match uu___2 with
                   | Success (y, g2) ->
                       let uu___3 =
                         let uu___4 = and_pre g11 g2 in (y, uu___4) in
                       Success uu___3
                   | err -> err)
              | Error err -> Error err
let (simplify_steps : FStarC_TypeChecker_Env.step Prims.list) =
  [FStarC_TypeChecker_Env.Beta;
  FStarC_TypeChecker_Env.UnfoldUntil FStarC_Syntax_Syntax.delta_constant;
  FStarC_TypeChecker_Env.UnfoldQual ["unfold"];
  FStarC_TypeChecker_Env.UnfoldOnly
    [FStarC_Parser_Const.pure_wp_monotonic_lid;
    FStarC_Parser_Const.pure_wp_monotonic0_lid];
  FStarC_TypeChecker_Env.Simplify;
  FStarC_TypeChecker_Env.Primops;
  FStarC_TypeChecker_Env.NoFullNorm]
let (check_term_top_gh :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.term ->
      FStarC_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
        Prims.bool ->
          guard_handler_t FStar_Pervasives_Native.option ->
            ((tot_or_ghost * FStarC_Syntax_Syntax.typ) * precondition)
              __result)
  =
  fun g ->
    fun e ->
      fun topt ->
        fun must_tot ->
          fun gh ->
            (let uu___1 = FStarC_Compiler_Effect.op_Bang dbg_Eq in
             if uu___1
             then
               let uu___2 =
                 let uu___3 = get_goal_ctr () in
                 FStarC_Class_Show.show FStarC_Class_Show.showable_int uu___3 in
               FStarC_Compiler_Util.print1 "(%s) Entering core ... \n" uu___2
             else ());
            (let uu___2 =
               (FStarC_Compiler_Effect.op_Bang dbg) ||
                 (FStarC_Compiler_Effect.op_Bang dbg_Top) in
             if uu___2
             then
               let uu___3 =
                 let uu___4 = get_goal_ctr () in
                 FStarC_Class_Show.show FStarC_Class_Show.showable_int uu___4 in
               let uu___4 =
                 FStarC_Class_Show.show FStarC_Syntax_Print.showable_term e in
               let uu___5 =
                 FStarC_Class_Show.show
                   (FStarC_Class_Show.show_option
                      FStarC_Syntax_Print.showable_term) topt in
               FStarC_Compiler_Util.print3
                 "(%s) Entering core with %s <: %s\n" uu___3 uu___4 uu___5
             else ());
            FStarC_Syntax_TermHashTable.reset_counters table;
            reset_cache_stats ();
            (let ctx =
               {
                 no_guard = false;
                 unfolding_ok = true;
                 error_context = [("Top", FStar_Pervasives_Native.None)]
               } in
             let res =
               FStarC_Profiling.profile
                 (fun uu___4 ->
                    let uu___5 =
                      let uu___6 = check_term_top g e topt must_tot gh in
                      uu___6 ctx in
                    match uu___5 with
                    | Success (et, g1) -> Success (et, g1)
                    | Error err -> Error err) FStar_Pervasives_Native.None
                 "FStarC.TypeChecker.Core.check_term_top" in
             let res1 =
               match res with
               | Success (et, FStar_Pervasives_Native.Some guard0) ->
                   let guard1 =
                     FStarC_TypeChecker_Normalize.normalize simplify_steps g
                       guard0 in
                   ((let uu___5 =
                       ((FStarC_Compiler_Effect.op_Bang dbg) ||
                          (FStarC_Compiler_Effect.op_Bang dbg_Top))
                         || (FStarC_Compiler_Effect.op_Bang dbg_Exit) in
                     if uu___5
                     then
                       ((let uu___7 =
                           let uu___8 = get_goal_ctr () in
                           FStarC_Compiler_Util.string_of_int uu___8 in
                         let uu___8 =
                           FStarC_Class_Show.show
                             FStarC_Syntax_Print.showable_term guard0 in
                         let uu___9 =
                           FStarC_Class_Show.show
                             FStarC_Syntax_Print.showable_term guard1 in
                         FStarC_Compiler_Util.print3
                           "(%s) Exiting core: Simplified guard from {{%s}} to {{%s}}\n"
                           uu___7 uu___8 uu___9);
                        (let guard_names =
                           let uu___7 = FStarC_Syntax_Free.names guard1 in
                           FStarC_Class_Setlike.elems ()
                             (Obj.magic
                                (FStarC_Compiler_FlatSet.setlike_flat_set
                                   FStarC_Syntax_Syntax.ord_bv))
                             (Obj.magic uu___7) in
                         let uu___7 =
                           FStarC_Compiler_List.tryFind
                             (fun bv ->
                                FStarC_Compiler_List.for_all
                                  (fun binding_env ->
                                     match binding_env with
                                     | FStarC_Syntax_Syntax.Binding_var
                                         bv_env ->
                                         let uu___8 =
                                           FStarC_Syntax_Syntax.bv_eq bv_env
                                             bv in
                                         Prims.op_Negation uu___8
                                     | uu___8 -> true)
                                  g.FStarC_TypeChecker_Env.gamma) guard_names in
                         match uu___7 with
                         | FStar_Pervasives_Native.Some bv ->
                             let uu___8 =
                               let uu___9 =
                                 FStarC_Syntax_Syntax.bv_to_name bv in
                               FStarC_Class_Show.show
                                 FStarC_Syntax_Print.showable_term uu___9 in
                             FStarC_Compiler_Util.print1
                               "WARNING: %s is free in the core generated guard\n"
                               uu___8
                         | uu___8 -> ()))
                     else ());
                    Success (et, (FStar_Pervasives_Native.Some guard1)))
               | Success uu___4 ->
                   ((let uu___6 =
                       (FStarC_Compiler_Effect.op_Bang dbg) ||
                         (FStarC_Compiler_Effect.op_Bang dbg_Top) in
                     if uu___6
                     then
                       let uu___7 =
                         let uu___8 = get_goal_ctr () in
                         FStarC_Compiler_Util.string_of_int uu___8 in
                       FStarC_Compiler_Util.print1 "(%s) Exiting core (ok)\n"
                         uu___7
                     else ());
                    res)
               | Error uu___4 ->
                   ((let uu___6 =
                       (FStarC_Compiler_Effect.op_Bang dbg) ||
                         (FStarC_Compiler_Effect.op_Bang dbg_Top) in
                     if uu___6
                     then
                       let uu___7 =
                         let uu___8 = get_goal_ctr () in
                         FStarC_Compiler_Util.string_of_int uu___8 in
                       FStarC_Compiler_Util.print1
                         "(%s) Exiting core (failed)\n" uu___7
                     else ());
                    res) in
             (let uu___5 = FStarC_Compiler_Effect.op_Bang dbg_Eq in
              if uu___5
              then
                (FStarC_Syntax_TermHashTable.print_stats table;
                 (let cs = report_cache_stats () in
                  let uu___7 = FStarC_Compiler_Util.string_of_int cs.hits in
                  let uu___8 = FStarC_Compiler_Util.string_of_int cs.misses in
                  FStarC_Compiler_Util.print2
                    "Cache_stats { hits = %s; misses = %s }\n" uu___7 uu___8))
              else ());
             res1)
let (check_term :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.term ->
      FStarC_Syntax_Syntax.typ ->
        Prims.bool ->
          (FStarC_Syntax_Syntax.typ FStar_Pervasives_Native.option, error)
            FStar_Pervasives.either)
  =
  fun g ->
    fun e ->
      fun t ->
        fun must_tot ->
          let uu___ =
            check_term_top_gh g e (FStar_Pervasives_Native.Some t) must_tot
              FStar_Pervasives_Native.None in
          match uu___ with
          | Success (uu___1, g1) -> FStar_Pervasives.Inl g1
          | Error err -> FStar_Pervasives.Inr err
let (check_term_at_type :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.term ->
      FStarC_Syntax_Syntax.typ ->
        ((tot_or_ghost * FStarC_Syntax_Syntax.typ
           FStar_Pervasives_Native.option),
          error) FStar_Pervasives.either)
  =
  fun g ->
    fun e ->
      fun t ->
        let must_tot = false in
        let uu___ =
          check_term_top_gh g e (FStar_Pervasives_Native.Some t) must_tot
            FStar_Pervasives_Native.None in
        match uu___ with
        | Success ((eff, uu___1), g1) -> FStar_Pervasives.Inl (eff, g1)
        | Error err -> FStar_Pervasives.Inr err
let (compute_term_type_handle_guards :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.term ->
      (FStarC_TypeChecker_Env.env -> FStarC_Syntax_Syntax.typ -> Prims.bool)
        ->
        ((tot_or_ghost * FStarC_Syntax_Syntax.typ), error)
          FStar_Pervasives.either)
  =
  fun g ->
    fun e ->
      fun gh ->
        let e1 = FStarC_Syntax_Compress.deep_compress true true e in
        let must_tot = false in
        let uu___ =
          check_term_top_gh g e1 FStar_Pervasives_Native.None must_tot
            (FStar_Pervasives_Native.Some gh) in
        match uu___ with
        | Success (r, FStar_Pervasives_Native.None) -> FStar_Pervasives.Inl r
        | Success (uu___1, FStar_Pervasives_Native.Some uu___2) ->
            failwith
              "Impossible: All guards should have been handled already"
        | Error err -> FStar_Pervasives.Inr err
let (open_binders_in_term :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.binders ->
      FStarC_Syntax_Syntax.term ->
        (FStarC_TypeChecker_Env.env * FStarC_Syntax_Syntax.binders *
          FStarC_Syntax_Syntax.term))
  =
  fun env1 ->
    fun bs ->
      fun t ->
        let g = initial_env env1 FStar_Pervasives_Native.None in
        let uu___ = open_term_binders g bs t in
        match uu___ with | (g', bs1, t1) -> ((g'.tcenv), bs1, t1)
let (open_binders_in_comp :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.binders ->
      FStarC_Syntax_Syntax.comp ->
        (FStarC_TypeChecker_Env.env * FStarC_Syntax_Syntax.binders *
          FStarC_Syntax_Syntax.comp))
  =
  fun env1 ->
    fun bs ->
      fun c ->
        let g = initial_env env1 FStar_Pervasives_Native.None in
        let uu___ = open_comp_binders g bs c in
        match uu___ with | (g', bs1, c1) -> ((g'.tcenv), bs1, c1)
let (check_term_equality :
  Prims.bool ->
    Prims.bool ->
      FStarC_TypeChecker_Env.env ->
        FStarC_Syntax_Syntax.typ ->
          FStarC_Syntax_Syntax.typ ->
            (FStarC_Syntax_Syntax.typ FStar_Pervasives_Native.option, 
              error) FStar_Pervasives.either)
  =
  fun guard_ok ->
    fun unfolding_ok1 ->
      fun g ->
        fun t0 ->
          fun t1 ->
            let g1 = initial_env g FStar_Pervasives_Native.None in
            (let uu___1 = FStarC_Compiler_Effect.op_Bang dbg_Top in
             if uu___1
             then
               let uu___2 =
                 FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t0 in
               let uu___3 =
                 FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t1 in
               let uu___4 =
                 FStarC_Class_Show.show FStarC_Class_Show.showable_bool
                   guard_ok in
               let uu___5 =
                 FStarC_Class_Show.show FStarC_Class_Show.showable_bool
                   unfolding_ok1 in
               FStarC_Compiler_Util.print4
                 "Entering check_term_equality with %s and %s (guard_ok=%s; unfolding_ok=%s) {\n"
                 uu___2 uu___3 uu___4 uu___5
             else ());
            (let ctx =
               {
                 no_guard = (Prims.op_Negation guard_ok);
                 unfolding_ok = unfolding_ok1;
                 error_context = [("Eq", FStar_Pervasives_Native.None)]
               } in
             let r =
               let uu___1 = check_relation g1 EQUALITY t0 t1 in uu___1 ctx in
             (let uu___2 = FStarC_Compiler_Effect.op_Bang dbg_Top in
              if uu___2
              then
                let uu___3 =
                  FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t0 in
                let uu___4 =
                  FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t1 in
                let uu___5 =
                  FStarC_Class_Show.show
                    (showable_result
                       (FStarC_Class_Show.show_tuple2
                          FStarC_Class_Show.showable_unit
                          (FStarC_Class_Show.show_option
                             FStarC_Syntax_Print.showable_term))) r in
                FStarC_Compiler_Util.print3
                  "} Exiting check_term_equality (%s, %s). Result = %s.\n"
                  uu___3 uu___4 uu___5
              else ());
             (let r1 =
                match r with
                | Success (uu___2, g2) -> FStar_Pervasives.Inl g2
                | Error err -> FStar_Pervasives.Inr err in
              r1))
let (check_term_subtyping :
  Prims.bool ->
    Prims.bool ->
      FStarC_TypeChecker_Env.env ->
        FStarC_Syntax_Syntax.typ ->
          FStarC_Syntax_Syntax.typ ->
            (FStarC_Syntax_Syntax.typ FStar_Pervasives_Native.option, 
              error) FStar_Pervasives.either)
  =
  fun guard_ok ->
    fun unfolding_ok1 ->
      fun g ->
        fun t0 ->
          fun t1 ->
            let g1 = initial_env g FStar_Pervasives_Native.None in
            let ctx =
              {
                no_guard = (Prims.op_Negation guard_ok);
                unfolding_ok = unfolding_ok1;
                error_context = [("Subtyping", FStar_Pervasives_Native.None)]
              } in
            let uu___ =
              let uu___1 =
                check_relation g1 (SUBTYPING FStar_Pervasives_Native.None) t0
                  t1 in
              uu___1 ctx in
            match uu___ with
            | Success (uu___1, g2) -> FStar_Pervasives.Inl g2
            | Error err -> FStar_Pervasives.Inr err