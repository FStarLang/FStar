open Prims
let (goal_ctr : Prims.int FStar_Compiler_Effect.ref) =
  FStar_Compiler_Util.mk_ref Prims.int_zero
let (get_goal_ctr : unit -> Prims.int) =
  fun uu___ -> FStar_Compiler_Effect.op_Bang goal_ctr
let (incr_goal_ctr : unit -> Prims.int) =
  fun uu___ ->
    let v = FStar_Compiler_Effect.op_Bang goal_ctr in
    FStar_Compiler_Effect.op_Colon_Equals goal_ctr (v + Prims.int_one);
    v + Prims.int_one
type guard_handler_t =
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool
type env =
  {
  tcenv: FStar_TypeChecker_Env.env ;
  allow_universe_instantiation: Prims.bool ;
  max_binder_index: Prims.int ;
  guard_handler: guard_handler_t FStar_Pervasives_Native.option ;
  should_read_cache: Prims.bool }
let (__proj__Mkenv__item__tcenv : env -> FStar_TypeChecker_Env.env) =
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
let (push_binder : env -> FStar_Syntax_Syntax.binder -> env) =
  fun g ->
    fun b ->
      if
        (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.index <=
          g.max_binder_index
      then
        failwith
          "Assertion failed: unexpected shadowing in the core environment"
      else
        (let uu___1 = FStar_TypeChecker_Env.push_binders g.tcenv [b] in
         {
           tcenv = uu___1;
           allow_universe_instantiation = (g.allow_universe_instantiation);
           max_binder_index =
             ((b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.index);
           guard_handler = (g.guard_handler);
           should_read_cache = (g.should_read_cache)
         })
let (fresh_binder :
  env -> FStar_Syntax_Syntax.binder -> (env * FStar_Syntax_Syntax.binder)) =
  fun g ->
    fun old ->
      let ctr = g.max_binder_index + Prims.int_one in
      let bv =
        let uu___ = old.FStar_Syntax_Syntax.binder_bv in
        {
          FStar_Syntax_Syntax.ppname = (uu___.FStar_Syntax_Syntax.ppname);
          FStar_Syntax_Syntax.index = ctr;
          FStar_Syntax_Syntax.sort = (uu___.FStar_Syntax_Syntax.sort)
        } in
      let b =
        FStar_Syntax_Syntax.mk_binder_with_attrs bv
          old.FStar_Syntax_Syntax.binder_qual
          old.FStar_Syntax_Syntax.binder_attrs in
      let uu___ = push_binder g b in (uu___, b)
let (open_binders :
  env ->
    FStar_Syntax_Syntax.binders ->
      (env * FStar_Syntax_Syntax.binder Prims.list *
        FStar_Syntax_Syntax.subst_elt Prims.list))
  =
  fun g ->
    fun bs ->
      let uu___ =
        FStar_Compiler_List.fold_left
          (fun uu___1 ->
             fun b ->
               match uu___1 with
               | (g1, bs1, subst) ->
                   let bv =
                     let uu___2 = b.FStar_Syntax_Syntax.binder_bv in
                     let uu___3 =
                       FStar_Syntax_Subst.subst subst
                         (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___2.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___2.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu___3
                     } in
                   let b1 =
                     let uu___2 =
                       FStar_Syntax_Subst.subst_bqual subst
                         b.FStar_Syntax_Syntax.binder_qual in
                     let uu___3 =
                       FStar_Compiler_List.map
                         (FStar_Syntax_Subst.subst subst)
                         b.FStar_Syntax_Syntax.binder_attrs in
                     {
                       FStar_Syntax_Syntax.binder_bv = bv;
                       FStar_Syntax_Syntax.binder_qual = uu___2;
                       FStar_Syntax_Syntax.binder_attrs = uu___3
                     } in
                   let uu___2 = fresh_binder g1 b1 in
                   (match uu___2 with
                    | (g2, b') ->
                        let uu___3 =
                          let uu___4 =
                            FStar_Syntax_Subst.shift_subst Prims.int_one
                              subst in
                          (FStar_Syntax_Syntax.DB
                             (Prims.int_zero,
                               (b'.FStar_Syntax_Syntax.binder_bv)))
                            :: uu___4 in
                        (g2, (b' :: bs1), uu___3))) (g, [], []) bs in
      match uu___ with
      | (g1, bs_rev, subst) -> (g1, (FStar_Compiler_List.rev bs_rev), subst)
let (open_pat :
  env ->
    FStar_Syntax_Syntax.pat ->
      (env * FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t))
  =
  fun g ->
    fun p ->
      let rec open_pat_aux g1 p1 sub =
        match p1.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_constant uu___ -> (g1, p1, sub)
        | FStar_Syntax_Syntax.Pat_cons (fv, us_opt, pats) ->
            let uu___ =
              FStar_Compiler_List.fold_left
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
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_cons
                          (fv, us_opt, (FStar_Compiler_List.rev pats1)));
                     FStar_Syntax_Syntax.p = (p1.FStar_Syntax_Syntax.p)
                   }, sub1))
        | FStar_Syntax_Syntax.Pat_var x ->
            let bx =
              let uu___ =
                let uu___1 =
                  FStar_Syntax_Subst.subst sub x.FStar_Syntax_Syntax.sort in
                {
                  FStar_Syntax_Syntax.ppname = (x.FStar_Syntax_Syntax.ppname);
                  FStar_Syntax_Syntax.index = (x.FStar_Syntax_Syntax.index);
                  FStar_Syntax_Syntax.sort = uu___1
                } in
              FStar_Syntax_Syntax.mk_binder uu___ in
            let uu___ = fresh_binder g1 bx in
            (match uu___ with
             | (g2, bx') ->
                 let sub1 =
                   let uu___1 =
                     FStar_Syntax_Subst.shift_subst Prims.int_one sub in
                   (FStar_Syntax_Syntax.DB
                      (Prims.int_zero, (bx'.FStar_Syntax_Syntax.binder_bv)))
                     :: uu___1 in
                 (g2,
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_var
                          (bx'.FStar_Syntax_Syntax.binder_bv));
                     FStar_Syntax_Syntax.p = (p1.FStar_Syntax_Syntax.p)
                   }, sub1))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let bx =
              let uu___ =
                let uu___1 =
                  FStar_Syntax_Subst.subst sub x.FStar_Syntax_Syntax.sort in
                {
                  FStar_Syntax_Syntax.ppname = (x.FStar_Syntax_Syntax.ppname);
                  FStar_Syntax_Syntax.index = (x.FStar_Syntax_Syntax.index);
                  FStar_Syntax_Syntax.sort = uu___1
                } in
              FStar_Syntax_Syntax.mk_binder uu___ in
            let uu___ = fresh_binder g1 bx in
            (match uu___ with
             | (g2, bx') ->
                 let sub1 =
                   let uu___1 =
                     FStar_Syntax_Subst.shift_subst Prims.int_one sub in
                   (FStar_Syntax_Syntax.DB
                      (Prims.int_zero, (bx'.FStar_Syntax_Syntax.binder_bv)))
                     :: uu___1 in
                 (g2,
                   {
                     FStar_Syntax_Syntax.v =
                       (FStar_Syntax_Syntax.Pat_wild
                          (bx'.FStar_Syntax_Syntax.binder_bv));
                     FStar_Syntax_Syntax.p = (p1.FStar_Syntax_Syntax.p)
                   }, sub1))
        | FStar_Syntax_Syntax.Pat_dot_term eopt ->
            let eopt1 =
              FStar_Compiler_Util.map_option (FStar_Syntax_Subst.subst sub)
                eopt in
            (g1,
              {
                FStar_Syntax_Syntax.v =
                  (FStar_Syntax_Syntax.Pat_dot_term eopt1);
                FStar_Syntax_Syntax.p = (p1.FStar_Syntax_Syntax.p)
              }, sub) in
      open_pat_aux g p []
let (open_term :
  env ->
    FStar_Syntax_Syntax.binder ->
      FStar_Syntax_Syntax.term ->
        (env * FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.term))
  =
  fun g ->
    fun b ->
      fun t ->
        let uu___ = fresh_binder g b in
        match uu___ with
        | (g1, b') ->
            let t1 =
              FStar_Syntax_Subst.subst
                [FStar_Syntax_Syntax.DB
                   (Prims.int_zero, (b'.FStar_Syntax_Syntax.binder_bv))] t in
            (g1, b', t1)
let (open_term_binders :
  env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term ->
        (env * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term))
  =
  fun g ->
    fun bs ->
      fun t ->
        let uu___ = open_binders g bs in
        match uu___ with
        | (g1, bs1, subst) ->
            let uu___1 = FStar_Syntax_Subst.subst subst t in
            (g1, bs1, uu___1)
let (open_comp :
  env ->
    FStar_Syntax_Syntax.binder ->
      FStar_Syntax_Syntax.comp ->
        (env * FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp))
  =
  fun g ->
    fun b ->
      fun c ->
        let uu___ = fresh_binder g b in
        match uu___ with
        | (g1, bx) ->
            let c1 =
              FStar_Syntax_Subst.subst_comp
                [FStar_Syntax_Syntax.DB
                   (Prims.int_zero, (bx.FStar_Syntax_Syntax.binder_bv))] c in
            (g1, bx, c1)
let (open_comp_binders :
  env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.comp ->
        (env * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp))
  =
  fun g ->
    fun bs ->
      fun c ->
        let uu___ = open_binders g bs in
        match uu___ with
        | (g1, bs1, s) ->
            let c1 = FStar_Syntax_Subst.subst_comp s c in (g1, bs1, c1)
let (arrow_formals_comp :
  env ->
    FStar_Syntax_Syntax.term ->
      (env * FStar_Syntax_Syntax.binder Prims.list *
        FStar_Syntax_Syntax.comp))
  =
  fun g ->
    fun c ->
      let uu___ = FStar_Syntax_Util.arrow_formals_comp_ln c in
      match uu___ with
      | (bs, c1) ->
          let uu___1 = open_binders g bs in
          (match uu___1 with
           | (g1, bs1, subst) ->
               let uu___2 = FStar_Syntax_Subst.subst_comp subst c1 in
               (g1, bs1, uu___2))
let (open_branch :
  env -> FStar_Syntax_Syntax.branch -> (env * FStar_Syntax_Syntax.branch)) =
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
                   FStar_Compiler_Util.map_option
                     (FStar_Syntax_Subst.subst s) wopt in
                 let uu___4 = FStar_Syntax_Subst.subst s e in
                 (p1, uu___3, uu___4) in
               (g1, uu___2))
let (open_branches_eq_pat :
  env ->
    FStar_Syntax_Syntax.branch ->
      FStar_Syntax_Syntax.branch ->
        (env * (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term
          FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) *
          (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term
          FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term)))
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
                          FStar_Compiler_Util.map_option
                            (FStar_Syntax_Subst.subst s) wopt0 in
                        let uu___6 = FStar_Syntax_Subst.subst s e0 in
                        (p01, uu___5, uu___6) in
                      let uu___5 =
                        let uu___6 =
                          FStar_Compiler_Util.map_option
                            (FStar_Syntax_Subst.subst s) wopt1 in
                        let uu___7 = FStar_Syntax_Subst.subst s e1 in
                        (p01, uu___6, uu___7) in
                      (g1, uu___4, uu___5)))
type precondition = FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option
type 'a success = ('a * precondition)
type relation =
  | EQUALITY 
  | SUBTYPING of FStar_Syntax_Syntax.term FStar_Pervasives_Native.option 
let (uu___is_EQUALITY : relation -> Prims.bool) =
  fun projectee -> match projectee with | EQUALITY -> true | uu___ -> false
let (uu___is_SUBTYPING : relation -> Prims.bool) =
  fun projectee ->
    match projectee with | SUBTYPING _0 -> true | uu___ -> false
let (__proj__SUBTYPING__item___0 :
  relation -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | SUBTYPING _0 -> _0
let (relation_to_string : relation -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | EQUALITY -> "=?="
    | SUBTYPING (FStar_Pervasives_Native.None) -> "<:?"
    | SUBTYPING (FStar_Pervasives_Native.Some tm) ->
        let uu___1 = FStar_Syntax_Print.term_to_string tm in
        FStar_Compiler_Util.format1 "( <:? %s)" uu___1
type context_term =
  | CtxTerm of FStar_Syntax_Syntax.term 
  | CtxRel of FStar_Syntax_Syntax.term * relation * FStar_Syntax_Syntax.term 
let (uu___is_CtxTerm : context_term -> Prims.bool) =
  fun projectee -> match projectee with | CtxTerm _0 -> true | uu___ -> false
let (__proj__CtxTerm__item___0 : context_term -> FStar_Syntax_Syntax.term) =
  fun projectee -> match projectee with | CtxTerm _0 -> _0
let (uu___is_CtxRel : context_term -> Prims.bool) =
  fun projectee ->
    match projectee with | CtxRel (_0, _1, _2) -> true | uu___ -> false
let (__proj__CtxRel__item___0 : context_term -> FStar_Syntax_Syntax.term) =
  fun projectee -> match projectee with | CtxRel (_0, _1, _2) -> _0
let (__proj__CtxRel__item___1 : context_term -> relation) =
  fun projectee -> match projectee with | CtxRel (_0, _1, _2) -> _1
let (__proj__CtxRel__item___2 : context_term -> FStar_Syntax_Syntax.term) =
  fun projectee -> match projectee with | CtxRel (_0, _1, _2) -> _2
let (context_term_to_string : context_term -> Prims.string) =
  fun c ->
    match c with
    | CtxTerm term -> FStar_Syntax_Print.term_to_string term
    | CtxRel (t0, r, t1) ->
        let uu___ = FStar_Syntax_Print.term_to_string t0 in
        let uu___1 = relation_to_string r in
        let uu___2 = FStar_Syntax_Print.term_to_string t1 in
        FStar_Compiler_Util.format3 "%s %s %s" uu___ uu___1 uu___2
type context =
  {
  no_guard: Prims.bool ;
  error_context:
    (Prims.string * context_term FStar_Pervasives_Native.option) Prims.list }
let (__proj__Mkcontext__item__no_guard : context -> Prims.bool) =
  fun projectee ->
    match projectee with | { no_guard; error_context;_} -> no_guard
let (__proj__Mkcontext__item__error_context :
  context ->
    (Prims.string * context_term FStar_Pervasives_Native.option) Prims.list)
  =
  fun projectee ->
    match projectee with | { no_guard; error_context;_} -> error_context
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
            FStar_Compiler_Util.format3 "%s %s (%s)\n" depth msg uu___ in
          let tl1 = aux (Prims.op_Hat depth ">") tl in Prims.op_Hat hd tl1 in
    aux "" (FStar_Compiler_List.rev ctx.error_context)
type error = (context * Prims.string)
let (print_error : error -> Prims.string) =
  fun err ->
    let uu___ = err in
    match uu___ with
    | (ctx, msg) ->
        let uu___1 = print_context ctx in
        FStar_Compiler_Util.format2 "%s%s" uu___1 msg
let (print_error_short : error -> Prims.string) =
  fun err -> FStar_Pervasives_Native.snd err
type 'a result = context -> ('a success, error) FStar_Pervasives.either
type effect_label =
  | E_TOTAL 
  | E_GHOST 
let (uu___is_E_TOTAL : effect_label -> Prims.bool) =
  fun projectee -> match projectee with | E_TOTAL -> true | uu___ -> false
let (uu___is_E_GHOST : effect_label -> Prims.bool) =
  fun projectee -> match projectee with | E_GHOST -> true | uu___ -> false
type hash_entry =
  {
  he_term: FStar_Syntax_Syntax.term ;
  he_gamma: FStar_Syntax_Syntax.binding Prims.list ;
  he_res: (effect_label * FStar_Syntax_Syntax.typ) success }
let (__proj__Mkhash_entry__item__he_term :
  hash_entry -> FStar_Syntax_Syntax.term) =
  fun projectee ->
    match projectee with | { he_term; he_gamma; he_res;_} -> he_term
let (__proj__Mkhash_entry__item__he_gamma :
  hash_entry -> FStar_Syntax_Syntax.binding Prims.list) =
  fun projectee ->
    match projectee with | { he_term; he_gamma; he_res;_} -> he_gamma
let (__proj__Mkhash_entry__item__he_res :
  hash_entry -> (effect_label * FStar_Syntax_Syntax.typ) success) =
  fun projectee ->
    match projectee with | { he_term; he_gamma; he_res;_} -> he_res
type tc_table = hash_entry FStar_Syntax_TermHashTable.hashtable
let (equal_term_for_hash :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1 ->
    fun t2 ->
      FStar_Profiling.profile
        (fun uu___ -> FStar_Syntax_Hash.equal_term t1 t2)
        FStar_Pervasives_Native.None
        "FStar.TypeChecker.Core.equal_term_for_hash"
let (equal_term :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1 ->
    fun t2 ->
      FStar_Profiling.profile
        (fun uu___ -> FStar_Syntax_Hash.equal_term t1 t2)
        FStar_Pervasives_Native.None "FStar.TypeChecker.Core.equal_term"
let (table : tc_table) =
  FStar_Syntax_TermHashTable.create (Prims.parse_int "1048576")
type cache_stats_t = {
  hits: Prims.int ;
  misses: Prims.int }
let (__proj__Mkcache_stats_t__item__hits : cache_stats_t -> Prims.int) =
  fun projectee -> match projectee with | { hits; misses;_} -> hits
let (__proj__Mkcache_stats_t__item__misses : cache_stats_t -> Prims.int) =
  fun projectee -> match projectee with | { hits; misses;_} -> misses
let (cache_stats : cache_stats_t FStar_Compiler_Effect.ref) =
  FStar_Compiler_Util.mk_ref
    { hits = Prims.int_zero; misses = Prims.int_zero }
let (record_cache_hit : unit -> unit) =
  fun uu___ ->
    let cs = FStar_Compiler_Effect.op_Bang cache_stats in
    FStar_Compiler_Effect.op_Colon_Equals cache_stats
      { hits = (cs.hits + Prims.int_one); misses = (cs.misses) }
let (record_cache_miss : unit -> unit) =
  fun uu___ ->
    let cs = FStar_Compiler_Effect.op_Bang cache_stats in
    FStar_Compiler_Effect.op_Colon_Equals cache_stats
      { hits = (cs.hits); misses = (cs.misses + Prims.int_one) }
let (reset_cache_stats : unit -> unit) =
  fun uu___ ->
    FStar_Compiler_Effect.op_Colon_Equals cache_stats
      { hits = Prims.int_zero; misses = Prims.int_zero }
let (report_cache_stats : unit -> cache_stats_t) =
  fun uu___ -> FStar_Compiler_Effect.op_Bang cache_stats
let (clear_memo_table : unit -> unit) =
  fun uu___ -> FStar_Syntax_TermHashTable.clear table
let (insert :
  env ->
    FStar_Syntax_Syntax.term ->
      (effect_label * FStar_Syntax_Syntax.typ) success -> unit)
  =
  fun g ->
    fun e ->
      fun res ->
        let entry =
          {
            he_term = e;
            he_gamma = ((g.tcenv).FStar_TypeChecker_Env.gamma);
            he_res = res
          } in
        FStar_Syntax_TermHashTable.insert e entry table
let return : 'a . 'a -> 'a result =
  fun x ->
    fun uu___ -> FStar_Pervasives.Inl (x, FStar_Pervasives_Native.None)
let (and_pre :
  precondition ->
    precondition ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
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
          let uu___ = FStar_Syntax_Util.mk_conj p11 p21 in
          FStar_Pervasives_Native.Some uu___
let op_let_Bang : 'a 'b . 'a result -> ('a -> 'b result) -> 'b result =
  fun x ->
    fun y ->
      fun ctx0 ->
        let uu___ = x ctx0 in
        match uu___ with
        | FStar_Pervasives.Inl (x1, g1) ->
            let uu___1 = let uu___2 = y x1 in uu___2 ctx0 in
            (match uu___1 with
             | FStar_Pervasives.Inl (y1, g2) ->
                 let uu___2 = let uu___3 = and_pre g1 g2 in (y1, uu___3) in
                 FStar_Pervasives.Inl uu___2
             | err -> err)
        | FStar_Pervasives.Inr err -> FStar_Pervasives.Inr err
let op_and_Bang : 'a 'b . 'a result -> 'b result -> ('a * 'b) result =
  fun x ->
    fun y -> op_let_Bang x (fun v -> op_let_Bang y (fun u -> return (v, u)))
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
  fun msg -> fun ctx -> FStar_Pervasives.Inr (ctx, msg)
let (dump_context : unit result) =
  fun ctx ->
    (let uu___1 = print_context ctx in
     FStar_Compiler_Util.print_string uu___1);
    (let uu___1 = return () in uu___1 ctx)
let handle_with : 'a . 'a result -> (unit -> 'a result) -> 'a result =
  fun x ->
    fun h ->
      fun ctx ->
        let uu___ = x ctx in
        match uu___ with
        | FStar_Pervasives.Inr uu___1 -> let uu___2 = h () in uu___2 ctx
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
          let ctx' =
            {
              no_guard = (ctx.no_guard);
              error_context = ((msg, t) :: (ctx.error_context))
            } in
          let uu___ = x () in uu___ ctx'
let (mk_type :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun u ->
    FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
      FStar_Compiler_Range.dummyRange
let (is_type :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe result) =
  fun g ->
    fun t ->
      let aux t1 =
        let uu___ =
          let uu___1 = FStar_Syntax_Subst.compress t1 in
          uu___1.FStar_Syntax_Syntax.n in
        match uu___ with
        | FStar_Syntax_Syntax.Tm_type u -> return u
        | uu___1 ->
            let uu___2 =
              let uu___3 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Compiler_Util.format1 "Expected a type; got %s" uu___3 in
            fail uu___2 in
      with_context "is_type" (FStar_Pervasives_Native.Some (CtxTerm t))
        (fun uu___ ->
           let uu___1 = aux t in
           handle_with uu___1
             (fun uu___2 ->
                let uu___3 =
                  let uu___4 =
                    FStar_TypeChecker_Normalize.unfold_whnf g.tcenv t in
                  FStar_Syntax_Util.unrefine uu___4 in
                aux uu___3))
let rec (is_arrow :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binder * effect_label * FStar_Syntax_Syntax.typ)
        result)
  =
  fun g ->
    fun t ->
      let rec aux t1 =
        let uu___ =
          let uu___1 = FStar_Syntax_Subst.compress t1 in
          uu___1.FStar_Syntax_Syntax.n in
        match uu___ with
        | FStar_Syntax_Syntax.Tm_arrow (x::[], c) ->
            let uu___1 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
            if uu___1
            then
              let uu___2 = open_comp g x c in
              (match uu___2 with
               | (g1, x1, c1) ->
                   let eff =
                     let uu___3 = FStar_Syntax_Util.is_total_comp c1 in
                     if uu___3 then E_TOTAL else E_GHOST in
                   return (x1, eff, (FStar_Syntax_Util.comp_result c1)))
            else
              (let e_tag =
                 let uu___3 = c.FStar_Syntax_Syntax.n in
                 match uu___3 with
                 | FStar_Syntax_Syntax.Comp ct ->
                     let uu___4 =
                       (FStar_Ident.lid_equals
                          ct.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_Pure_lid)
                         ||
                         (FStar_Ident.lid_equals
                            ct.FStar_Syntax_Syntax.effect_name
                            FStar_Parser_Const.effect_Lemma_lid) in
                     if uu___4
                     then FStar_Pervasives_Native.Some E_TOTAL
                     else
                       (let uu___6 =
                          FStar_Ident.lid_equals
                            ct.FStar_Syntax_Syntax.effect_name
                            FStar_Parser_Const.effect_Ghost_lid in
                        if uu___6
                        then FStar_Pervasives_Native.Some E_GHOST
                        else FStar_Pervasives_Native.None) in
               match e_tag with
               | FStar_Pervasives_Native.None ->
                   let uu___3 =
                     let uu___4 =
                       FStar_Ident.string_of_lid
                         (FStar_Syntax_Util.comp_effect_name c) in
                     FStar_Compiler_Util.format1
                       "Expected total or gtot arrow, got %s" uu___4 in
                   fail uu___3
               | FStar_Pervasives_Native.Some e_tag1 ->
                   let uu___3 = arrow_formals_comp g t1 in
                   (match uu___3 with
                    | (g1, x1::[], c1) ->
                        let uu___4 = FStar_Syntax_Util.comp_effect_args c1 in
                        (match uu___4 with
                         | (pre, uu___5)::(post, uu___6)::uu___7 ->
                             let arg_typ =
                               FStar_Syntax_Util.refine
                                 x1.FStar_Syntax_Syntax.binder_bv pre in
                             let res_typ =
                               let r =
                                 FStar_Syntax_Syntax.new_bv
                                   FStar_Pervasives_Native.None
                                   (FStar_Syntax_Util.comp_result c1) in
                               let post1 =
                                 let uu___8 =
                                   let uu___9 =
                                     let uu___10 =
                                       FStar_Syntax_Syntax.bv_to_name r in
                                     (uu___10, FStar_Pervasives_Native.None) in
                                   [uu___9] in
                                 FStar_Syntax_Syntax.mk_Tm_app post uu___8
                                   post.FStar_Syntax_Syntax.pos in
                               FStar_Syntax_Util.refine r post1 in
                             let xbv =
                               let uu___8 = x1.FStar_Syntax_Syntax.binder_bv in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___8.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___8.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = arg_typ
                               } in
                             let x2 =
                               {
                                 FStar_Syntax_Syntax.binder_bv = xbv;
                                 FStar_Syntax_Syntax.binder_qual =
                                   (x1.FStar_Syntax_Syntax.binder_qual);
                                 FStar_Syntax_Syntax.binder_attrs =
                                   (x1.FStar_Syntax_Syntax.binder_attrs)
                               } in
                             return (x2, e_tag1, res_typ))))
        | FStar_Syntax_Syntax.Tm_arrow (x::xs, c) ->
            let t2 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (xs, c))
                t1.FStar_Syntax_Syntax.pos in
            let uu___1 = open_term g x t2 in
            (match uu___1 with | (g1, x1, t3) -> return (x1, E_TOTAL, t3))
        | FStar_Syntax_Syntax.Tm_refine (x, uu___1) ->
            is_arrow g x.FStar_Syntax_Syntax.sort
        | FStar_Syntax_Syntax.Tm_meta (t2, uu___1) -> aux t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2, uu___1, uu___2) -> aux t2
        | uu___1 ->
            let uu___2 =
              let uu___3 = FStar_Syntax_Print.tag_of_term t1 in
              let uu___4 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Compiler_Util.format2 "Expected an arrow, got (%s) %s"
                uu___3 uu___4 in
            fail uu___2 in
      with_context "is_arrow" FStar_Pervasives_Native.None
        (fun uu___ ->
           let uu___1 = aux t in
           handle_with uu___1
             (fun uu___2 ->
                let uu___3 =
                  FStar_TypeChecker_Normalize.unfold_whnf g.tcenv t in
                aux uu___3))
let (check_arg_qual :
  FStar_Syntax_Syntax.aqual -> FStar_Syntax_Syntax.bqual -> unit result) =
  fun a ->
    fun b ->
      match b with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit uu___) ->
          (match a with
           | FStar_Pervasives_Native.Some
               { FStar_Syntax_Syntax.aqual_implicit = true;
                 FStar_Syntax_Syntax.aqual_attributes = uu___1;_}
               -> return ()
           | uu___1 -> fail "missing arg qualifier implicit")
      | uu___ ->
          (match a with
           | FStar_Pervasives_Native.Some
               { FStar_Syntax_Syntax.aqual_implicit = true;
                 FStar_Syntax_Syntax.aqual_attributes = uu___1;_}
               -> fail "extra arg qualifier implicit"
           | uu___1 -> return ())
let (check_bqual :
  FStar_Syntax_Syntax.bqual -> FStar_Syntax_Syntax.bqual -> unit result) =
  fun b0 ->
    fun b1 ->
      match (b0, b1) with
      | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
          return ()
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b01),
         FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b11)) ->
          return ()
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality),
         FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality)) ->
          return ()
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t1),
         FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t2)) ->
          let uu___ = equal_term t1 t2 in
          if uu___ then return () else fail "Binder qualifier mismatch"
      | uu___ -> fail "Binder qualifier mismatch"
let (check_aqual :
  FStar_Syntax_Syntax.aqual -> FStar_Syntax_Syntax.aqual -> unit result) =
  fun a0 ->
    fun a1 ->
      match (a0, a1) with
      | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
          return ()
      | (FStar_Pervasives_Native.Some
         { FStar_Syntax_Syntax.aqual_implicit = b0;
           FStar_Syntax_Syntax.aqual_attributes = uu___;_},
         FStar_Pervasives_Native.Some
         { FStar_Syntax_Syntax.aqual_implicit = b1;
           FStar_Syntax_Syntax.aqual_attributes = uu___1;_})
          -> if b0 = b1 then return () else fail "Unequal arg qualifiers"
      | uu___ -> fail "Unequal arg qualifiers"
let (mk_forall_l :
  FStar_Syntax_Syntax.universes ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun us ->
    fun xs ->
      fun t ->
        FStar_Compiler_List.fold_right2
          (fun u ->
             fun x ->
               fun t1 ->
                 FStar_Syntax_Util.mk_forall u
                   x.FStar_Syntax_Syntax.binder_bv t1) us xs t
let (close_guard :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.universes -> precondition -> precondition)
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
  FStar_Syntax_Syntax.binder ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.term -> precondition -> precondition)
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
                      FStar_Syntax_Syntax.bv_to_name
                        x.FStar_Syntax_Syntax.binder_bv in
                    FStar_Syntax_Util.mk_eq2 u
                      (x.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort
                      uu___2 t1 in
                  FStar_Syntax_Util.mk_imp uu___1 t1 in
                FStar_Syntax_Util.mk_forall u x.FStar_Syntax_Syntax.binder_bv
                  t2 in
              FStar_Pervasives_Native.Some uu___
let with_binders :
  'a .
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.universes -> 'a result -> 'a result
  =
  fun xs ->
    fun us ->
      fun f ->
        fun ctx ->
          let uu___ = f ctx in
          match uu___ with
          | FStar_Pervasives.Inl (t, g) ->
              let uu___1 = let uu___2 = close_guard xs us g in (t, uu___2) in
              FStar_Pervasives.Inl uu___1
          | err -> err
let with_definition :
  'a .
    FStar_Syntax_Syntax.binder ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.term -> 'a result -> 'a result
  =
  fun x ->
    fun u ->
      fun t ->
        fun f ->
          fun ctx ->
            let uu___ = f ctx in
            match uu___ with
            | FStar_Pervasives.Inl (a1, g) ->
                let uu___1 =
                  let uu___2 = close_guard_with_definition x u t g in
                  (a1, uu___2) in
                FStar_Pervasives.Inl uu___1
            | err -> err
let (guard : FStar_Syntax_Syntax.typ -> unit result) =
  fun t ->
    fun uu___ -> FStar_Pervasives.Inl ((), (FStar_Pervasives_Native.Some t))
let (abs :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.term) ->
      FStar_Syntax_Syntax.term)
  =
  fun a ->
    fun f ->
      let x = FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None a in
      let xb = FStar_Syntax_Syntax.mk_binder x in
      let uu___ = f xb in
      FStar_Syntax_Util.abs [xb] uu___ FStar_Pervasives_Native.None
let (weaken_subtyping_guard :
  FStar_Syntax_Syntax.term -> precondition -> precondition) =
  fun p ->
    fun g ->
      FStar_Compiler_Util.map_opt g (fun q -> FStar_Syntax_Util.mk_imp p q)
let (strengthen_subtyping_guard :
  FStar_Syntax_Syntax.term -> precondition -> precondition) =
  fun p ->
    fun g ->
      let uu___ =
        let uu___1 =
          FStar_Compiler_Util.map_opt g
            (fun q -> FStar_Syntax_Util.mk_conj p q) in
        FStar_Compiler_Util.dflt p uu___1 in
      FStar_Pervasives_Native.Some uu___
let weaken :
  'a .
    FStar_Syntax_Syntax.term ->
      'a result -> context -> ('a success, error) FStar_Pervasives.either
  =
  fun p ->
    fun g ->
      fun ctx ->
        let uu___ = g ctx in
        match uu___ with
        | FStar_Pervasives.Inl (x, q) ->
            let uu___1 =
              let uu___2 = weaken_subtyping_guard p q in (x, uu___2) in
            FStar_Pervasives.Inl uu___1
        | err -> err
let weaken_with_guard_formula :
  'a .
    FStar_TypeChecker_Common.guard_formula ->
      'a result -> context -> ('a success, error) FStar_Pervasives.either
  =
  fun p ->
    fun g ->
      match p with
      | FStar_TypeChecker_Common.Trivial -> g
      | FStar_TypeChecker_Common.NonTrivial p1 -> weaken p1 g
let (push_hypothesis : env -> FStar_Syntax_Syntax.term -> env) =
  fun g ->
    fun h ->
      let bv =
        FStar_Syntax_Syntax.new_bv
          (FStar_Pervasives_Native.Some (h.FStar_Syntax_Syntax.pos)) h in
      let b = FStar_Syntax_Syntax.mk_binder bv in
      let uu___ = fresh_binder g b in FStar_Pervasives_Native.fst uu___
let strengthen :
  'a .
    FStar_Syntax_Syntax.term ->
      'a result -> context -> ('a success, error) FStar_Pervasives.either
  =
  fun p ->
    fun g ->
      fun ctx ->
        let uu___ = g ctx in
        match uu___ with
        | FStar_Pervasives.Inl (x, q) ->
            let uu___1 =
              let uu___2 = strengthen_subtyping_guard p q in (x, uu___2) in
            FStar_Pervasives.Inl uu___1
        | err -> err
let no_guard : 'a . 'a result -> 'a result =
  fun g ->
    fun ctx ->
      let uu___ = g { no_guard = true; error_context = (ctx.error_context) } in
      match uu___ with
      | FStar_Pervasives.Inl (x, FStar_Pervasives_Native.None) ->
          FStar_Pervasives.Inl (x, FStar_Pervasives_Native.None)
      | FStar_Pervasives.Inl (x, FStar_Pervasives_Native.Some g1) ->
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_Syntax_Print.term_to_string g1 in
              FStar_Compiler_Util.format1 "Unexpected guard: %s" uu___3 in
            fail uu___2 in
          uu___1 ctx
      | err -> err
let (equatable : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g ->
    fun t ->
      let uu___ = FStar_Syntax_Util.head_and_args t in
      match uu___ with
      | (head, uu___1) ->
          FStar_TypeChecker_Rel.may_relate_with_logical_guard g.tcenv true
            head
let (apply_predicate :
  FStar_Syntax_Syntax.binder ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term)
  =
  fun x ->
    fun p ->
      fun e ->
        FStar_Syntax_Subst.subst
          [FStar_Syntax_Syntax.NT ((x.FStar_Syntax_Syntax.binder_bv), e)] p
let (curry_arrow :
  FStar_Syntax_Syntax.binder ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun x ->
    fun xs ->
      fun c ->
        let tail =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (xs, c))
            FStar_Compiler_Range.dummyRange in
        let uu___ =
          let uu___1 =
            let uu___2 = FStar_Syntax_Syntax.mk_Total tail in ([x], uu___2) in
          FStar_Syntax_Syntax.Tm_arrow uu___1 in
        FStar_Syntax_Syntax.mk uu___ FStar_Compiler_Range.dummyRange
let (curry_abs :
  FStar_Syntax_Syntax.binder ->
    FStar_Syntax_Syntax.binder ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b0 ->
    fun b1 ->
      fun bs ->
        fun body ->
          fun ropt ->
            let tail =
              FStar_Syntax_Syntax.mk
                (FStar_Syntax_Syntax.Tm_abs ((b1 :: bs), body, ropt))
                body.FStar_Syntax_Syntax.pos in
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_abs
                 ([b0], tail, FStar_Pervasives_Native.None))
              body.FStar_Syntax_Syntax.pos
let (is_gtot_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c ->
    (FStar_Syntax_Util.is_tot_or_gtot_comp c) &&
      (let uu___ = FStar_Syntax_Util.is_total_comp c in
       Prims.op_Negation uu___)
let rec (context_included :
  FStar_Syntax_Syntax.binding Prims.list ->
    FStar_Syntax_Syntax.binding Prims.list -> Prims.bool)
  =
  fun g0 ->
    fun g1 ->
      let uu___ = FStar_Compiler_Util.physical_equality g0 g1 in
      if uu___
      then true
      else
        (match (g0, g1) with
         | ([], uu___2) -> true
         | (b0::g0', b1::g1') ->
             (match (b0, b1) with
              | (FStar_Syntax_Syntax.Binding_var x0,
                 FStar_Syntax_Syntax.Binding_var x1) ->
                  if
                    x0.FStar_Syntax_Syntax.index =
                      x1.FStar_Syntax_Syntax.index
                  then
                    (equal_term x0.FStar_Syntax_Syntax.sort
                       x1.FStar_Syntax_Syntax.sort)
                      && (context_included g0' g1')
                  else context_included g0 g1'
              | (FStar_Syntax_Syntax.Binding_lid uu___2,
                 FStar_Syntax_Syntax.Binding_lid uu___3) -> true
              | (FStar_Syntax_Syntax.Binding_univ uu___2,
                 FStar_Syntax_Syntax.Binding_univ uu___3) -> true
              | uu___2 -> false)
         | uu___2 -> false)
let (curry_application :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        Prims.list ->
        FStar_Compiler_Range.range ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun hd ->
    fun arg ->
      fun args ->
        fun p ->
          let head =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd, [arg])) p in
          let t =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (head, args))
              p in
          t
let (lookup :
  env ->
    FStar_Syntax_Syntax.term ->
      (effect_label * FStar_Syntax_Syntax.typ) result)
  =
  fun g ->
    fun e ->
      let uu___ = FStar_Syntax_TermHashTable.lookup e table in
      match uu___ with
      | FStar_Pervasives_Native.None -> fail "not in cache"
      | FStar_Pervasives_Native.Some he ->
          let uu___1 =
            context_included he.he_gamma
              (g.tcenv).FStar_TypeChecker_Env.gamma in
          if uu___1
          then
            (record_cache_hit ();
             (fun uu___3 -> FStar_Pervasives.Inl (he.he_res)))
          else (record_cache_miss (); fail "not in cache")
let (check_no_escape :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.term -> unit result) =
  fun bs ->
    fun t ->
      let xs = FStar_Syntax_Free.names t in
      let uu___ =
        FStar_Compiler_Util.for_all
          (fun b ->
             let uu___1 =
               FStar_Compiler_Util.set_mem b.FStar_Syntax_Syntax.binder_bv xs in
             Prims.op_Negation uu___1) bs in
      if uu___ then return () else fail "Name escapes its scope"
let rec map :
  'a 'b . ('a -> 'b result) -> 'a Prims.list -> 'b Prims.list result =
  fun f ->
    fun l ->
      match l with
      | [] -> return []
      | hd::tl ->
          let uu___ = f hd in
          op_let_Bang uu___
            (fun hd1 ->
               let uu___1 = map f tl in
               op_let_Bang uu___1 (fun tl1 -> return (hd1 :: tl1)))
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
          | ([], []) -> return b1
          | (x::xs1, y::ys1) ->
              let uu___ = f x y b1 in
              op_let_Bang uu___ (fun b2 -> iter2 xs1 ys1 f b2)
          | uu___ -> fail "Lists of differing length"
let (non_informative : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g -> fun t -> FStar_TypeChecker_Normalize.non_info_norm g.tcenv t
let (as_comp :
  env -> (effect_label * FStar_Syntax_Syntax.typ) -> FStar_Syntax_Syntax.comp)
  =
  fun g ->
    fun et ->
      match et with
      | (E_TOTAL, t) -> FStar_Syntax_Syntax.mk_Total t
      | (E_GHOST, t) ->
          let uu___ = non_informative g t in
          if uu___
          then FStar_Syntax_Syntax.mk_Total t
          else FStar_Syntax_Syntax.mk_GTotal t
let (comp_as_effect_label_and_type :
  FStar_Syntax_Syntax.comp ->
    (effect_label * FStar_Syntax_Syntax.typ) FStar_Pervasives_Native.option)
  =
  fun c ->
    let uu___ = FStar_Syntax_Util.is_total_comp c in
    if uu___
    then
      FStar_Pervasives_Native.Some
        (E_TOTAL, (FStar_Syntax_Util.comp_result c))
    else
      (let uu___2 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
       if uu___2
       then
         FStar_Pervasives_Native.Some
           (E_GHOST, (FStar_Syntax_Util.comp_result c))
       else FStar_Pervasives_Native.None)
let (join_eff : effect_label -> effect_label -> effect_label) =
  fun e0 ->
    fun e1 ->
      match (e0, e1) with
      | (E_GHOST, uu___) -> E_GHOST
      | (uu___, E_GHOST) -> E_GHOST
      | uu___ -> E_TOTAL
let (join_eff_l : effect_label Prims.list -> effect_label) =
  fun es -> FStar_List_Tot_Base.fold_right join_eff es E_TOTAL
let (guard_not_allowed : Prims.bool result) =
  fun ctx ->
    FStar_Pervasives.Inl ((ctx.no_guard), FStar_Pervasives_Native.None)
let (default_norm_steps : FStar_TypeChecker_Env.steps) =
  [FStar_TypeChecker_Env.Primops;
  FStar_TypeChecker_Env.Weak;
  FStar_TypeChecker_Env.HNF;
  FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant;
  FStar_TypeChecker_Env.Unascribe;
  FStar_TypeChecker_Env.Eager_unfolding;
  FStar_TypeChecker_Env.Iota;
  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta]
let (debug : env -> (unit -> unit) -> unit) =
  fun g ->
    fun f ->
      let uu___ =
        FStar_TypeChecker_Env.debug g.tcenv (FStar_Options.Other "Core") in
      if uu___ then f () else ()
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
let (side_to_string : side -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | Left -> "Left"
    | Right -> "Right"
    | Both -> "Both"
    | Neither -> "Neither"
let rec (check_relation :
  env ->
    relation ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit result)
  =
  fun g ->
    fun rel ->
      fun t0 ->
        fun t1 ->
          let err uu___ =
            match rel with
            | EQUALITY ->
                let uu___1 =
                  let uu___2 = FStar_Syntax_Print.term_to_string t0 in
                  let uu___3 = FStar_Syntax_Print.term_to_string t1 in
                  FStar_Compiler_Util.format2 "not equal terms: %s <> %s"
                    uu___2 uu___3 in
                fail uu___1
            | uu___1 ->
                let uu___2 =
                  let uu___3 = FStar_Syntax_Print.term_to_string t0 in
                  let uu___4 = FStar_Syntax_Print.term_to_string t1 in
                  FStar_Compiler_Util.format2 "%s is not a subtype of %s"
                    uu___3 uu___4 in
                fail uu___2 in
          let rel_to_string rel1 =
            match rel1 with | EQUALITY -> "=?=" | uu___ -> "<:?" in
          (let uu___1 =
             FStar_TypeChecker_Env.debug g.tcenv (FStar_Options.Other "Core") in
           if uu___1
           then
             let uu___2 = FStar_Syntax_Print.tag_of_term t0 in
             let uu___3 = FStar_Syntax_Print.term_to_string t0 in
             let uu___4 = FStar_Syntax_Print.tag_of_term t1 in
             let uu___5 = FStar_Syntax_Print.term_to_string t1 in
             FStar_Compiler_Util.print5 "check_relation (%s) %s %s (%s) %s\n"
               uu___2 uu___3 (rel_to_string rel) uu___4 uu___5
           else ());
          op_let_Bang guard_not_allowed
            (fun guard_not_ok ->
               let guard_ok = Prims.op_Negation guard_not_ok in
               let head_matches t01 t11 =
                 let head0 = FStar_Syntax_Util.leftmost_head t01 in
                 let head1 = FStar_Syntax_Util.leftmost_head t11 in
                 let uu___1 =
                   let uu___2 =
                     let uu___3 = FStar_Syntax_Util.un_uinst head0 in
                     uu___3.FStar_Syntax_Syntax.n in
                   let uu___3 =
                     let uu___4 = FStar_Syntax_Util.un_uinst head1 in
                     uu___4.FStar_Syntax_Syntax.n in
                   (uu___2, uu___3) in
                 match uu___1 with
                 | (FStar_Syntax_Syntax.Tm_fvar fv0,
                    FStar_Syntax_Syntax.Tm_fvar fv1) ->
                     FStar_Syntax_Syntax.fv_eq fv0 fv1
                 | (FStar_Syntax_Syntax.Tm_name x0,
                    FStar_Syntax_Syntax.Tm_name x1) ->
                     FStar_Syntax_Syntax.bv_eq x0 x1
                 | (FStar_Syntax_Syntax.Tm_constant c0,
                    FStar_Syntax_Syntax.Tm_constant c1) ->
                     equal_term head0 head1
                 | (FStar_Syntax_Syntax.Tm_type uu___2,
                    FStar_Syntax_Syntax.Tm_type uu___3) -> true
                 | (FStar_Syntax_Syntax.Tm_arrow uu___2,
                    FStar_Syntax_Syntax.Tm_arrow uu___3) -> true
                 | (FStar_Syntax_Syntax.Tm_match uu___2,
                    FStar_Syntax_Syntax.Tm_match uu___3) -> true
                 | uu___2 -> false in
               let which_side_to_unfold t01 t11 =
                 let rec delta_depth_of_head t =
                   let head = FStar_Syntax_Util.leftmost_head t in
                   let uu___1 =
                     let uu___2 = FStar_Syntax_Util.un_uinst head in
                     uu___2.FStar_Syntax_Syntax.n in
                   match uu___1 with
                   | FStar_Syntax_Syntax.Tm_fvar fv ->
                       let uu___2 =
                         FStar_TypeChecker_Env.delta_depth_of_fv g.tcenv fv in
                       FStar_Pervasives_Native.Some uu___2
                   | FStar_Syntax_Syntax.Tm_match
                       (t2, uu___2, uu___3, uu___4) -> delta_depth_of_head t2
                   | uu___2 -> FStar_Pervasives_Native.None in
                 let dd0 = delta_depth_of_head t01 in
                 let dd1 = delta_depth_of_head t11 in
                 match (dd0, dd1) with
                 | (FStar_Pervasives_Native.Some uu___1,
                    FStar_Pervasives_Native.None) -> Left
                 | (FStar_Pervasives_Native.None,
                    FStar_Pervasives_Native.Some uu___1) -> Right
                 | (FStar_Pervasives_Native.Some dd01,
                    FStar_Pervasives_Native.Some dd11) ->
                     if dd01 = dd11
                     then Both
                     else
                       (let uu___2 =
                          FStar_TypeChecker_Common.delta_depth_greater_than
                            dd01 dd11 in
                        if uu___2 then Left else Right)
                 | (FStar_Pervasives_Native.None,
                    FStar_Pervasives_Native.None) -> Neither in
               let maybe_unfold_side side1 t01 t11 =
                 FStar_Profiling.profile
                   (fun uu___1 ->
                      match side1 with
                      | Neither -> FStar_Pervasives_Native.None
                      | Both ->
                          let uu___2 =
                            let uu___3 =
                              FStar_TypeChecker_Normalize.maybe_unfold_head
                                g.tcenv t01 in
                            let uu___4 =
                              FStar_TypeChecker_Normalize.maybe_unfold_head
                                g.tcenv t11 in
                            (uu___3, uu___4) in
                          (match uu___2 with
                           | (FStar_Pervasives_Native.Some t02,
                              FStar_Pervasives_Native.Some t12) ->
                               FStar_Pervasives_Native.Some (t02, t12)
                           | (FStar_Pervasives_Native.Some t02,
                              FStar_Pervasives_Native.None) ->
                               FStar_Pervasives_Native.Some (t02, t11)
                           | (FStar_Pervasives_Native.None,
                              FStar_Pervasives_Native.Some t12) ->
                               FStar_Pervasives_Native.Some (t01, t12)
                           | uu___3 -> FStar_Pervasives_Native.None)
                      | Left ->
                          let uu___2 =
                            FStar_TypeChecker_Normalize.maybe_unfold_head
                              g.tcenv t01 in
                          (match uu___2 with
                           | FStar_Pervasives_Native.Some t02 ->
                               FStar_Pervasives_Native.Some (t02, t11)
                           | uu___3 -> FStar_Pervasives_Native.None)
                      | Right ->
                          let uu___2 =
                            FStar_TypeChecker_Normalize.maybe_unfold_head
                              g.tcenv t11 in
                          (match uu___2 with
                           | FStar_Pervasives_Native.Some t12 ->
                               FStar_Pervasives_Native.Some (t01, t12)
                           | uu___3 -> FStar_Pervasives_Native.None))
                   FStar_Pervasives_Native.None
                   "FStar.TypeChecker.Core.maybe_unfold_side" in
               let maybe_unfold t01 t11 =
                 let uu___1 = which_side_to_unfold t01 t11 in
                 maybe_unfold_side uu___1 t01 t11 in
               let fallback t01 t11 =
                 if guard_ok
                 then
                   let uu___1 = (equatable g t01) || (equatable g t11) in
                   (if uu___1
                    then
                      let uu___2 = check' g t01 in
                      op_let_Bang uu___2
                        (fun uu___3 ->
                           match uu___3 with
                           | (uu___4, t_typ) ->
                               let uu___5 = universe_of g t_typ in
                               op_let_Bang uu___5
                                 (fun u ->
                                    let uu___6 =
                                      FStar_Syntax_Util.mk_eq2 u t_typ t01
                                        t11 in
                                    guard uu___6))
                    else err ())
                 else err () in
               let maybe_unfold_side_and_retry side1 t01 t11 =
                 let uu___1 = maybe_unfold_side side1 t01 t11 in
                 match uu___1 with
                 | FStar_Pervasives_Native.None -> fallback t01 t11
                 | FStar_Pervasives_Native.Some (t02, t12) ->
                     check_relation g rel t02 t12 in
               let maybe_unfold_and_retry t01 t11 =
                 let side1 = which_side_to_unfold t01 t11 in
                 maybe_unfold_side_and_retry side1 t01 t11 in
               let beta_iota_reduce t =
                 let t2 = FStar_Syntax_Subst.compress t in
                 match t2.FStar_Syntax_Syntax.n with
                 | FStar_Syntax_Syntax.Tm_app uu___1 ->
                     let head = FStar_Syntax_Util.leftmost_head t2 in
                     let uu___2 =
                       let uu___3 = FStar_Syntax_Subst.compress head in
                       uu___3.FStar_Syntax_Syntax.n in
                     (match uu___2 with
                      | FStar_Syntax_Syntax.Tm_abs uu___3 ->
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.Beta;
                            FStar_TypeChecker_Env.Iota] g.tcenv t2
                      | uu___3 -> t2)
                 | FStar_Syntax_Syntax.Tm_let uu___1 ->
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.Beta;
                       FStar_TypeChecker_Env.Iota] g.tcenv t2
                 | FStar_Syntax_Syntax.Tm_match uu___1 ->
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.Beta;
                       FStar_TypeChecker_Env.Iota] g.tcenv t2
                 | FStar_Syntax_Syntax.Tm_refine uu___1 ->
                     FStar_Syntax_Util.flatten_refinement t2
                 | uu___1 -> t2 in
               let beta_iota_reduce1 t =
                 FStar_Profiling.profile (fun uu___1 -> beta_iota_reduce t)
                   FStar_Pervasives_Native.None
                   "FStar.TypeChecker.Core.beta_iota_reduce" in
               let t01 =
                 let uu___1 = beta_iota_reduce1 t0 in
                 FStar_Syntax_Subst.compress uu___1 in
               let t11 =
                 let uu___1 = beta_iota_reduce1 t1 in
                 FStar_Syntax_Subst.compress uu___1 in
               let check_relation1 g1 rel1 t02 t12 =
                 with_context "check_relation"
                   (FStar_Pervasives_Native.Some (CtxRel (t02, rel1, t12)))
                   (fun uu___1 -> check_relation g1 rel1 t02 t12) in
               let uu___1 = equal_term t01 t11 in
               if uu___1
               then return ()
               else
                 (match ((t01.FStar_Syntax_Syntax.n),
                          (t11.FStar_Syntax_Syntax.n))
                  with
                  | (FStar_Syntax_Syntax.Tm_type u0,
                     FStar_Syntax_Syntax.Tm_type u1) ->
                      let uu___3 =
                        FStar_TypeChecker_Rel.teq_nosmt_force g.tcenv t01 t11 in
                      if uu___3 then return () else err ()
                  | (FStar_Syntax_Syntax.Tm_meta
                     (t02, FStar_Syntax_Syntax.Meta_pattern uu___3), uu___4)
                      -> check_relation1 g rel t02 t11
                  | (FStar_Syntax_Syntax.Tm_meta
                     (t02, FStar_Syntax_Syntax.Meta_named uu___3), uu___4) ->
                      check_relation1 g rel t02 t11
                  | (FStar_Syntax_Syntax.Tm_meta
                     (t02, FStar_Syntax_Syntax.Meta_labeled uu___3), uu___4)
                      -> check_relation1 g rel t02 t11
                  | (FStar_Syntax_Syntax.Tm_meta
                     (t02, FStar_Syntax_Syntax.Meta_desugared uu___3),
                     uu___4) -> check_relation1 g rel t02 t11
                  | (FStar_Syntax_Syntax.Tm_ascribed (t02, uu___3, uu___4),
                     uu___5) -> check_relation1 g rel t02 t11
                  | (uu___3, FStar_Syntax_Syntax.Tm_meta
                     (t12, FStar_Syntax_Syntax.Meta_pattern uu___4)) ->
                      check_relation1 g rel t01 t12
                  | (uu___3, FStar_Syntax_Syntax.Tm_meta
                     (t12, FStar_Syntax_Syntax.Meta_named uu___4)) ->
                      check_relation1 g rel t01 t12
                  | (uu___3, FStar_Syntax_Syntax.Tm_meta
                     (t12, FStar_Syntax_Syntax.Meta_labeled uu___4)) ->
                      check_relation1 g rel t01 t12
                  | (uu___3, FStar_Syntax_Syntax.Tm_meta
                     (t12, FStar_Syntax_Syntax.Meta_desugared uu___4)) ->
                      check_relation1 g rel t01 t12
                  | (uu___3, FStar_Syntax_Syntax.Tm_ascribed
                     (t12, uu___4, uu___5)) -> check_relation1 g rel t01 t12
                  | (FStar_Syntax_Syntax.Tm_uinst (f0, us0),
                     FStar_Syntax_Syntax.Tm_uinst (f1, us1)) ->
                      let uu___3 = equal_term f0 f1 in
                      if uu___3
                      then
                        let uu___4 =
                          FStar_TypeChecker_Rel.teq_nosmt_force g.tcenv t01
                            t11 in
                        (if uu___4 then return () else err ())
                      else maybe_unfold_and_retry t01 t11
                  | (FStar_Syntax_Syntax.Tm_fvar uu___3,
                     FStar_Syntax_Syntax.Tm_fvar uu___4) ->
                      maybe_unfold_and_retry t01 t11
                  | (FStar_Syntax_Syntax.Tm_refine (x0, f0),
                     FStar_Syntax_Syntax.Tm_refine (x1, f1)) ->
                      let uu___3 =
                        head_matches x0.FStar_Syntax_Syntax.sort
                          x1.FStar_Syntax_Syntax.sort in
                      if uu___3
                      then
                        let uu___4 =
                          check_relation1 g EQUALITY
                            x0.FStar_Syntax_Syntax.sort
                            x1.FStar_Syntax_Syntax.sort in
                        op_let_Bang uu___4
                          (fun uu___5 ->
                             let uu___6 =
                               universe_of g x0.FStar_Syntax_Syntax.sort in
                             op_let_Bang uu___6
                               (fun u ->
                                  let uu___7 =
                                    let uu___8 =
                                      FStar_Syntax_Syntax.mk_binder x0 in
                                    open_term g uu___8 f0 in
                                  match uu___7 with
                                  | (g1, b, f01) ->
                                      let f11 =
                                        FStar_Syntax_Subst.subst
                                          [FStar_Syntax_Syntax.DB
                                             (Prims.int_zero,
                                               (b.FStar_Syntax_Syntax.binder_bv))]
                                          f1 in
                                      op_let_Bang guard_not_allowed
                                        (fun uu___8 ->
                                           if uu___8
                                           then
                                             let uu___9 =
                                               check_relation1 g1 EQUALITY
                                                 f01 f11 in
                                             with_binders [b] [u] uu___9
                                           else
                                             (match rel with
                                              | EQUALITY ->
                                                  let uu___10 =
                                                    let uu___11 =
                                                      check_relation1 g1
                                                        EQUALITY f01 f11 in
                                                    handle_with uu___11
                                                      (fun uu___12 ->
                                                         let uu___13 =
                                                           FStar_Syntax_Util.mk_iff
                                                             f01 f11 in
                                                         guard uu___13) in
                                                  with_binders [b] [u]
                                                    uu___10
                                              | SUBTYPING
                                                  (FStar_Pervasives_Native.Some
                                                  tm) ->
                                                  let uu___10 =
                                                    let uu___11 =
                                                      FStar_Syntax_Util.mk_imp
                                                        f01 f11 in
                                                    FStar_Syntax_Subst.subst
                                                      [FStar_Syntax_Syntax.NT
                                                         ((b.FStar_Syntax_Syntax.binder_bv),
                                                           tm)] uu___11 in
                                                  guard uu___10
                                              | SUBTYPING
                                                  (FStar_Pervasives_Native.None)
                                                  ->
                                                  let uu___10 =
                                                    let uu___11 =
                                                      FStar_Syntax_Util.mk_imp
                                                        f01 f11 in
                                                    FStar_Syntax_Util.mk_forall
                                                      u
                                                      b.FStar_Syntax_Syntax.binder_bv
                                                      uu___11 in
                                                  guard uu___10))))
                      else
                        (let uu___5 =
                           maybe_unfold x0.FStar_Syntax_Syntax.sort
                             x1.FStar_Syntax_Syntax.sort in
                         match uu___5 with
                         | FStar_Pervasives_Native.None -> fallback t01 t11
                         | FStar_Pervasives_Native.Some (t02, t12) ->
                             let lhs =
                               FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_refine
                                    ({
                                       FStar_Syntax_Syntax.ppname =
                                         (x0.FStar_Syntax_Syntax.ppname);
                                       FStar_Syntax_Syntax.index =
                                         (x0.FStar_Syntax_Syntax.index);
                                       FStar_Syntax_Syntax.sort = t02
                                     }, f0)) t02.FStar_Syntax_Syntax.pos in
                             let rhs =
                               FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_refine
                                    ({
                                       FStar_Syntax_Syntax.ppname =
                                         (x1.FStar_Syntax_Syntax.ppname);
                                       FStar_Syntax_Syntax.index =
                                         (x1.FStar_Syntax_Syntax.index);
                                       FStar_Syntax_Syntax.sort = t12
                                     }, f1)) t12.FStar_Syntax_Syntax.pos in
                             let uu___6 =
                               FStar_Syntax_Util.flatten_refinement lhs in
                             let uu___7 =
                               FStar_Syntax_Util.flatten_refinement rhs in
                             check_relation1 g rel uu___6 uu___7)
                  | (FStar_Syntax_Syntax.Tm_refine (x0, f0), uu___3) ->
                      let uu___4 =
                        head_matches x0.FStar_Syntax_Syntax.sort t11 in
                      if uu___4
                      then
                        check_relation1 g rel x0.FStar_Syntax_Syntax.sort t11
                      else
                        (let uu___6 =
                           maybe_unfold x0.FStar_Syntax_Syntax.sort t11 in
                         match uu___6 with
                         | FStar_Pervasives_Native.None -> fallback t01 t11
                         | FStar_Pervasives_Native.Some (t02, t12) ->
                             let lhs =
                               FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_refine
                                    ({
                                       FStar_Syntax_Syntax.ppname =
                                         (x0.FStar_Syntax_Syntax.ppname);
                                       FStar_Syntax_Syntax.index =
                                         (x0.FStar_Syntax_Syntax.index);
                                       FStar_Syntax_Syntax.sort = t02
                                     }, f0)) t02.FStar_Syntax_Syntax.pos in
                             let uu___7 =
                               FStar_Syntax_Util.flatten_refinement lhs in
                             check_relation1 g rel uu___7 t12)
                  | (uu___3, FStar_Syntax_Syntax.Tm_refine (x1, f1)) ->
                      let uu___4 =
                        head_matches t01 x1.FStar_Syntax_Syntax.sort in
                      if uu___4
                      then
                        let uu___5 =
                          universe_of g x1.FStar_Syntax_Syntax.sort in
                        op_let_Bang uu___5
                          (fun u1 ->
                             let uu___6 =
                               check_relation1 g EQUALITY t01
                                 x1.FStar_Syntax_Syntax.sort in
                             op_let_Bang uu___6
                               (fun uu___7 ->
                                  let uu___8 =
                                    let uu___9 =
                                      FStar_Syntax_Syntax.mk_binder x1 in
                                    open_term g uu___9 f1 in
                                  match uu___8 with
                                  | (g1, b1, f11) ->
                                      op_let_Bang guard_not_allowed
                                        (fun uu___9 ->
                                           if uu___9
                                           then
                                             let uu___10 =
                                               check_relation1 g1 EQUALITY
                                                 FStar_Syntax_Util.t_true f11 in
                                             with_binders [b1] [u1] uu___10
                                           else
                                             (match rel with
                                              | EQUALITY ->
                                                  let uu___11 =
                                                    let uu___12 =
                                                      check_relation1 g1
                                                        EQUALITY
                                                        FStar_Syntax_Util.t_true
                                                        f11 in
                                                    handle_with uu___12
                                                      (fun uu___13 ->
                                                         guard f11) in
                                                  with_binders [b1] [u1]
                                                    uu___11
                                              | SUBTYPING
                                                  (FStar_Pervasives_Native.Some
                                                  tm) ->
                                                  let uu___11 =
                                                    FStar_Syntax_Subst.subst
                                                      [FStar_Syntax_Syntax.NT
                                                         ((b1.FStar_Syntax_Syntax.binder_bv),
                                                           tm)] f11 in
                                                  guard uu___11
                                              | SUBTYPING
                                                  (FStar_Pervasives_Native.None)
                                                  ->
                                                  let uu___11 =
                                                    FStar_Syntax_Util.mk_forall
                                                      u1
                                                      b1.FStar_Syntax_Syntax.binder_bv
                                                      f11 in
                                                  guard uu___11))))
                      else
                        (let uu___6 =
                           maybe_unfold t01 x1.FStar_Syntax_Syntax.sort in
                         match uu___6 with
                         | FStar_Pervasives_Native.None -> fallback t01 t11
                         | FStar_Pervasives_Native.Some (t02, t12) ->
                             let rhs =
                               FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_refine
                                    ({
                                       FStar_Syntax_Syntax.ppname =
                                         (x1.FStar_Syntax_Syntax.ppname);
                                       FStar_Syntax_Syntax.index =
                                         (x1.FStar_Syntax_Syntax.index);
                                       FStar_Syntax_Syntax.sort = t12
                                     }, f1)) t12.FStar_Syntax_Syntax.pos in
                             let uu___7 =
                               FStar_Syntax_Util.flatten_refinement rhs in
                             check_relation1 g rel t02 uu___7)
                  | (FStar_Syntax_Syntax.Tm_uinst uu___3, uu___4) ->
                      let head_matches1 = head_matches t01 t11 in
                      let uu___5 =
                        FStar_Syntax_Util.leftmost_head_and_args t01 in
                      (match uu___5 with
                       | (head0, args0) ->
                           let uu___6 =
                             FStar_Syntax_Util.leftmost_head_and_args t11 in
                           (match uu___6 with
                            | (head1, args1) ->
                                if
                                  Prims.op_Negation
                                    (head_matches1 &&
                                       ((FStar_Compiler_List.length args0) =
                                          (FStar_Compiler_List.length args1)))
                                then maybe_unfold_and_retry t01 t11
                                else
                                  (let uu___8 =
                                     let uu___9 =
                                       check_relation1 g EQUALITY head0 head1 in
                                     op_let_Bang uu___9
                                       (fun uu___10 ->
                                          check_relation_args g EQUALITY
                                            args0 args1) in
                                   handle_with uu___8
                                     (fun uu___9 ->
                                        maybe_unfold_side_and_retry Both t01
                                          t11))))
                  | (FStar_Syntax_Syntax.Tm_fvar uu___3, uu___4) ->
                      let head_matches1 = head_matches t01 t11 in
                      let uu___5 =
                        FStar_Syntax_Util.leftmost_head_and_args t01 in
                      (match uu___5 with
                       | (head0, args0) ->
                           let uu___6 =
                             FStar_Syntax_Util.leftmost_head_and_args t11 in
                           (match uu___6 with
                            | (head1, args1) ->
                                if
                                  Prims.op_Negation
                                    (head_matches1 &&
                                       ((FStar_Compiler_List.length args0) =
                                          (FStar_Compiler_List.length args1)))
                                then maybe_unfold_and_retry t01 t11
                                else
                                  (let uu___8 =
                                     let uu___9 =
                                       check_relation1 g EQUALITY head0 head1 in
                                     op_let_Bang uu___9
                                       (fun uu___10 ->
                                          check_relation_args g EQUALITY
                                            args0 args1) in
                                   handle_with uu___8
                                     (fun uu___9 ->
                                        maybe_unfold_side_and_retry Both t01
                                          t11))))
                  | (FStar_Syntax_Syntax.Tm_app uu___3, uu___4) ->
                      let head_matches1 = head_matches t01 t11 in
                      let uu___5 =
                        FStar_Syntax_Util.leftmost_head_and_args t01 in
                      (match uu___5 with
                       | (head0, args0) ->
                           let uu___6 =
                             FStar_Syntax_Util.leftmost_head_and_args t11 in
                           (match uu___6 with
                            | (head1, args1) ->
                                if
                                  Prims.op_Negation
                                    (head_matches1 &&
                                       ((FStar_Compiler_List.length args0) =
                                          (FStar_Compiler_List.length args1)))
                                then maybe_unfold_and_retry t01 t11
                                else
                                  (let uu___8 =
                                     let uu___9 =
                                       check_relation1 g EQUALITY head0 head1 in
                                     op_let_Bang uu___9
                                       (fun uu___10 ->
                                          check_relation_args g EQUALITY
                                            args0 args1) in
                                   handle_with uu___8
                                     (fun uu___9 ->
                                        maybe_unfold_side_and_retry Both t01
                                          t11))))
                  | (uu___3, FStar_Syntax_Syntax.Tm_uinst uu___4) ->
                      let head_matches1 = head_matches t01 t11 in
                      let uu___5 =
                        FStar_Syntax_Util.leftmost_head_and_args t01 in
                      (match uu___5 with
                       | (head0, args0) ->
                           let uu___6 =
                             FStar_Syntax_Util.leftmost_head_and_args t11 in
                           (match uu___6 with
                            | (head1, args1) ->
                                if
                                  Prims.op_Negation
                                    (head_matches1 &&
                                       ((FStar_Compiler_List.length args0) =
                                          (FStar_Compiler_List.length args1)))
                                then maybe_unfold_and_retry t01 t11
                                else
                                  (let uu___8 =
                                     let uu___9 =
                                       check_relation1 g EQUALITY head0 head1 in
                                     op_let_Bang uu___9
                                       (fun uu___10 ->
                                          check_relation_args g EQUALITY
                                            args0 args1) in
                                   handle_with uu___8
                                     (fun uu___9 ->
                                        maybe_unfold_side_and_retry Both t01
                                          t11))))
                  | (uu___3, FStar_Syntax_Syntax.Tm_fvar uu___4) ->
                      let head_matches1 = head_matches t01 t11 in
                      let uu___5 =
                        FStar_Syntax_Util.leftmost_head_and_args t01 in
                      (match uu___5 with
                       | (head0, args0) ->
                           let uu___6 =
                             FStar_Syntax_Util.leftmost_head_and_args t11 in
                           (match uu___6 with
                            | (head1, args1) ->
                                if
                                  Prims.op_Negation
                                    (head_matches1 &&
                                       ((FStar_Compiler_List.length args0) =
                                          (FStar_Compiler_List.length args1)))
                                then maybe_unfold_and_retry t01 t11
                                else
                                  (let uu___8 =
                                     let uu___9 =
                                       check_relation1 g EQUALITY head0 head1 in
                                     op_let_Bang uu___9
                                       (fun uu___10 ->
                                          check_relation_args g EQUALITY
                                            args0 args1) in
                                   handle_with uu___8
                                     (fun uu___9 ->
                                        maybe_unfold_side_and_retry Both t01
                                          t11))))
                  | (uu___3, FStar_Syntax_Syntax.Tm_app uu___4) ->
                      let head_matches1 = head_matches t01 t11 in
                      let uu___5 =
                        FStar_Syntax_Util.leftmost_head_and_args t01 in
                      (match uu___5 with
                       | (head0, args0) ->
                           let uu___6 =
                             FStar_Syntax_Util.leftmost_head_and_args t11 in
                           (match uu___6 with
                            | (head1, args1) ->
                                if
                                  Prims.op_Negation
                                    (head_matches1 &&
                                       ((FStar_Compiler_List.length args0) =
                                          (FStar_Compiler_List.length args1)))
                                then maybe_unfold_and_retry t01 t11
                                else
                                  (let uu___8 =
                                     let uu___9 =
                                       check_relation1 g EQUALITY head0 head1 in
                                     op_let_Bang uu___9
                                       (fun uu___10 ->
                                          check_relation_args g EQUALITY
                                            args0 args1) in
                                   handle_with uu___8
                                     (fun uu___9 ->
                                        maybe_unfold_side_and_retry Both t01
                                          t11))))
                  | (FStar_Syntax_Syntax.Tm_abs (b0::b1::bs, body, ropt),
                     uu___3) ->
                      let t02 = curry_abs b0 b1 bs body ropt in
                      check_relation1 g rel t02 t11
                  | (uu___3, FStar_Syntax_Syntax.Tm_abs
                     (b0::b1::bs, body, ropt)) ->
                      let t12 = curry_abs b0 b1 bs body ropt in
                      check_relation1 g rel t01 t12
                  | (FStar_Syntax_Syntax.Tm_abs (b0::[], body0, uu___3),
                     FStar_Syntax_Syntax.Tm_abs (b1::[], body1, uu___4)) ->
                      let uu___5 =
                        check_relation1 g EQUALITY
                          (b0.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort
                          (b1.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                      op_let_Bang uu___5
                        (fun uu___6 ->
                           let uu___7 =
                             check_bqual b0.FStar_Syntax_Syntax.binder_qual
                               b1.FStar_Syntax_Syntax.binder_qual in
                           op_let_Bang uu___7
                             (fun uu___8 ->
                                let uu___9 =
                                  universe_of g
                                    (b0.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                                op_let_Bang uu___9
                                  (fun u ->
                                     let uu___10 = open_term g b0 body0 in
                                     match uu___10 with
                                     | (g1, b01, body01) ->
                                         let body11 =
                                           FStar_Syntax_Subst.subst
                                             [FStar_Syntax_Syntax.DB
                                                (Prims.int_zero,
                                                  (b01.FStar_Syntax_Syntax.binder_bv))]
                                             body1 in
                                         let uu___11 =
                                           check_relation1 g1 EQUALITY body01
                                             body11 in
                                         with_binders [b01] [u] uu___11)))
                  | (FStar_Syntax_Syntax.Tm_arrow (x0::x1::xs, c0), uu___3)
                      ->
                      let uu___4 = curry_arrow x0 (x1 :: xs) c0 in
                      check_relation1 g rel uu___4 t11
                  | (uu___3, FStar_Syntax_Syntax.Tm_arrow (x0::x1::xs, c1))
                      ->
                      let uu___4 = curry_arrow x0 (x1 :: xs) c1 in
                      check_relation1 g rel t01 uu___4
                  | (FStar_Syntax_Syntax.Tm_arrow (x0::[], c0),
                     FStar_Syntax_Syntax.Tm_arrow (x1::[], c1)) ->
                      with_context "subtype arrow"
                        FStar_Pervasives_Native.None
                        (fun uu___3 ->
                           let uu___4 =
                             check_bqual x0.FStar_Syntax_Syntax.binder_qual
                               x1.FStar_Syntax_Syntax.binder_qual in
                           op_let_Bang uu___4
                             (fun uu___5 ->
                                let uu___6 =
                                  universe_of g
                                    (x1.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                                op_let_Bang uu___6
                                  (fun u1 ->
                                     let uu___7 = open_comp g x1 c1 in
                                     match uu___7 with
                                     | (g_x1, x11, c11) ->
                                         let c01 =
                                           FStar_Syntax_Subst.subst_comp
                                             [FStar_Syntax_Syntax.DB
                                                (Prims.int_zero,
                                                  (x11.FStar_Syntax_Syntax.binder_bv))]
                                             c0 in
                                         let uu___8 =
                                           let rel_arg =
                                             match rel with
                                             | EQUALITY -> EQUALITY
                                             | uu___9 ->
                                                 let uu___10 =
                                                   let uu___11 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       x11.FStar_Syntax_Syntax.binder_bv in
                                                   FStar_Pervasives_Native.Some
                                                     uu___11 in
                                                 SUBTYPING uu___10 in
                                           let rel_comp =
                                             match rel with
                                             | EQUALITY -> EQUALITY
                                             | SUBTYPING e ->
                                                 let uu___9 =
                                                   let uu___10 =
                                                     FStar_Syntax_Util.is_pure_or_ghost_comp
                                                       c01 in
                                                   if uu___10
                                                   then
                                                     op_let_Question e
                                                       (fun e1 ->
                                                          let uu___11 =
                                                            let uu___12 =
                                                              let uu___13 =
                                                                FStar_Syntax_Util.args_of_binders
                                                                  [x11] in
                                                              FStar_Pervasives_Native.snd
                                                                uu___13 in
                                                            FStar_Syntax_Syntax.mk_Tm_app
                                                              e1 uu___12
                                                              FStar_Compiler_Range.dummyRange in
                                                          FStar_Pervasives_Native.Some
                                                            uu___11)
                                                   else
                                                     FStar_Pervasives_Native.None in
                                                 SUBTYPING uu___9 in
                                           let uu___9 =
                                             check_relation1 g rel
                                               (x11.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort
                                               (x0.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                                           op_let_Bang uu___9
                                             (fun uu___10 ->
                                                with_context "check_subcomp"
                                                  FStar_Pervasives_Native.None
                                                  (fun uu___11 ->
                                                     check_relation_comp g_x1
                                                       rel_comp c01 c11)) in
                                         with_binders [x11] [u1] uu___8)))
                  | (FStar_Syntax_Syntax.Tm_match (e0, uu___3, brs0, uu___4),
                     FStar_Syntax_Syntax.Tm_match (e1, uu___5, brs1, uu___6))
                      ->
                      let relate_branch br0 br1 uu___7 =
                        match (br0, br1) with
                        | ((p0, FStar_Pervasives_Native.None, body0),
                           (p1, FStar_Pervasives_Native.None, body1)) ->
                            let uu___8 =
                              let uu___9 = FStar_Syntax_Syntax.eq_pat p0 p1 in
                              Prims.op_Negation uu___9 in
                            if uu___8
                            then fail "patterns not equal"
                            else
                              (let uu___10 =
                                 open_branches_eq_pat g
                                   (p0, FStar_Pervasives_Native.None, body0)
                                   (p1, FStar_Pervasives_Native.None, body1) in
                               match uu___10 with
                               | (g', (p01, uu___11, body01),
                                  (p11, uu___12, body11)) ->
                                   let uu___13 =
                                     FStar_TypeChecker_PatternUtils.raw_pat_as_exp
                                       g.tcenv p01 in
                                   (match uu___13 with
                                    | FStar_Pervasives_Native.Some
                                        (uu___14, bvs0) ->
                                        let bs0 =
                                          FStar_Compiler_List.map
                                            FStar_Syntax_Syntax.mk_binder
                                            bvs0 in
                                        let uu___15 = check_binders g bs0 in
                                        op_let_Bang uu___15
                                          (fun us ->
                                             let uu___16 =
                                               check_relation1 g' rel body01
                                                 body11 in
                                             with_binders bs0 us uu___16)
                                    | uu___14 ->
                                        fail
                                          "raw_pat_as_exp failed in check_equality match rule"))
                        | uu___8 ->
                            fail "Core does not support branches with when" in
                      let uu___7 =
                        let uu___8 = check_relation1 g EQUALITY e0 e1 in
                        op_let_Bang uu___8
                          (fun uu___9 -> iter2 brs0 brs1 relate_branch ()) in
                      handle_with uu___7 (fun uu___8 -> fallback t01 t11)
                  | uu___3 -> fallback t01 t11))
and (check_relation_args :
  env ->
    relation ->
      FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> unit result)
  =
  fun g ->
    fun rel ->
      fun a0 ->
        fun a1 ->
          if
            (FStar_Compiler_List.length a0) = (FStar_Compiler_List.length a1)
          then
            iter2 a0 a1
              (fun uu___ ->
                 fun uu___1 ->
                   fun uu___2 ->
                     match (uu___, uu___1) with
                     | ((t0, q0), (t1, q1)) ->
                         let uu___3 = check_aqual q0 q1 in
                         op_let_Bang uu___3
                           (fun uu___4 -> check_relation g rel t0 t1)) ()
          else fail "Unequal number of arguments"
and (check_relation_comp :
  env ->
    relation ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp -> unit result)
  =
  fun g ->
    fun rel ->
      fun c0 ->
        fun c1 ->
          let destruct_comp c =
            let uu___ = FStar_Syntax_Util.is_total_comp c in
            if uu___
            then
              FStar_Pervasives_Native.Some
                (E_TOTAL, (FStar_Syntax_Util.comp_result c))
            else
              (let uu___2 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
               if uu___2
               then
                 FStar_Pervasives_Native.Some
                   (E_GHOST, (FStar_Syntax_Util.comp_result c))
               else FStar_Pervasives_Native.None) in
          let uu___ =
            let uu___1 = destruct_comp c0 in
            let uu___2 = destruct_comp c1 in (uu___1, uu___2) in
          match uu___ with
          | (FStar_Pervasives_Native.None, uu___1) ->
              let uu___2 =
                let uu___3 = FStar_Syntax_Util.eq_comp c0 c1 in
                uu___3 = FStar_Syntax_Util.Equal in
              if uu___2
              then return ()
              else
                (let ct_eq ct0 ct1 =
                   let uu___4 =
                     check_relation g EQUALITY
                       ct0.FStar_Syntax_Syntax.result_typ
                       ct1.FStar_Syntax_Syntax.result_typ in
                   op_let_Bang uu___4
                     (fun uu___5 ->
                        check_relation_args g EQUALITY
                          ct0.FStar_Syntax_Syntax.effect_args
                          ct1.FStar_Syntax_Syntax.effect_args) in
                 let ct0 = FStar_Syntax_Util.comp_to_comp_typ_nouniv c0 in
                 let ct1 = FStar_Syntax_Util.comp_to_comp_typ_nouniv c1 in
                 let uu___4 =
                   FStar_Ident.lid_equals ct0.FStar_Syntax_Syntax.effect_name
                     ct1.FStar_Syntax_Syntax.effect_name in
                 if uu___4
                 then ct_eq ct0 ct1
                 else
                   (let ct01 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev g.tcenv c0 in
                    let ct11 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev g.tcenv c1 in
                    let uu___6 =
                      FStar_Ident.lid_equals
                        ct01.FStar_Syntax_Syntax.effect_name
                        ct11.FStar_Syntax_Syntax.effect_name in
                    if uu___6
                    then ct_eq ct01 ct11
                    else
                      (let uu___8 =
                         let uu___9 =
                           FStar_Ident.string_of_lid
                             ct01.FStar_Syntax_Syntax.effect_name in
                         let uu___10 =
                           FStar_Ident.string_of_lid
                             ct11.FStar_Syntax_Syntax.effect_name in
                         FStar_Compiler_Util.format2
                           "Subcomp failed: Unequal computation types %s and %s"
                           uu___9 uu___10 in
                       fail uu___8)))
          | (uu___1, FStar_Pervasives_Native.None) ->
              let uu___2 =
                let uu___3 = FStar_Syntax_Util.eq_comp c0 c1 in
                uu___3 = FStar_Syntax_Util.Equal in
              if uu___2
              then return ()
              else
                (let ct_eq ct0 ct1 =
                   let uu___4 =
                     check_relation g EQUALITY
                       ct0.FStar_Syntax_Syntax.result_typ
                       ct1.FStar_Syntax_Syntax.result_typ in
                   op_let_Bang uu___4
                     (fun uu___5 ->
                        check_relation_args g EQUALITY
                          ct0.FStar_Syntax_Syntax.effect_args
                          ct1.FStar_Syntax_Syntax.effect_args) in
                 let ct0 = FStar_Syntax_Util.comp_to_comp_typ_nouniv c0 in
                 let ct1 = FStar_Syntax_Util.comp_to_comp_typ_nouniv c1 in
                 let uu___4 =
                   FStar_Ident.lid_equals ct0.FStar_Syntax_Syntax.effect_name
                     ct1.FStar_Syntax_Syntax.effect_name in
                 if uu___4
                 then ct_eq ct0 ct1
                 else
                   (let ct01 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev g.tcenv c0 in
                    let ct11 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev g.tcenv c1 in
                    let uu___6 =
                      FStar_Ident.lid_equals
                        ct01.FStar_Syntax_Syntax.effect_name
                        ct11.FStar_Syntax_Syntax.effect_name in
                    if uu___6
                    then ct_eq ct01 ct11
                    else
                      (let uu___8 =
                         let uu___9 =
                           FStar_Ident.string_of_lid
                             ct01.FStar_Syntax_Syntax.effect_name in
                         let uu___10 =
                           FStar_Ident.string_of_lid
                             ct11.FStar_Syntax_Syntax.effect_name in
                         FStar_Compiler_Util.format2
                           "Subcomp failed: Unequal computation types %s and %s"
                           uu___9 uu___10 in
                       fail uu___8)))
          | (FStar_Pervasives_Native.Some (E_TOTAL, t0),
             FStar_Pervasives_Native.Some (uu___1, t1)) ->
              check_relation g rel t0 t1
          | (FStar_Pervasives_Native.Some (E_GHOST, t0),
             FStar_Pervasives_Native.Some (E_GHOST, t1)) ->
              check_relation g rel t0 t1
          | (FStar_Pervasives_Native.Some (E_GHOST, t0),
             FStar_Pervasives_Native.Some (E_TOTAL, t1)) ->
              let uu___1 = non_informative g t1 in
              if uu___1
              then check_relation g rel t0 t1
              else fail "Expected a Total computation, but got Ghost"
and (check_subtype :
  env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          context -> (unit success, error) FStar_Pervasives.either)
  =
  fun g ->
    fun e ->
      fun t0 ->
        fun t1 ->
          fun ctx ->
            FStar_Profiling.profile
              (fun uu___ ->
                 let rel = SUBTYPING e in
                 let uu___1 =
                   with_context "check_subtype"
                     (FStar_Pervasives_Native.Some (CtxRel (t0, rel, t1)))
                     (fun uu___2 -> check_relation g rel t0 t1) in
                 uu___1 ctx) FStar_Pervasives_Native.None
              "FStar.TypeChecker.Core.check_subtype"
and (memo_check :
  env ->
    FStar_Syntax_Syntax.term ->
      (effect_label * FStar_Syntax_Syntax.typ) result)
  =
  fun g ->
    fun e ->
      let check_then_memo g1 e1 ctx =
        let r = let uu___ = check' g1 e1 in uu___ ctx in
        match r with
        | FStar_Pervasives.Inl (res, FStar_Pervasives_Native.None) ->
            (insert g1 e1 (res, FStar_Pervasives_Native.None); r)
        | FStar_Pervasives.Inl (res, FStar_Pervasives_Native.Some guard1) ->
            (match g1.guard_handler with
             | FStar_Pervasives_Native.None ->
                 (insert g1 e1 (res, (FStar_Pervasives_Native.Some guard1));
                  r)
             | FStar_Pervasives_Native.Some gh ->
                 let uu___ = gh g1.tcenv guard1 in
                 if uu___
                 then
                   let r1 = (res, FStar_Pervasives_Native.None) in
                   (insert g1 e1 r1; FStar_Pervasives.Inl r1)
                 else
                   (let uu___2 = fail "guard handler failed" in uu___2 ctx))
        | uu___ -> r in
      fun ctx ->
        if Prims.op_Negation g.should_read_cache
        then check_then_memo g e ctx
        else
          (let uu___1 = let uu___2 = lookup g e in uu___2 ctx in
           match uu___1 with
           | FStar_Pervasives.Inr uu___2 ->
               if FStar_Pervasives_Native.uu___is_Some g.guard_handler
               then
                 check_then_memo
                   {
                     tcenv = (g.tcenv);
                     allow_universe_instantiation =
                       (g.allow_universe_instantiation);
                     max_binder_index = (g.max_binder_index);
                     guard_handler = (g.guard_handler);
                     should_read_cache = false
                   } e ctx
               else check_then_memo g e ctx
           | FStar_Pervasives.Inl (et, FStar_Pervasives_Native.None) ->
               FStar_Pervasives.Inl (et, FStar_Pervasives_Native.None)
           | FStar_Pervasives.Inl (et, FStar_Pervasives_Native.Some pre) ->
               (match g.guard_handler with
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives.Inl
                      (et, (FStar_Pervasives_Native.Some pre))
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
      FStar_Syntax_Syntax.term ->
        (effect_label * FStar_Syntax_Syntax.typ) result)
  =
  fun msg ->
    fun g ->
      fun e ->
        with_context msg (FStar_Pervasives_Native.Some (CtxTerm e))
          (fun uu___ -> memo_check g e)
and (check' :
  env ->
    FStar_Syntax_Syntax.term ->
      (effect_label * FStar_Syntax_Syntax.typ) result)
  =
  fun g ->
    fun e ->
      let e1 = FStar_Syntax_Subst.compress e in
      match e1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_lazy
          { FStar_Syntax_Syntax.blob = uu___;
            FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
              uu___1;
            FStar_Syntax_Syntax.ltyp = uu___2;
            FStar_Syntax_Syntax.rng = uu___3;_}
          -> let uu___4 = FStar_Syntax_Util.unlazy e1 in check' g uu___4
      | FStar_Syntax_Syntax.Tm_lazy i ->
          return (E_TOTAL, (i.FStar_Syntax_Syntax.ltyp))
      | FStar_Syntax_Syntax.Tm_meta (t, uu___) -> memo_check g t
      | FStar_Syntax_Syntax.Tm_uvar (uv, s) ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_Syntax_Util.ctx_uvar_typ uv in
              FStar_Syntax_Subst.subst' s uu___2 in
            (E_TOTAL, uu___1) in
          return uu___
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu___ = FStar_TypeChecker_Env.try_lookup_bv g.tcenv x in
          (match uu___ with
           | FStar_Pervasives_Native.None ->
               let uu___1 =
                 let uu___2 = FStar_Syntax_Print.bv_to_string x in
                 FStar_Compiler_Util.format1 "Variable not found: %s" uu___2 in
               fail uu___1
           | FStar_Pervasives_Native.Some (t, uu___1) -> return (E_TOTAL, t))
      | FStar_Syntax_Syntax.Tm_fvar f ->
          let uu___ =
            FStar_TypeChecker_Env.try_lookup_lid g.tcenv
              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu___ with
           | FStar_Pervasives_Native.Some (([], t), uu___1) ->
               return (E_TOTAL, t)
           | uu___1 -> fail "Missing universes instantiation")
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
             FStar_Syntax_Syntax.pos = uu___;
             FStar_Syntax_Syntax.vars = uu___1;
             FStar_Syntax_Syntax.hash_code = uu___2;_},
           us)
          ->
          let uu___3 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid g.tcenv us
              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu___3 with
           | FStar_Pervasives_Native.None ->
               let uu___4 =
                 let uu___5 =
                   FStar_Ident.string_of_lid
                     (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                 FStar_Compiler_Util.format1 "Top-level name not found: %s"
                   uu___5 in
               fail uu___4
           | FStar_Pervasives_Native.Some (t, uu___4) -> return (E_TOTAL, t))
      | FStar_Syntax_Syntax.Tm_constant c ->
          (match c with
           | FStar_Const.Const_range_of -> fail "Unhandled constant"
           | FStar_Const.Const_set_range_of -> fail "Unhandled constant"
           | FStar_Const.Const_reify -> fail "Unhandled constant"
           | FStar_Const.Const_reflect uu___ -> fail "Unhandled constant"
           | uu___ ->
               let t =
                 FStar_TypeChecker_TcTerm.tc_constant g.tcenv
                   e1.FStar_Syntax_Syntax.pos c in
               return (E_TOTAL, t))
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu___ =
            let uu___1 = mk_type (FStar_Syntax_Syntax.U_succ u) in
            (E_TOTAL, uu___1) in
          return uu___
      | FStar_Syntax_Syntax.Tm_refine (x, phi) ->
          let uu___ = check "refinement head" g x.FStar_Syntax_Syntax.sort in
          op_let_Bang uu___
            (fun uu___1 ->
               match uu___1 with
               | (uu___2, t) ->
                   let uu___3 = is_type g t in
                   op_let_Bang uu___3
                     (fun u ->
                        let uu___4 =
                          let uu___5 = FStar_Syntax_Syntax.mk_binder x in
                          open_term g uu___5 phi in
                        match uu___4 with
                        | (g', x1, phi1) ->
                            let uu___5 =
                              let uu___6 = check "refinement formula" g' phi1 in
                              op_let_Bang uu___6
                                (fun uu___7 ->
                                   match uu___7 with
                                   | (uu___8, t') ->
                                       let uu___9 = is_type g' t' in
                                       op_let_Bang uu___9
                                         (fun uu___10 -> return (E_TOTAL, t))) in
                            with_binders [x1] [u] uu___5))
      | FStar_Syntax_Syntax.Tm_abs (xs, body, uu___) ->
          let uu___1 = open_term_binders g xs body in
          (match uu___1 with
           | (g', xs1, body1) ->
               let uu___2 =
                 with_context "abs binders" FStar_Pervasives_Native.None
                   (fun uu___3 -> check_binders g xs1) in
               op_let_Bang uu___2
                 (fun us ->
                    let uu___3 =
                      let uu___4 = check "abs body" g' body1 in
                      op_let_Bang uu___4
                        (fun t ->
                           let uu___5 =
                             let uu___6 =
                               let uu___7 = as_comp g t in
                               FStar_Syntax_Util.arrow xs1 uu___7 in
                             (E_TOTAL, uu___6) in
                           return uu___5) in
                    with_binders xs1 us uu___3))
      | FStar_Syntax_Syntax.Tm_arrow (xs, c) ->
          let uu___ = open_comp_binders g xs c in
          (match uu___ with
           | (g', xs1, c1) ->
               let uu___1 =
                 with_context "arrow binders" FStar_Pervasives_Native.None
                   (fun uu___2 -> check_binders g xs1) in
               op_let_Bang uu___1
                 (fun us ->
                    let uu___2 =
                      let uu___3 =
                        with_context "arrow comp"
                          FStar_Pervasives_Native.None
                          (fun uu___4 -> check_comp g' c1) in
                      op_let_Bang uu___3
                        (fun u ->
                           let uu___4 =
                             let uu___5 =
                               mk_type (FStar_Syntax_Syntax.U_max (u :: us)) in
                             (E_TOTAL, uu___5) in
                           return uu___4) in
                    with_binders xs1 us uu___2))
      | FStar_Syntax_Syntax.Tm_app
          (hd,
           (t1, FStar_Pervasives_Native.None)::(t2,
                                                FStar_Pervasives_Native.None)::[])
          when FStar_TypeChecker_Util.short_circuit_head hd ->
          let uu___ = check "app head" g hd in
          op_let_Bang uu___
            (fun uu___1 ->
               match uu___1 with
               | (eff_hd, t_hd) ->
                   let uu___2 = is_arrow g t_hd in
                   op_let_Bang uu___2
                     (fun uu___3 ->
                        match uu___3 with
                        | (x, eff_arr1, s1) ->
                            let uu___4 = check "app arg" g t1 in
                            op_let_Bang uu___4
                              (fun uu___5 ->
                                 match uu___5 with
                                 | (eff_arg1, t_t1) ->
                                     let uu___6 =
                                       with_context "operator arg1"
                                         FStar_Pervasives_Native.None
                                         (fun uu___7 ->
                                            check_subtype g
                                              (FStar_Pervasives_Native.Some
                                                 t1) t_t1
                                              (x.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort) in
                                     op_let_Bang uu___6
                                       (fun uu___7 ->
                                          let s11 =
                                            FStar_Syntax_Subst.subst
                                              [FStar_Syntax_Syntax.NT
                                                 ((x.FStar_Syntax_Syntax.binder_bv),
                                                   t1)] s1 in
                                          let uu___8 = is_arrow g s11 in
                                          op_let_Bang uu___8
                                            (fun uu___9 ->
                                               match uu___9 with
                                               | (y, eff_arr2, s2) ->
                                                   let guard_formula =
                                                     FStar_TypeChecker_Util.short_circuit
                                                       hd
                                                       [(t1,
                                                          FStar_Pervasives_Native.None)] in
                                                   let g' =
                                                     match guard_formula with
                                                     | FStar_TypeChecker_Common.Trivial
                                                         -> g
                                                     | FStar_TypeChecker_Common.NonTrivial
                                                         gf ->
                                                         push_hypothesis g gf in
                                                   let uu___10 =
                                                     let uu___11 =
                                                       check "app arg" g' t2 in
                                                     weaken_with_guard_formula
                                                       guard_formula uu___11 in
                                                   op_let_Bang uu___10
                                                     (fun uu___11 ->
                                                        match uu___11 with
                                                        | (eff_arg2, t_t2) ->
                                                            let uu___12 =
                                                              with_context
                                                                "operator arg2"
                                                                FStar_Pervasives_Native.None
                                                                (fun uu___13
                                                                   ->
                                                                   check_subtype
                                                                    g'
                                                                    (FStar_Pervasives_Native.Some
                                                                    t2) t_t2
                                                                    (y.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort) in
                                                            op_let_Bang
                                                              uu___12
                                                              (fun uu___13 ->
                                                                 let uu___14
                                                                   =
                                                                   let uu___15
                                                                    =
                                                                    FStar_Syntax_Subst.subst
                                                                    [
                                                                    FStar_Syntax_Syntax.NT
                                                                    ((y.FStar_Syntax_Syntax.binder_bv),
                                                                    t2)] s2 in
                                                                   ((join_eff_l
                                                                    [eff_hd;
                                                                    eff_arr1;
                                                                    eff_arr2;
                                                                    eff_arg1;
                                                                    eff_arg2]),
                                                                    uu___15) in
                                                                 return
                                                                   uu___14)))))))
      | FStar_Syntax_Syntax.Tm_app (hd, (arg, arg_qual)::[]) ->
          let uu___ = check "app head" g hd in
          op_let_Bang uu___
            (fun uu___1 ->
               match uu___1 with
               | (eff_hd, t) ->
                   let uu___2 = is_arrow g t in
                   op_let_Bang uu___2
                     (fun uu___3 ->
                        match uu___3 with
                        | (x, eff_arr, t') ->
                            let uu___4 = check "app arg" g arg in
                            op_let_Bang uu___4
                              (fun uu___5 ->
                                 match uu___5 with
                                 | (eff_arg, t_arg) ->
                                     let uu___6 =
                                       with_context "app subtyping"
                                         FStar_Pervasives_Native.None
                                         (fun uu___7 ->
                                            check_subtype g
                                              (FStar_Pervasives_Native.Some
                                                 arg) t_arg
                                              (x.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort) in
                                     op_let_Bang uu___6
                                       (fun uu___7 ->
                                          let uu___8 =
                                            with_context "app arg qual"
                                              FStar_Pervasives_Native.None
                                              (fun uu___9 ->
                                                 check_arg_qual arg_qual
                                                   x.FStar_Syntax_Syntax.binder_qual) in
                                          op_let_Bang uu___8
                                            (fun uu___9 ->
                                               let uu___10 =
                                                 let uu___11 =
                                                   FStar_Syntax_Subst.subst
                                                     [FStar_Syntax_Syntax.NT
                                                        ((x.FStar_Syntax_Syntax.binder_bv),
                                                          arg)] t' in
                                                 ((join_eff eff_hd
                                                     (join_eff eff_arr
                                                        eff_arg)), uu___11) in
                                               return uu___10)))))
      | FStar_Syntax_Syntax.Tm_app (hd, arg::args) ->
          let head =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd, [arg]))
              e1.FStar_Syntax_Syntax.pos in
          let t =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (head, args))
              e1.FStar_Syntax_Syntax.pos in
          memo_check g t
      | FStar_Syntax_Syntax.Tm_ascribed
          (e2, (FStar_Pervasives.Inl t, uu___, eq), uu___1) ->
          let uu___2 = check "ascription head" g e2 in
          op_let_Bang uu___2
            (fun uu___3 ->
               match uu___3 with
               | (eff, te) ->
                   let uu___4 = check "ascription type" g t in
                   op_let_Bang uu___4
                     (fun uu___5 ->
                        match uu___5 with
                        | (uu___6, t') ->
                            let uu___7 = is_type g t' in
                            op_let_Bang uu___7
                              (fun uu___8 ->
                                 let uu___9 =
                                   with_context "ascription subtyping"
                                     FStar_Pervasives_Native.None
                                     (fun uu___10 ->
                                        check_subtype g
                                          (FStar_Pervasives_Native.Some e2)
                                          te t) in
                                 op_let_Bang uu___9
                                   (fun uu___10 -> return (eff, t)))))
      | FStar_Syntax_Syntax.Tm_ascribed
          (e2, (FStar_Pervasives.Inr c, uu___, uu___1), uu___2) ->
          let uu___3 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
          if uu___3
          then
            let uu___4 = check "ascription head" g e2 in
            op_let_Bang uu___4
              (fun uu___5 ->
                 match uu___5 with
                 | (eff, te) ->
                     let uu___6 =
                       with_context "ascription comp"
                         FStar_Pervasives_Native.None
                         (fun uu___7 -> check_comp g c) in
                     op_let_Bang uu___6
                       (fun uu___7 ->
                          let c_e = as_comp g (eff, te) in
                          let uu___8 =
                            check_relation_comp g
                              (SUBTYPING (FStar_Pervasives_Native.Some e2))
                              c_e c in
                          op_let_Bang uu___8
                            (fun uu___9 ->
                               let uu___10 = comp_as_effect_label_and_type c in
                               match uu___10 with
                               | FStar_Pervasives_Native.Some (eff1, t) ->
                                   return (eff1, t))))
          else
            (let uu___5 =
               let uu___6 = FStar_Syntax_Print.comp_to_string c in
               FStar_Compiler_Util.format1
                 "Effect ascriptions are not fully handled yet: %s" uu___6 in
             fail uu___5)
      | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) ->
          let uu___ = lb.FStar_Syntax_Syntax.lbname in
          (match uu___ with
           | FStar_Pervasives.Inl x ->
               let uu___1 =
                 let uu___2 = FStar_Syntax_Syntax.mk_binder x in
                 open_term g uu___2 body in
               (match uu___1 with
                | (g', x1, body1) ->
                    let uu___2 =
                      FStar_Ident.lid_equals lb.FStar_Syntax_Syntax.lbeff
                        FStar_Parser_Const.effect_Tot_lid in
                    if uu___2
                    then
                      let uu___3 =
                        check "let definition" g lb.FStar_Syntax_Syntax.lbdef in
                      op_let_Bang uu___3
                        (fun uu___4 ->
                           match uu___4 with
                           | (eff_def, tdef) ->
                               let uu___5 =
                                 check "let type" g
                                   lb.FStar_Syntax_Syntax.lbtyp in
                               op_let_Bang uu___5
                                 (fun uu___6 ->
                                    match uu___6 with
                                    | (uu___7, ttyp) ->
                                        let uu___8 = is_type g ttyp in
                                        op_let_Bang uu___8
                                          (fun u ->
                                             let uu___9 =
                                               with_context "let subtyping"
                                                 FStar_Pervasives_Native.None
                                                 (fun uu___10 ->
                                                    check_subtype g
                                                      (FStar_Pervasives_Native.Some
                                                         (lb.FStar_Syntax_Syntax.lbdef))
                                                      tdef ttyp) in
                                             op_let_Bang uu___9
                                               (fun uu___10 ->
                                                  let uu___11 =
                                                    let uu___12 =
                                                      check "let body" g'
                                                        body1 in
                                                    op_let_Bang uu___12
                                                      (fun uu___13 ->
                                                         match uu___13 with
                                                         | (eff_body, t) ->
                                                             let uu___14 =
                                                               check_no_escape
                                                                 [x1] t in
                                                             op_let_Bang
                                                               uu___14
                                                               (fun uu___15
                                                                  ->
                                                                  return
                                                                    ((join_eff
                                                                    eff_def
                                                                    eff_body),
                                                                    t))) in
                                                  with_definition x1 u
                                                    lb.FStar_Syntax_Syntax.lbdef
                                                    uu___11))))
                    else fail "Let binding is effectful"))
      | FStar_Syntax_Syntax.Tm_match
          (sc, FStar_Pervasives_Native.None, branches, rc_opt) ->
          let uu___ = check "scrutinee" g sc in
          op_let_Bang uu___
            (fun uu___1 ->
               match uu___1 with
               | (eff_sc, t_sc) ->
                   let uu___2 =
                     with_context "universe_of"
                       (FStar_Pervasives_Native.Some (CtxTerm t_sc))
                       (fun uu___3 -> universe_of g t_sc) in
                   op_let_Bang uu___2
                     (fun u_sc ->
                        let rec check_branches path_condition branch_typ_opt
                          branches1 =
                          match branches1 with
                          | [] ->
                              (match branch_typ_opt with
                               | FStar_Pervasives_Native.None ->
                                   fail
                                     "could not compute a type for the match"
                               | FStar_Pervasives_Native.Some et ->
                                   let uu___3 =
                                     let uu___4 =
                                       FStar_Syntax_Util.mk_imp
                                         path_condition
                                         FStar_Syntax_Util.t_false in
                                     guard uu___4 in
                                   op_let_Bang uu___3
                                     (fun uu___4 -> return et))
                          | (p, FStar_Pervasives_Native.None, b)::rest ->
                              let uu___3 =
                                open_branch g
                                  (p, FStar_Pervasives_Native.None, b) in
                              (match uu___3 with
                               | (g', (p1, uu___4, b1)) ->
                                   let uu___5 =
                                     FStar_TypeChecker_PatternUtils.raw_pat_as_exp
                                       g.tcenv p1 in
                                   (match uu___5 with
                                    | FStar_Pervasives_Native.None ->
                                        fail "Ill-formed pattern"
                                    | FStar_Pervasives_Native.Some (e2, bvs)
                                        ->
                                        let bs =
                                          FStar_Compiler_List.map
                                            FStar_Syntax_Syntax.mk_binder bvs in
                                        let uu___6 = check_binders g bs in
                                        op_let_Bang uu___6
                                          (fun us ->
                                             let msg =
                                               let uu___7 =
                                                 FStar_Syntax_Print.term_to_string
                                                   e2 in
                                               let uu___8 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   ", " bs in
                                               FStar_Compiler_Util.format2
                                                 "Checking pattern term %s in a conetxt with pattern binders %s\n"
                                                 uu___7 uu___8 in
                                             let uu___7 = check msg g' e2 in
                                             op_let_Bang uu___7
                                               (fun uu___8 ->
                                                  match uu___8 with
                                                  | (eff_pat, t) ->
                                                      let uu___9 =
                                                        with_context
                                                          "Pattern and scrutinee type compatibility"
                                                          FStar_Pervasives_Native.None
                                                          (fun uu___10 ->
                                                             let uu___11 =
                                                               check_scrutinee_pattern_type_compatible
                                                                 g' t_sc t in
                                                             no_guard uu___11) in
                                                      op_let_Bang uu___9
                                                        (fun uu___10 ->
                                                           let pat_sc_eq =
                                                             FStar_Syntax_Util.mk_eq2
                                                               u_sc t_sc sc
                                                               e2 in
                                                           let this_path_condition
                                                             =
                                                             FStar_Syntax_Util.mk_conj
                                                               path_condition
                                                               pat_sc_eq in
                                                           let g'1 =
                                                             push_hypothesis
                                                               g'
                                                               this_path_condition in
                                                           let uu___11 =
                                                             let uu___12 =
                                                               let uu___13 =
                                                                 let uu___14
                                                                   =
                                                                   with_context
                                                                    "branch"
                                                                    (FStar_Pervasives_Native.Some
                                                                    (CtxTerm
                                                                    b1))
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    check
                                                                    "branch"
                                                                    g'1 b1) in
                                                                 op_let_Bang
                                                                   uu___14
                                                                   (fun
                                                                    uu___15
                                                                    ->
                                                                    match uu___15
                                                                    with
                                                                    | 
                                                                    (eff_br,
                                                                    tbr) ->
                                                                    (match branch_typ_opt
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    let uu___16
                                                                    =
                                                                    check_no_escape
                                                                    bs tbr in
                                                                    op_let_Bang
                                                                    uu___16
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    return
                                                                    (eff_br,
                                                                    tbr))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (acc_eff,
                                                                    expect_tbr)
                                                                    ->
                                                                    let uu___16
                                                                    =
                                                                    with_context
                                                                    "check_branch_subtype"
                                                                    (FStar_Pervasives_Native.Some
                                                                    (CtxRel
                                                                    (tbr,
                                                                    (SUBTYPING
                                                                    (FStar_Pervasives_Native.Some
                                                                    b1)),
                                                                    expect_tbr)))
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    check_subtype
                                                                    g'1
                                                                    (FStar_Pervasives_Native.Some
                                                                    b1) tbr
                                                                    expect_tbr) in
                                                                    op_let_Bang
                                                                    uu___16
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    return
                                                                    ((join_eff
                                                                    eff_br
                                                                    acc_eff),
                                                                    expect_tbr)))) in
                                                               weaken
                                                                 this_path_condition
                                                                 uu___13 in
                                                             with_binders bs
                                                               us uu___12 in
                                                           op_let_Bang
                                                             uu___11
                                                             (fun uu___12 ->
                                                                match uu___12
                                                                with
                                                                | (eff_br,
                                                                   tbr) ->
                                                                    let path_condition1
                                                                    =
                                                                    let uu___13
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    FStar_Syntax_Util.mk_neg
                                                                    pat_sc_eq in
                                                                    mk_forall_l
                                                                    us bs
                                                                    uu___14 in
                                                                    FStar_Syntax_Util.mk_conj
                                                                    path_condition
                                                                    uu___13 in
                                                                    (match 
                                                                    p1.FStar_Syntax_Syntax.v
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Pat_var
                                                                    uu___13
                                                                    ->
                                                                    (match rest
                                                                    with
                                                                    | 
                                                                    uu___14::uu___15
                                                                    ->
                                                                    fail
                                                                    "Redundant branches after wildcard"
                                                                    | 
                                                                    uu___14
                                                                    ->
                                                                    return
                                                                    (eff_br,
                                                                    tbr))
                                                                    | 
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu___13
                                                                    ->
                                                                    (match rest
                                                                    with
                                                                    | 
                                                                    uu___14::uu___15
                                                                    ->
                                                                    fail
                                                                    "Redundant branches after wildcard"
                                                                    | 
                                                                    uu___14
                                                                    ->
                                                                    return
                                                                    (eff_br,
                                                                    tbr))
                                                                    | 
                                                                    uu___13
                                                                    ->
                                                                    check_branches
                                                                    path_condition1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (eff_br,
                                                                    tbr))
                                                                    rest))))))) in
                        let uu___3 =
                          match rc_opt with
                          | FStar_Pervasives_Native.Some
                              { FStar_Syntax_Syntax.residual_effect = uu___4;
                                FStar_Syntax_Syntax.residual_typ =
                                  FStar_Pervasives_Native.Some t;
                                FStar_Syntax_Syntax.residual_flags = uu___5;_}
                              ->
                              let uu___6 =
                                with_context "residual type"
                                  (FStar_Pervasives_Native.Some (CtxTerm t))
                                  (fun uu___7 -> universe_of g t) in
                              op_let_Bang uu___6
                                (fun uu___7 ->
                                   return
                                     (FStar_Pervasives_Native.Some
                                        (E_TOTAL, t)))
                          | uu___4 -> return FStar_Pervasives_Native.None in
                        op_let_Bang uu___3
                          (fun branch_typ_opt ->
                             let uu___4 =
                               let ctx =
                                 match branch_typ_opt with
                                 | FStar_Pervasives_Native.None ->
                                     FStar_Pervasives_Native.None
                                 | FStar_Pervasives_Native.Some (uu___5, t)
                                     ->
                                     FStar_Pervasives_Native.Some (CtxTerm t) in
                               with_context "check_branches" ctx
                                 (fun uu___5 ->
                                    check_branches FStar_Syntax_Util.t_true
                                      branch_typ_opt branches) in
                             op_let_Bang uu___4
                               (fun uu___5 ->
                                  match uu___5 with
                                  | (eff_br, t_br) ->
                                      return ((join_eff eff_sc eff_br), t_br)))))
      | FStar_Syntax_Syntax.Tm_match
          (sc, FStar_Pervasives_Native.Some
           (as_x,
            (FStar_Pervasives.Inl returns_ty, FStar_Pervasives_Native.None,
             eq)),
           branches, rc_opt)
          ->
          let uu___ = check "scrutinee" g sc in
          op_let_Bang uu___
            (fun uu___1 ->
               match uu___1 with
               | (eff_sc, t_sc) ->
                   let uu___2 =
                     with_context "universe_of"
                       (FStar_Pervasives_Native.Some (CtxTerm t_sc))
                       (fun uu___3 -> universe_of g t_sc) in
                   op_let_Bang uu___2
                     (fun u_sc ->
                        let as_x1 =
                          {
                            FStar_Syntax_Syntax.binder_bv =
                              (let uu___3 =
                                 as_x.FStar_Syntax_Syntax.binder_bv in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_sc
                               });
                            FStar_Syntax_Syntax.binder_qual =
                              (as_x.FStar_Syntax_Syntax.binder_qual);
                            FStar_Syntax_Syntax.binder_attrs =
                              (as_x.FStar_Syntax_Syntax.binder_attrs)
                          } in
                        let uu___3 = open_term g as_x1 returns_ty in
                        match uu___3 with
                        | (g_as_x, as_x2, returns_ty1) ->
                            let uu___4 =
                              check "return type" g_as_x returns_ty1 in
                            op_let_Bang uu___4
                              (fun uu___5 ->
                                 match uu___5 with
                                 | (_eff_t, returns_ty_t) ->
                                     let uu___6 = is_type g_as_x returns_ty_t in
                                     op_let_Bang uu___6
                                       (fun _u_ty ->
                                          let rec check_branches
                                            path_condition branches1 acc_eff
                                            =
                                            match branches1 with
                                            | [] ->
                                                let uu___7 =
                                                  let uu___8 =
                                                    FStar_Syntax_Util.mk_imp
                                                      path_condition
                                                      FStar_Syntax_Util.t_false in
                                                  guard uu___8 in
                                                op_let_Bang uu___7
                                                  (fun uu___8 ->
                                                     return acc_eff)
                                            | (p,
                                               FStar_Pervasives_Native.None,
                                               b)::rest ->
                                                let uu___7 =
                                                  open_branch g
                                                    (p,
                                                      FStar_Pervasives_Native.None,
                                                      b) in
                                                (match uu___7 with
                                                 | (g', (p1, uu___8, b1)) ->
                                                     let uu___9 =
                                                       FStar_TypeChecker_PatternUtils.raw_pat_as_exp
                                                         g.tcenv p1 in
                                                     (match uu___9 with
                                                      | FStar_Pervasives_Native.None
                                                          ->
                                                          fail
                                                            "Ill-formed pattern"
                                                      | FStar_Pervasives_Native.Some
                                                          (e2, bvs) ->
                                                          let bs =
                                                            FStar_Compiler_List.map
                                                              FStar_Syntax_Syntax.mk_binder
                                                              bvs in
                                                          let uu___10 =
                                                            check_binders g
                                                              bs in
                                                          op_let_Bang uu___10
                                                            (fun us ->
                                                               let uu___11 =
                                                                 check
                                                                   "pattern term"
                                                                   g' e2 in
                                                               op_let_Bang
                                                                 uu___11
                                                                 (fun uu___12
                                                                    ->
                                                                    match uu___12
                                                                    with
                                                                    | 
                                                                    (eff_pat,
                                                                    t) ->
                                                                    let uu___13
                                                                    =
                                                                    with_context
                                                                    "Pattern and scrutinee type compatibility"
                                                                    FStar_Pervasives_Native.None
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    no_guard
                                                                    (check_subtype
                                                                    g'
                                                                    (FStar_Pervasives_Native.Some
                                                                    e2) t_sc
                                                                    t)) in
                                                                    op_let_Bang
                                                                    uu___13
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    let pat_sc_eq
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    u_sc t_sc
                                                                    sc e2 in
                                                                    let this_path_condition
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    path_condition
                                                                    pat_sc_eq in
                                                                    let g'1 =
                                                                    push_hypothesis
                                                                    g'
                                                                    this_path_condition in
                                                                    let uu___15
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    check
                                                                    "branch"
                                                                    g'1 b1 in
                                                                    op_let_Bang
                                                                    uu___18
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    match uu___19
                                                                    with
                                                                    | 
                                                                    (eff_br,
                                                                    tbr) ->
                                                                    let expect_tbr
                                                                    =
                                                                    FStar_Syntax_Subst.subst
                                                                    [
                                                                    FStar_Syntax_Syntax.NT
                                                                    ((as_x2.FStar_Syntax_Syntax.binder_bv),
                                                                    e2)]
                                                                    returns_ty1 in
                                                                    let rel =
                                                                    if eq
                                                                    then
                                                                    EQUALITY
                                                                    else
                                                                    SUBTYPING
                                                                    (FStar_Pervasives_Native.Some
                                                                    b1) in
                                                                    let uu___20
                                                                    =
                                                                    check_relation
                                                                    g'1 rel
                                                                    tbr
                                                                    expect_tbr in
                                                                    op_let_Bang
                                                                    uu___20
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    return
                                                                    ((join_eff
                                                                    eff_br
                                                                    acc_eff),
                                                                    expect_tbr))) in
                                                                    weaken
                                                                    this_path_condition
                                                                    uu___17 in
                                                                    with_binders
                                                                    bs us
                                                                    uu___16 in
                                                                    op_let_Bang
                                                                    uu___15
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    match uu___16
                                                                    with
                                                                    | 
                                                                    (eff_br,
                                                                    tbr) ->
                                                                    let path_condition1
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    FStar_Syntax_Util.mk_neg
                                                                    pat_sc_eq in
                                                                    mk_forall_l
                                                                    us bs
                                                                    uu___18 in
                                                                    FStar_Syntax_Util.mk_conj
                                                                    path_condition
                                                                    uu___17 in
                                                                    (match 
                                                                    p1.FStar_Syntax_Syntax.v
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Pat_var
                                                                    uu___17
                                                                    ->
                                                                    (match rest
                                                                    with
                                                                    | 
                                                                    uu___18::uu___19
                                                                    ->
                                                                    fail
                                                                    "Redundant branches after wildcard"
                                                                    | 
                                                                    uu___18
                                                                    ->
                                                                    return
                                                                    eff_br)
                                                                    | 
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu___17
                                                                    ->
                                                                    (match rest
                                                                    with
                                                                    | 
                                                                    uu___18::uu___19
                                                                    ->
                                                                    fail
                                                                    "Redundant branches after wildcard"
                                                                    | 
                                                                    uu___18
                                                                    ->
                                                                    return
                                                                    eff_br)
                                                                    | 
                                                                    uu___17
                                                                    ->
                                                                    check_branches
                                                                    path_condition1
                                                                    rest
                                                                    eff_br))))))) in
                                          let uu___7 =
                                            check_branches
                                              FStar_Syntax_Util.t_true
                                              branches E_TOTAL in
                                          op_let_Bang uu___7
                                            (fun eff ->
                                               let ty =
                                                 FStar_Syntax_Subst.subst
                                                   [FStar_Syntax_Syntax.NT
                                                      ((as_x2.FStar_Syntax_Syntax.binder_bv),
                                                        sc)] returns_ty1 in
                                               return (eff, ty))))))
      | FStar_Syntax_Syntax.Tm_match uu___ ->
          fail "Match with effect returns ascription, or tactic handler"
      | uu___ ->
          let uu___1 =
            let uu___2 = FStar_Syntax_Print.tag_of_term e1 in
            FStar_Compiler_Util.format1 "Unexpected term: %s" uu___2 in
          fail uu___1
and (check_binders :
  env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.universe Prims.list result)
  =
  fun g_initial ->
    fun xs ->
      let rec aux g xs1 =
        match xs1 with
        | [] -> return []
        | x::xs2 ->
            let uu___ =
              check "binder sort" g
                (x.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
            op_let_Bang uu___
              (fun uu___1 ->
                 match uu___1 with
                 | (uu___2, t) ->
                     let uu___3 = is_type g t in
                     op_let_Bang uu___3
                       (fun u ->
                          let uu___4 =
                            let uu___5 =
                              let uu___6 = push_binder g x in aux uu___6 xs2 in
                            op_let_Bang uu___5 (fun us -> return (u :: us)) in
                          with_binders [x] [u] uu___4)) in
      aux g_initial xs
and (check_comp :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.universe result) =
  fun g ->
    fun c ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total (t, uu___) ->
          let uu___1 =
            check "(G)Tot comp result" g (FStar_Syntax_Util.comp_result c) in
          op_let_Bang uu___1
            (fun uu___2 -> match uu___2 with | (uu___3, t1) -> is_type g t1)
      | FStar_Syntax_Syntax.GTotal (t, uu___) ->
          let uu___1 =
            check "(G)Tot comp result" g (FStar_Syntax_Util.comp_result c) in
          op_let_Bang uu___1
            (fun uu___2 -> match uu___2 with | (uu___3, t1) -> is_type g t1)
      | FStar_Syntax_Syntax.Comp ct ->
          if
            (FStar_Compiler_List.length ct.FStar_Syntax_Syntax.comp_univs) <>
              Prims.int_one
          then fail "Unexpected/missing universe instantitation in comp"
          else
            (let u = FStar_Compiler_List.hd ct.FStar_Syntax_Syntax.comp_univs in
             let effect_app_tm =
               let head =
                 let uu___1 =
                   FStar_Syntax_Syntax.fvar
                     ct.FStar_Syntax_Syntax.effect_name
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu___1 [u] in
               let uu___1 =
                 let uu___2 =
                   FStar_Syntax_Syntax.as_arg
                     ct.FStar_Syntax_Syntax.result_typ in
                 uu___2 :: (ct.FStar_Syntax_Syntax.effect_args) in
               FStar_Syntax_Syntax.mk_Tm_app head uu___1
                 (ct.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos in
             let uu___1 = check "effectful comp" g effect_app_tm in
             op_let_Bang uu___1
               (fun uu___2 ->
                  match uu___2 with
                  | (uu___3, t) ->
                      let uu___4 =
                        with_context "comp fully applied"
                          FStar_Pervasives_Native.None
                          (fun uu___5 ->
                             check_subtype g FStar_Pervasives_Native.None t
                               FStar_Syntax_Syntax.teff) in
                      op_let_Bang uu___4
                        (fun uu___5 ->
                           let c_lid =
                             FStar_TypeChecker_Env.norm_eff_name g.tcenv
                               ct.FStar_Syntax_Syntax.effect_name in
                           let is_total =
                             let uu___6 =
                               FStar_TypeChecker_Env.lookup_effect_quals
                                 g.tcenv c_lid in
                             FStar_Compiler_Effect.op_Bar_Greater uu___6
                               (FStar_Compiler_List.existsb
                                  (fun q ->
                                     q = FStar_Syntax_Syntax.TotalEffect)) in
                           if Prims.op_Negation is_total
                           then return FStar_Syntax_Syntax.U_zero
                           else
                             (let uu___7 =
                                FStar_Syntax_Util.is_pure_or_ghost_effect
                                  c_lid in
                              if uu___7
                              then return u
                              else
                                (let uu___9 =
                                   FStar_TypeChecker_Env.effect_repr 
                                     g.tcenv c u in
                                 match uu___9 with
                                 | FStar_Pervasives_Native.None ->
                                     let uu___10 =
                                       let uu___11 =
                                         FStar_Ident.string_of_lid
                                           (FStar_Syntax_Util.comp_effect_name
                                              c) in
                                       let uu___12 =
                                         FStar_Ident.string_of_lid c_lid in
                                       FStar_Compiler_Util.format2
                                         "Total effect %s (normalized to %s) does not have a representation"
                                         uu___11 uu___12 in
                                     fail uu___10
                                 | FStar_Pervasives_Native.Some tm ->
                                     universe_of g tm)))))
and (universe_of :
  env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.universe result) =
  fun g ->
    fun t ->
      let uu___ = check "universe of" g t in
      op_let_Bang uu___
        (fun uu___1 -> match uu___1 with | (uu___2, t1) -> is_type g t1)
and (check_scrutinee_pattern_type_compatible :
  env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> precondition result)
  =
  fun g ->
    fun t_sc ->
      fun t_pat ->
        let err s =
          let uu___ =
            let uu___1 = FStar_Syntax_Print.term_to_string t_sc in
            let uu___2 = FStar_Syntax_Print.term_to_string t_pat in
            FStar_Compiler_Util.format3
              "Scrutinee type %s and Pattern type %s are not compatible because %s"
              uu___1 uu___2 s in
          fail uu___ in
        let t_sc1 =
          let uu___ =
            FStar_Compiler_Effect.op_Bar_Greater t_sc
              (FStar_TypeChecker_Normalize.normalize_refinement
                 FStar_TypeChecker_Normalize.whnf_steps g.tcenv) in
          FStar_Compiler_Effect.op_Bar_Greater uu___
            FStar_Syntax_Util.unrefine in
        let uu___ = FStar_Syntax_Util.head_and_args t_sc1 in
        match uu___ with
        | (head_sc, args_sc) ->
            let uu___1 = FStar_Syntax_Util.head_and_args t_pat in
            (match uu___1 with
             | (head_pat, args_pat) ->
                 let uu___2 =
                   let uu___3 =
                     let uu___4 =
                       let uu___5 = FStar_Syntax_Subst.compress head_sc in
                       uu___5.FStar_Syntax_Syntax.n in
                     let uu___5 =
                       let uu___6 = FStar_Syntax_Subst.compress head_pat in
                       uu___6.FStar_Syntax_Syntax.n in
                     (uu___4, uu___5) in
                   match uu___3 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv_head,
                      FStar_Syntax_Syntax.Tm_fvar fv_pat) when
                       let uu___4 = FStar_Syntax_Syntax.lid_of_fv fv_head in
                       let uu___5 = FStar_Syntax_Syntax.lid_of_fv fv_pat in
                       FStar_Ident.lid_equals uu___4 uu___5 -> return fv_head
                   | (FStar_Syntax_Syntax.Tm_uinst
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv_head;
                         FStar_Syntax_Syntax.pos = uu___4;
                         FStar_Syntax_Syntax.vars = uu___5;
                         FStar_Syntax_Syntax.hash_code = uu___6;_},
                       us_head),
                      FStar_Syntax_Syntax.Tm_uinst
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv_pat;
                         FStar_Syntax_Syntax.pos = uu___7;
                         FStar_Syntax_Syntax.vars = uu___8;
                         FStar_Syntax_Syntax.hash_code = uu___9;_},
                       us_pat)) when
                       let uu___10 = FStar_Syntax_Syntax.lid_of_fv fv_head in
                       let uu___11 = FStar_Syntax_Syntax.lid_of_fv fv_pat in
                       FStar_Ident.lid_equals uu___10 uu___11 ->
                       let uu___10 =
                         FStar_TypeChecker_Rel.teq_nosmt_force g.tcenv
                           head_sc head_pat in
                       if uu___10
                       then return fv_head
                       else err "Incompatible universe instantiations"
                   | (uu___4, uu___5) ->
                       let uu___6 =
                         let uu___7 = FStar_Syntax_Print.tag_of_term head_sc in
                         let uu___8 = FStar_Syntax_Print.tag_of_term head_pat in
                         FStar_Compiler_Util.format2
                           "Head constructors(%s and %s) not fvar" uu___7
                           uu___8 in
                       err uu___6 in
                 op_let_Bang uu___2
                   (fun t_fv ->
                      let uu___3 =
                        let uu___4 =
                          let uu___5 = FStar_Syntax_Syntax.lid_of_fv t_fv in
                          FStar_TypeChecker_Env.is_type_constructor g.tcenv
                            uu___5 in
                        if uu___4
                        then return t_fv
                        else
                          (let uu___6 =
                             let uu___7 =
                               FStar_Syntax_Print.fv_to_string t_fv in
                             FStar_Compiler_Util.format1
                               "%s is not a type constructor" uu___7 in
                           err uu___6) in
                      op_let_Bang uu___3
                        (fun uu___4 ->
                           let uu___5 =
                             if
                               (FStar_Compiler_List.length args_sc) =
                                 (FStar_Compiler_List.length args_pat)
                             then return t_fv
                             else
                               (let uu___7 =
                                  let uu___8 =
                                    FStar_Compiler_Util.string_of_int
                                      (FStar_Compiler_List.length args_sc) in
                                  let uu___9 =
                                    FStar_Compiler_Util.string_of_int
                                      (FStar_Compiler_List.length args_pat) in
                                  FStar_Compiler_Util.format2
                                    "Number of arguments don't match (%s and %s)"
                                    uu___8 uu___9 in
                                err uu___7) in
                           op_let_Bang uu___5
                             (fun uu___6 ->
                                let uu___7 =
                                  let uu___8 =
                                    let uu___9 =
                                      FStar_Syntax_Syntax.lid_of_fv t_fv in
                                    FStar_TypeChecker_Env.num_inductive_ty_params
                                      g.tcenv uu___9 in
                                  match uu___8 with
                                  | FStar_Pervasives_Native.None ->
                                      (args_sc, args_pat)
                                  | FStar_Pervasives_Native.Some n ->
                                      let uu___9 =
                                        let uu___10 =
                                          FStar_Compiler_Util.first_N n
                                            args_sc in
                                        FStar_Pervasives_Native.fst uu___10 in
                                      let uu___10 =
                                        let uu___11 =
                                          FStar_Compiler_Util.first_N n
                                            args_pat in
                                        FStar_Pervasives_Native.fst uu___11 in
                                      (uu___9, uu___10) in
                                match uu___7 with
                                | (params_sc, params_pat) ->
                                    let uu___8 =
                                      iter2 params_sc params_pat
                                        (fun uu___9 ->
                                           fun uu___10 ->
                                             fun uu___11 ->
                                               match (uu___9, uu___10) with
                                               | ((t_sc2, uu___12),
                                                  (t_pat1, uu___13)) ->
                                                   check_relation g EQUALITY
                                                     t_sc2 t_pat1) () in
                                    op_let_Bang uu___8
                                      (fun uu___9 ->
                                         return FStar_Pervasives_Native.None)))))
let (initial_env :
  FStar_TypeChecker_Env.env ->
    guard_handler_t FStar_Pervasives_Native.option -> env)
  =
  fun g ->
    fun gh ->
      let max_index =
        FStar_Compiler_List.fold_left
          (fun index ->
             fun b ->
               match b with
               | FStar_Syntax_Syntax.Binding_var x ->
                   if x.FStar_Syntax_Syntax.index > index
                   then x.FStar_Syntax_Syntax.index
                   else index
               | uu___ -> index) Prims.int_zero g.FStar_TypeChecker_Env.gamma in
      {
        tcenv = g;
        allow_universe_instantiation = false;
        max_binder_index = max_index;
        guard_handler = gh;
        should_read_cache = true
      }
let (check_term_top :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
        Prims.bool ->
          guard_handler_t FStar_Pervasives_Native.option ->
            (effect_label * FStar_Syntax_Syntax.typ)
              FStar_Pervasives_Native.option result)
  =
  fun g ->
    fun e ->
      fun topt ->
        fun must_tot ->
          fun gh ->
            let g1 = initial_env g gh in
            let uu___ = check "top" g1 e in
            op_let_Bang uu___
              (fun eff_te ->
                 match topt with
                 | FStar_Pervasives_Native.None ->
                     return (FStar_Pervasives_Native.Some eff_te)
                 | FStar_Pervasives_Native.Some t ->
                     let target_comp =
                       if
                         must_tot ||
                           ((FStar_Pervasives_Native.fst eff_te) = E_TOTAL)
                       then FStar_Syntax_Syntax.mk_Total t
                       else FStar_Syntax_Syntax.mk_GTotal t in
                     let uu___1 =
                       with_context "top-level subtyping"
                         FStar_Pervasives_Native.None
                         (fun uu___2 ->
                            let uu___3 = as_comp g1 eff_te in
                            check_relation_comp
                              {
                                tcenv = (g1.tcenv);
                                allow_universe_instantiation = true;
                                max_binder_index = (g1.max_binder_index);
                                guard_handler = (g1.guard_handler);
                                should_read_cache = (g1.should_read_cache)
                              } (SUBTYPING (FStar_Pervasives_Native.Some e))
                              uu___3 target_comp) in
                     op_let_Bang uu___1
                       (fun uu___2 -> return FStar_Pervasives_Native.None))
let (simplify_steps : FStar_TypeChecker_Env.step Prims.list) =
  [FStar_TypeChecker_Env.Beta;
  FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant;
  FStar_TypeChecker_Env.UnfoldQual ["unfold"];
  FStar_TypeChecker_Env.UnfoldOnly
    [FStar_Parser_Const.pure_wp_monotonic_lid;
    FStar_Parser_Const.pure_wp_monotonic0_lid];
  FStar_TypeChecker_Env.Simplify;
  FStar_TypeChecker_Env.Primops;
  FStar_TypeChecker_Env.NoFullNorm]
let (check_term_top_gh :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
        Prims.bool ->
          guard_handler_t FStar_Pervasives_Native.option ->
            (((effect_label * FStar_Syntax_Syntax.typ)
               FStar_Pervasives_Native.option * precondition),
              error) FStar_Pervasives.either)
  =
  fun g ->
    fun e ->
      fun topt ->
        fun must_tot ->
          fun gh ->
            (let uu___1 =
               FStar_TypeChecker_Env.debug g (FStar_Options.Other "CoreEq") in
             if uu___1
             then
               let uu___2 =
                 let uu___3 = get_goal_ctr () in
                 FStar_Compiler_Util.string_of_int uu___3 in
               FStar_Compiler_Util.print1 "(%s) Entering core ... \n" uu___2
             else ());
            (let uu___2 =
               (FStar_TypeChecker_Env.debug g (FStar_Options.Other "Core"))
                 ||
                 (FStar_TypeChecker_Env.debug g
                    (FStar_Options.Other "CoreTop")) in
             if uu___2
             then
               let uu___3 =
                 let uu___4 = get_goal_ctr () in
                 FStar_Compiler_Util.string_of_int uu___4 in
               let uu___4 = FStar_Syntax_Print.term_to_string e in
               let uu___5 =
                 match topt with
                 | FStar_Pervasives_Native.None -> ""
                 | FStar_Pervasives_Native.Some t ->
                     FStar_Syntax_Print.term_to_string t in
               FStar_Compiler_Util.print3
                 "(%s) Entering core with %s <: %s\n" uu___3 uu___4 uu___5
             else ());
            FStar_Syntax_TermHashTable.reset_counters table;
            reset_cache_stats ();
            (let ctx = { no_guard = false; error_context = [] } in
             let res =
               FStar_Profiling.profile
                 (fun uu___4 ->
                    let uu___5 =
                      let uu___6 = check_term_top g e topt must_tot gh in
                      uu___6 ctx in
                    match uu___5 with
                    | FStar_Pervasives.Inl (et, g1) ->
                        FStar_Pervasives.Inl (et, g1)
                    | FStar_Pervasives.Inr err -> FStar_Pervasives.Inr err)
                 FStar_Pervasives_Native.None
                 "FStar.TypeChecker.Core.check_term_top" in
             let res1 =
               match res with
               | FStar_Pervasives.Inl
                   (et, FStar_Pervasives_Native.Some guard0) ->
                   let guard1 =
                     FStar_TypeChecker_Normalize.normalize simplify_steps g
                       guard0 in
                   ((let uu___5 =
                       ((FStar_TypeChecker_Env.debug g
                           (FStar_Options.Other "CoreExit"))
                          ||
                          (FStar_TypeChecker_Env.debug g
                             (FStar_Options.Other "Core")))
                         ||
                         (FStar_TypeChecker_Env.debug g
                            (FStar_Options.Other "CoreTop")) in
                     if uu___5
                     then
                       let uu___6 =
                         let uu___7 = get_goal_ctr () in
                         FStar_Compiler_Util.string_of_int uu___7 in
                       let uu___7 = FStar_Syntax_Print.term_to_string guard0 in
                       let uu___8 = FStar_Syntax_Print.term_to_string guard1 in
                       FStar_Compiler_Util.print3
                         "(%s) Exiting core: Simplified guard from {{%s}} to {{%s}}\n"
                         uu___6 uu___7 uu___8
                     else ());
                    FStar_Pervasives.Inl
                      (et, (FStar_Pervasives_Native.Some guard1)))
               | FStar_Pervasives.Inl uu___4 ->
                   ((let uu___6 =
                       (FStar_TypeChecker_Env.debug g
                          (FStar_Options.Other "Core"))
                         ||
                         (FStar_TypeChecker_Env.debug g
                            (FStar_Options.Other "CoreTop")) in
                     if uu___6
                     then
                       let uu___7 =
                         let uu___8 = get_goal_ctr () in
                         FStar_Compiler_Util.string_of_int uu___8 in
                       FStar_Compiler_Util.print1 "(%s) Exiting core (ok)\n"
                         uu___7
                     else ());
                    res)
               | FStar_Pervasives.Inr uu___4 ->
                   ((let uu___6 =
                       (FStar_TypeChecker_Env.debug g
                          (FStar_Options.Other "Core"))
                         ||
                         (FStar_TypeChecker_Env.debug g
                            (FStar_Options.Other "CoreTop")) in
                     if uu___6
                     then
                       let uu___7 =
                         let uu___8 = get_goal_ctr () in
                         FStar_Compiler_Util.string_of_int uu___8 in
                       FStar_Compiler_Util.print1
                         "(%s) Exiting core (failed)\n" uu___7
                     else ());
                    res) in
             (let uu___5 =
                FStar_TypeChecker_Env.debug g (FStar_Options.Other "CoreEq") in
              if uu___5
              then
                (FStar_Syntax_TermHashTable.print_stats table;
                 (let cs = report_cache_stats () in
                  let uu___7 = FStar_Compiler_Util.string_of_int cs.hits in
                  let uu___8 = FStar_Compiler_Util.string_of_int cs.misses in
                  FStar_Compiler_Util.print2
                    "Cache_stats { hits = %s; misses = %s }\n" uu___7 uu___8))
              else ());
             res1)
let (check_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        Prims.bool ->
          (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option, error)
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
          | FStar_Pervasives.Inl (uu___1, g1) -> FStar_Pervasives.Inl g1
          | FStar_Pervasives.Inr err -> FStar_Pervasives.Inr err
let (compute_term_type_handle_guards :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      Prims.bool ->
        (FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool)
          -> (FStar_Syntax_Syntax.typ, error) FStar_Pervasives.either)
  =
  fun g ->
    fun e ->
      fun must_tot ->
        fun gh ->
          let uu___ =
            check_term_top_gh g e FStar_Pervasives_Native.None must_tot
              (FStar_Pervasives_Native.Some gh) in
          match uu___ with
          | FStar_Pervasives.Inl
              (FStar_Pervasives_Native.Some (uu___1, t),
               FStar_Pervasives_Native.None)
              -> FStar_Pervasives.Inl t
          | FStar_Pervasives.Inl (FStar_Pervasives_Native.None, uu___1) ->
              failwith "Impossible: Success must return some effect and type"
          | FStar_Pervasives.Inl
              (uu___1, FStar_Pervasives_Native.Some uu___2) ->
              failwith
                "Impossible: All guards should have been handled already"
          | FStar_Pervasives.Inr err -> FStar_Pervasives.Inr err
let (open_binders_in_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term ->
        (FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.binders *
          FStar_Syntax_Syntax.term))
  =
  fun env1 ->
    fun bs ->
      fun t ->
        let g = initial_env env1 FStar_Pervasives_Native.None in
        let uu___ = open_term_binders g bs t in
        match uu___ with | (g', bs1, t1) -> ((g'.tcenv), bs1, t1)
let (open_binders_in_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.comp ->
        (FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.binders *
          FStar_Syntax_Syntax.comp))
  =
  fun env1 ->
    fun bs ->
      fun c ->
        let g = initial_env env1 FStar_Pervasives_Native.None in
        let uu___ = open_comp_binders g bs c in
        match uu___ with | (g', bs1, c1) -> ((g'.tcenv), bs1, c1)
let (check_term_equality :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option, error)
          FStar_Pervasives.either)
  =
  fun g ->
    fun t0 ->
      fun t1 ->
        let g1 = initial_env g FStar_Pervasives_Native.None in
        let ctx = { no_guard = false; error_context = [] } in
        let uu___ =
          let uu___1 = check_relation g1 EQUALITY t0 t1 in uu___1 ctx in
        match uu___ with
        | FStar_Pervasives.Inl (uu___1, g2) -> FStar_Pervasives.Inl g2
        | FStar_Pervasives.Inr err -> FStar_Pervasives.Inr err
let (check_term_subtyping :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option, error)
          FStar_Pervasives.either)
  =
  fun g ->
    fun t0 ->
      fun t1 ->
        let g1 = initial_env g FStar_Pervasives_Native.None in
        let ctx = { no_guard = false; error_context = [] } in
        let uu___ =
          let uu___1 =
            check_relation g1 (SUBTYPING FStar_Pervasives_Native.None) t0 t1 in
          uu___1 ctx in
        match uu___ with
        | FStar_Pervasives.Inl (uu___1, g2) -> FStar_Pervasives.Inl g2
        | FStar_Pervasives.Inr err -> FStar_Pervasives.Inr err