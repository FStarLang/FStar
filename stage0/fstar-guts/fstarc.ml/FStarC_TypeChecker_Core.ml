open Prims
type guard_commit_token_cb = unit -> unit
type guard_and_tok_t = (FStarC_Syntax_Syntax.typ * guard_commit_token_cb)
type tot_or_ghost =
  | E_Total 
  | E_Ghost 
let uu___is_E_Total (projectee : tot_or_ghost) : Prims.bool=
  match projectee with | E_Total -> true | uu___ -> false
let uu___is_E_Ghost (projectee : tot_or_ghost) : Prims.bool=
  match projectee with | E_Ghost -> true | uu___ -> false
let dbg : Prims.bool FStarC_Effect.ref= FStarC_Debug.get_toggle "Core"
let dbg_Eq : Prims.bool FStarC_Effect.ref= FStarC_Debug.get_toggle "CoreEq"
let dbg_Top : Prims.bool FStarC_Effect.ref= FStarC_Debug.get_toggle "CoreTop"
let dbg_Exit : Prims.bool FStarC_Effect.ref=
  FStarC_Debug.get_toggle "CoreExit"
let dbg_DisableCoreCache : Prims.bool FStarC_Effect.ref=
  FStarC_Debug.get_toggle "DisableCoreCache"
let goal_ctr : Prims.int FStarC_Effect.ref=
  FStarC_Effect.mk_ref Prims.int_zero
let get_goal_ctr (uu___ : unit) : Prims.int= FStarC_Effect.op_Bang goal_ctr
let incr_goal_ctr (uu___ : unit) : Prims.int=
  let v = FStarC_Effect.op_Bang goal_ctr in
  FStarC_Effect.op_Colon_Equals goal_ctr (v + Prims.int_one);
  v + Prims.int_one
type env =
  {
  tcenv: FStarC_TypeChecker_Env.env ;
  allow_universe_instantiation: Prims.bool ;
  should_read_cache: Prims.bool ;
  max_binder_index: Prims.int }
let __proj__Mkenv__item__tcenv (projectee : env) :
  FStarC_TypeChecker_Env.env=
  match projectee with
  | { tcenv; allow_universe_instantiation; should_read_cache;
      max_binder_index;_} -> tcenv
let __proj__Mkenv__item__allow_universe_instantiation (projectee : env) :
  Prims.bool=
  match projectee with
  | { tcenv; allow_universe_instantiation; should_read_cache;
      max_binder_index;_} -> allow_universe_instantiation
let __proj__Mkenv__item__should_read_cache (projectee : env) : Prims.bool=
  match projectee with
  | { tcenv; allow_universe_instantiation; should_read_cache;
      max_binder_index;_} -> should_read_cache
let __proj__Mkenv__item__max_binder_index (projectee : env) : Prims.int=
  match projectee with
  | { tcenv; allow_universe_instantiation; should_read_cache;
      max_binder_index;_} -> max_binder_index
let debug (g : 'uuuuu) (f : unit -> unit) : unit=
  let uu___ = FStarC_Effect.op_Bang dbg in if uu___ then f () else ()
let max (a : Prims.int) (b : Prims.int) : Prims.int= if a > b then a else b
let push_binder (g : env) (b : FStarC_Syntax_Syntax.binder) : env=
  let uu___ = FStarC_TypeChecker_Env.push_binders g.tcenv [b] in
  {
    tcenv = uu___;
    allow_universe_instantiation = (g.allow_universe_instantiation);
    should_read_cache = (g.should_read_cache);
    max_binder_index =
      (max g.max_binder_index
         (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.index)
  }
let push_binders : env -> FStarC_Syntax_Syntax.binder Prims.list -> env=
  FStarC_List.fold_left push_binder
let fresh_binder (g : env) (old : FStarC_Syntax_Syntax.binder) :
  (env * FStarC_Syntax_Syntax.binder)=
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
let wild_bv (t : FStarC_Syntax_Syntax.typ) (r : FStarC_Range_Type.t) :
  FStarC_Syntax_Syntax.bv=
  let uu___ = FStarC_Ident.mk_ident (FStarC_Ident.reserved_prefix, r) in
  {
    FStarC_Syntax_Syntax.ppname = uu___;
    FStarC_Syntax_Syntax.index = Prims.int_zero;
    FStarC_Syntax_Syntax.sort = t
  }
let new_binder (g : env) (t : FStarC_Syntax_Syntax.typ)
  (r : FStarC_Range_Type.t) : (env * FStarC_Syntax_Syntax.binder)=
  let bv = wild_bv t r in
  let b = FStarC_Syntax_Syntax.mk_binder bv in fresh_binder g b
let open_binders (g : env) (bs : FStarC_Syntax_Syntax.binders) :
  (env * FStarC_Syntax_Syntax.binder Prims.list *
    FStarC_Syntax_Syntax.subst_elt Prims.list)=
  let uu___ =
    FStarC_List.fold_left
      (fun uu___1 b ->
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
                 FStarC_List.map (FStarC_Syntax_Subst.subst subst)
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
                      FStarC_Syntax_Subst.shift_subst Prims.int_one subst in
                    (FStarC_Syntax_Syntax.DB
                       (Prims.int_zero, (b'.FStarC_Syntax_Syntax.binder_bv)))
                      :: uu___4 in
                  (g2, (b' :: bs1), uu___3))) (g, [], []) bs in
  match uu___ with
  | (g1, bs_rev, subst) -> (g1, (FStarC_List.rev bs_rev), subst)
let open_pat (g : env) (p : FStarC_Syntax_Syntax.pat) :
  (env * FStarC_Syntax_Syntax.pat * FStarC_Syntax_Syntax.subst_t)=
  let rec open_pat_aux g1 p1 sub =
    match p1.FStarC_Syntax_Syntax.v with
    | FStarC_Syntax_Syntax.Pat_constant uu___ -> (g1, p1, sub)
    | FStarC_Syntax_Syntax.Pat_cons (fv, us_opt, pats) ->
        let uu___ =
          FStarC_List.fold_left
            (fun uu___1 uu___2 ->
               match (uu___1, uu___2) with
               | ((g2, pats1, sub1), (p2, imp)) ->
                   let uu___3 = open_pat_aux g2 p2 sub1 in
                   (match uu___3 with
                    | (g3, p3, sub2) -> (g3, ((p3, imp) :: pats1), sub2)))
            (g1, [], sub) pats in
        (match uu___ with
         | (g2, pats1, sub1) ->
             (g2,
               {
                 FStarC_Syntax_Syntax.v =
                   (FStarC_Syntax_Syntax.Pat_cons
                      (fv, us_opt, (FStarC_List.rev pats1)));
                 FStarC_Syntax_Syntax.p = (p1.FStarC_Syntax_Syntax.p)
               }, sub1))
    | FStarC_Syntax_Syntax.Pat_var x ->
        let bx =
          let uu___ =
            let uu___1 =
              FStarC_Syntax_Subst.subst sub x.FStarC_Syntax_Syntax.sort in
            {
              FStarC_Syntax_Syntax.ppname = (x.FStarC_Syntax_Syntax.ppname);
              FStarC_Syntax_Syntax.index = (x.FStarC_Syntax_Syntax.index);
              FStarC_Syntax_Syntax.sort = uu___1
            } in
          FStarC_Syntax_Syntax.mk_binder uu___ in
        let uu___ = fresh_binder g1 bx in
        (match uu___ with
         | (g2, bx') ->
             let sub1 =
               let uu___1 = FStarC_Syntax_Subst.shift_subst Prims.int_one sub in
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
        let eopt1 = FStarC_Option.map (FStarC_Syntax_Subst.subst sub) eopt in
        (g1,
          {
            FStarC_Syntax_Syntax.v =
              (FStarC_Syntax_Syntax.Pat_dot_term eopt1);
            FStarC_Syntax_Syntax.p = (p1.FStarC_Syntax_Syntax.p)
          }, sub) in
  open_pat_aux g p []
let open_term (g : env) (b : FStarC_Syntax_Syntax.binder)
  (t : FStarC_Syntax_Syntax.term) :
  (env * FStarC_Syntax_Syntax.binder * FStarC_Syntax_Syntax.term)=
  let uu___ = fresh_binder g b in
  match uu___ with
  | (g1, b') ->
      let t1 =
        FStarC_Syntax_Subst.subst
          [FStarC_Syntax_Syntax.DB
             (Prims.int_zero, (b'.FStarC_Syntax_Syntax.binder_bv))] t in
      (g1, b', t1)
let open_term_binders (g : env) (bs : FStarC_Syntax_Syntax.binders)
  (t : FStarC_Syntax_Syntax.term) :
  (env * FStarC_Syntax_Syntax.binders * FStarC_Syntax_Syntax.term)=
  let uu___ = open_binders g bs in
  match uu___ with
  | (g1, bs1, subst) ->
      let uu___1 = FStarC_Syntax_Subst.subst subst t in (g1, bs1, uu___1)
let open_comp (g : env) (b : FStarC_Syntax_Syntax.binder)
  (c : FStarC_Syntax_Syntax.comp) :
  (env * FStarC_Syntax_Syntax.binder * FStarC_Syntax_Syntax.comp)=
  let uu___ = fresh_binder g b in
  match uu___ with
  | (g1, bx) ->
      let c1 =
        FStarC_Syntax_Subst.subst_comp
          [FStarC_Syntax_Syntax.DB
             (Prims.int_zero, (bx.FStarC_Syntax_Syntax.binder_bv))] c in
      (g1, bx, c1)
let open_comp_binders (g : env) (bs : FStarC_Syntax_Syntax.binders)
  (c : FStarC_Syntax_Syntax.comp) :
  (env * FStarC_Syntax_Syntax.binders * FStarC_Syntax_Syntax.comp)=
  let uu___ = open_binders g bs in
  match uu___ with
  | (g1, bs1, s) ->
      let c1 = FStarC_Syntax_Subst.subst_comp s c in (g1, bs1, c1)
let arrow_formals_comp (g : env) (c : FStarC_Syntax_Syntax.term) :
  (env * FStarC_Syntax_Syntax.binder Prims.list * FStarC_Syntax_Syntax.comp)=
  let uu___ = FStarC_Syntax_Util.arrow_formals_comp_ln c in
  match uu___ with
  | (bs, c1) ->
      let uu___1 = open_binders g bs in
      (match uu___1 with
       | (g1, bs1, subst) ->
           let uu___2 = FStarC_Syntax_Subst.subst_comp subst c1 in
           (g1, bs1, uu___2))
let open_branch (g : env) (br : FStarC_Syntax_Syntax.branch) :
  (env * FStarC_Syntax_Syntax.branch)=
  let uu___ = br in
  match uu___ with
  | (p, wopt, e) ->
      let uu___1 = open_pat g p in
      (match uu___1 with
       | (g1, p1, s) ->
           let uu___2 =
             let uu___3 =
               FStarC_Option.map (FStarC_Syntax_Subst.subst s) wopt in
             let uu___4 = FStarC_Syntax_Subst.subst s e in
             (p1, uu___3, uu___4) in
           (g1, uu___2))
let open_branches_eq_pat (g : env) (br0 : FStarC_Syntax_Syntax.branch)
  (br1 : FStarC_Syntax_Syntax.branch) :
  (env * (FStarC_Syntax_Syntax.pat * FStarC_Syntax_Syntax.term
    FStar_Pervasives_Native.option * FStarC_Syntax_Syntax.term) *
    (FStarC_Syntax_Syntax.pat * FStarC_Syntax_Syntax.term
    FStar_Pervasives_Native.option * FStarC_Syntax_Syntax.term))=
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
                    FStarC_Option.map (FStarC_Syntax_Subst.subst s) wopt0 in
                  let uu___6 = FStarC_Syntax_Subst.subst s e0 in
                  (p01, uu___5, uu___6) in
                let uu___5 =
                  let uu___6 =
                    FStarC_Option.map (FStarC_Syntax_Subst.subst s) wopt1 in
                  let uu___7 = FStarC_Syntax_Subst.subst s e1 in
                  (p01, uu___6, uu___7) in
                (g1, uu___4, uu___5)))
type relation =
  | EQUALITY 
  | SUBTYPING of FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option 
let uu___is_EQUALITY (projectee : relation) : Prims.bool=
  match projectee with | EQUALITY -> true | uu___ -> false
let uu___is_SUBTYPING (projectee : relation) : Prims.bool=
  match projectee with | SUBTYPING _0 -> true | uu___ -> false
let __proj__SUBTYPING__item___0 (projectee : relation) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match projectee with | SUBTYPING _0 -> _0
let relation_to_string (uu___ : relation) : Prims.string=
  match uu___ with
  | EQUALITY -> "=?="
  | SUBTYPING (FStar_Pervasives_Native.None) -> "<:?"
  | SUBTYPING (FStar_Pervasives_Native.Some tm) ->
      let uu___1 =
        FStarC_Class_Show.show FStarC_Syntax_Print.showable_term tm in
      FStarC_Format.fmt1 "( <:? %s)" uu___1
type context_term =
  | CtxTerm of FStarC_Syntax_Syntax.term 
  | CtxRel of FStarC_Syntax_Syntax.term * relation *
  FStarC_Syntax_Syntax.term 
let uu___is_CtxTerm (projectee : context_term) : Prims.bool=
  match projectee with | CtxTerm _0 -> true | uu___ -> false
let __proj__CtxTerm__item___0 (projectee : context_term) :
  FStarC_Syntax_Syntax.term= match projectee with | CtxTerm _0 -> _0
let uu___is_CtxRel (projectee : context_term) : Prims.bool=
  match projectee with | CtxRel (_0, _1, _2) -> true | uu___ -> false
let __proj__CtxRel__item___0 (projectee : context_term) :
  FStarC_Syntax_Syntax.term= match projectee with | CtxRel (_0, _1, _2) -> _0
let __proj__CtxRel__item___1 (projectee : context_term) : relation=
  match projectee with | CtxRel (_0, _1, _2) -> _1
let __proj__CtxRel__item___2 (projectee : context_term) :
  FStarC_Syntax_Syntax.term= match projectee with | CtxRel (_0, _1, _2) -> _2
let context_term_to_string (c : context_term) : Prims.string=
  match c with
  | CtxTerm term ->
      FStarC_Class_Show.show FStarC_Syntax_Print.showable_term term
  | CtxRel (t0, r, t1) ->
      let uu___ = FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t0 in
      let uu___1 = relation_to_string r in
      let uu___2 =
        FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t1 in
      FStarC_Format.fmt3 "%s %s %s" uu___ uu___1 uu___2
type context =
  {
  no_guard: Prims.bool ;
  unfolding_ok: Prims.bool ;
  error_context:
    (Prims.string * context_term FStar_Pervasives_Native.option) Prims.list }
let __proj__Mkcontext__item__no_guard (projectee : context) : Prims.bool=
  match projectee with
  | { no_guard; unfolding_ok; error_context;_} -> no_guard
let __proj__Mkcontext__item__unfolding_ok (projectee : context) : Prims.bool=
  match projectee with
  | { no_guard; unfolding_ok; error_context;_} -> unfolding_ok
let __proj__Mkcontext__item__error_context (projectee : context) :
  (Prims.string * context_term FStar_Pervasives_Native.option) Prims.list=
  match projectee with
  | { no_guard; unfolding_ok; error_context;_} -> error_context
let showable_context : context FStarC_Class_Show.showable=
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
             FStarC_List.map FStar_Pervasives_Native.fst
               context1.error_context in
           FStarC_Class_Show.show
             (FStarC_Class_Show.show_list FStarC_Class_Show.showable_string)
             uu___3 in
         FStarC_Format.fmt3
           "{no_guard=%s; unfolding_ok=%s; error_context=%s}" uu___ uu___1
           uu___2)
  }
let print_ctx_head (ctx : context) : Prims.string=
  match ctx.error_context with
  | [] -> "{Context: <empty>}\n"
  | (msg, ctx_term)::uu___ ->
      let uu___1 =
        match ctx_term with
        | FStar_Pervasives_Native.None -> ""
        | FStar_Pervasives_Native.Some ctx_term1 ->
            context_term_to_string ctx_term1 in
      FStarC_Format.fmt2 "{Context: %s (%s)}\n" msg uu___1
let print_context (ctx : context) : Prims.string=
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
          FStarC_Format.fmt3 "%s %s (%s)\n" depth msg uu___ in
        let tl1 = aux (Prims.strcat depth ">") tl in Prims.strcat hd tl1 in
  aux "" (FStarC_List.rev ctx.error_context)
type error = (context * FStarC_Errors_Msg.error_message)
let print_error (err : error) : Prims.string=
  let uu___ = err in
  match uu___ with
  | (ctx, msg) ->
      let uu___1 = print_context ctx in
      let uu___2 = FStarC_Errors_Msg.rendermsg msg in
      FStarC_Format.fmt2 "%s%s" uu___1 uu___2
let showable_error : error FStarC_Class_Show.showable=
  { FStarC_Class_Show.show = print_error }
let print_error_short (err : error) : Prims.string=
  let uu___ = err in
  match uu___ with | (uu___1, msg) -> FStarC_Errors_Msg.rendermsg msg
type precondition = FStarC_Syntax_Syntax.typ FStar_Pervasives_Native.option
type 'a success = ('a * precondition)
type hash_entry =
  {
  he_term: FStarC_Syntax_Syntax.term ;
  he_gamma: FStarC_Syntax_Syntax.binding Prims.list ;
  he_eff: tot_or_ghost ;
  he_typ: FStarC_Syntax_Syntax.typ }
let __proj__Mkhash_entry__item__he_term (projectee : hash_entry) :
  FStarC_Syntax_Syntax.term=
  match projectee with | { he_term; he_gamma; he_eff; he_typ;_} -> he_term
let __proj__Mkhash_entry__item__he_gamma (projectee : hash_entry) :
  FStarC_Syntax_Syntax.binding Prims.list=
  match projectee with | { he_term; he_gamma; he_eff; he_typ;_} -> he_gamma
let __proj__Mkhash_entry__item__he_eff (projectee : hash_entry) :
  tot_or_ghost=
  match projectee with | { he_term; he_gamma; he_eff; he_typ;_} -> he_eff
let __proj__Mkhash_entry__item__he_typ (projectee : hash_entry) :
  FStarC_Syntax_Syntax.typ=
  match projectee with | { he_term; he_gamma; he_eff; he_typ;_} -> he_typ
type guard_entry = {
  ge_gamma: FStarC_Syntax_Syntax.binding Prims.list }
let __proj__Mkguard_entry__item__ge_gamma (projectee : guard_entry) :
  FStarC_Syntax_Syntax.binding Prims.list=
  match projectee with | { ge_gamma;_} -> ge_gamma
type cache_t =
  {
  term_map: hash_entry FStarC_Syntax_Hash.term_map ;
  guard_map: guard_entry FStarC_Syntax_Hash.term_map }
let __proj__Mkcache_t__item__term_map (projectee : cache_t) :
  hash_entry FStarC_Syntax_Hash.term_map=
  match projectee with | { term_map; guard_map;_} -> term_map
let __proj__Mkcache_t__item__guard_map (projectee : cache_t) :
  guard_entry FStarC_Syntax_Hash.term_map=
  match projectee with | { term_map; guard_map;_} -> guard_map
type 'a __result =
  | Success of ('a * cache_t) 
  | Error of error 
let uu___is_Success (projectee : 'a __result) : Prims.bool=
  match projectee with | Success _0 -> true | uu___ -> false
let __proj__Success__item___0 (projectee : 'a __result) : ('a * cache_t)=
  match projectee with | Success _0 -> _0
let uu___is_Error (projectee : 'a __result) : Prims.bool=
  match projectee with | Error _0 -> true | uu___ -> false
let __proj__Error__item___0 (projectee : 'a __result) : error=
  match projectee with | Error _0 -> _0
type tc_table =
  {
  table: hash_entry FStarC_Syntax_TermHashTable.hashtable ;
  guard_table: guard_entry FStarC_Syntax_TermHashTable.hashtable ;
  counter: Prims.int FStarC_Effect.ref }
let __proj__Mktc_table__item__table (projectee : tc_table) :
  hash_entry FStarC_Syntax_TermHashTable.hashtable=
  match projectee with | { table; guard_table; counter;_} -> table
let __proj__Mktc_table__item__guard_table (projectee : tc_table) :
  guard_entry FStarC_Syntax_TermHashTable.hashtable=
  match projectee with | { table; guard_table; counter;_} -> guard_table
let __proj__Mktc_table__item__counter (projectee : tc_table) :
  Prims.int FStarC_Effect.ref=
  match projectee with | { table; guard_table; counter;_} -> counter
let showable_result (uu___ : 'a FStarC_Class_Show.showable) :
  'a __result FStarC_Class_Show.showable=
  {
    FStarC_Class_Show.show =
      (fun uu___1 ->
         match uu___1 with
         | Success (a1, uu___2) ->
             let uu___3 = FStarC_Class_Show.show uu___ a1 in
             Prims.strcat "Success " uu___3
         | Error e ->
             let uu___2 = print_error_short e in Prims.strcat "Error " uu___2)
  }
type 'a result = context -> cache_t -> 'a success __result
let equal_term_for_hash (t1 : FStarC_Syntax_Syntax.term)
  (t2 : FStarC_Syntax_Syntax.term) : Prims.bool=
  FStarC_Profiling.profile (fun uu___ -> FStarC_Syntax_Hash.equal_term t1 t2)
    FStar_Pervasives_Native.None
    "FStarC.TypeChecker.Core.equal_term_for_hash"
let equal_term (t1 : FStarC_Syntax_Syntax.term)
  (t2 : FStarC_Syntax_Syntax.term) : Prims.bool=
  FStarC_Profiling.profile (fun uu___ -> FStarC_Syntax_Hash.equal_term t1 t2)
    FStar_Pervasives_Native.None "FStarC.TypeChecker.Core.equal_term"
let table : tc_table=
  let uu___ = FStarC_Syntax_TermHashTable.create (Prims.parse_int "1048576") in
  let uu___1 = FStarC_Syntax_TermHashTable.create (Prims.parse_int "1048576") in
  let uu___2 = FStarC_Effect.mk_ref Prims.int_zero in
  { table = uu___; guard_table = uu___1; counter = uu___2 }
type cache_stats_t = {
  hits: Prims.int ;
  misses: Prims.int }
let __proj__Mkcache_stats_t__item__hits (projectee : cache_stats_t) :
  Prims.int= match projectee with | { hits; misses;_} -> hits
let __proj__Mkcache_stats_t__item__misses (projectee : cache_stats_t) :
  Prims.int= match projectee with | { hits; misses;_} -> misses
let cache_stats : cache_stats_t FStarC_Effect.ref=
  FStarC_Effect.mk_ref { hits = Prims.int_zero; misses = Prims.int_zero }
let record_cache_hit (uu___ : unit) : unit=
  let cs = FStarC_Effect.op_Bang cache_stats in
  FStarC_Effect.op_Colon_Equals cache_stats
    { hits = (cs.hits + Prims.int_one); misses = (cs.misses) }
let record_cache_miss (uu___ : unit) : unit=
  let cs = FStarC_Effect.op_Bang cache_stats in
  FStarC_Effect.op_Colon_Equals cache_stats
    { hits = (cs.hits); misses = (cs.misses + Prims.int_one) }
let reset_cache_stats (uu___ : unit) : unit=
  FStarC_Effect.op_Colon_Equals cache_stats
    { hits = Prims.int_zero; misses = Prims.int_zero }
let report_cache_stats (uu___ : unit) : cache_stats_t=
  FStarC_Effect.op_Bang cache_stats
let clear_memo_table (uu___ : unit) : unit=
  FStarC_Syntax_TermHashTable.clear table.table;
  FStarC_Syntax_TermHashTable.clear table.guard_table;
  (let uu___3 =
     let uu___4 = FStarC_Effect.op_Bang table.counter in
     uu___4 + Prims.int_one in
   FStarC_Effect.op_Colon_Equals table.counter uu___3)
type guard_commit_token =
  {
  guard_cache: cache_t FStar_Pervasives_Native.option FStarC_Effect.ref ;
  guard_counter: Prims.int }
let __proj__Mkguard_commit_token__item__guard_cache
  (projectee : guard_commit_token) :
  cache_t FStar_Pervasives_Native.option FStarC_Effect.ref=
  match projectee with | { guard_cache; guard_counter;_} -> guard_cache
let __proj__Mkguard_commit_token__item__guard_counter
  (projectee : guard_commit_token) : Prims.int=
  match projectee with | { guard_cache; guard_counter;_} -> guard_counter
type my_guard_and_tok_t = (FStarC_Syntax_Syntax.typ * (unit -> unit))
let empty_token : guard_commit_token_cb= fun uu___ -> ()
let mk_token (cache : cache_t) : guard_commit_token=
  let uu___ = FStarC_Effect.mk_ref (FStar_Pervasives_Native.Some cache) in
  let uu___1 = FStarC_Effect.op_Bang table.counter in
  { guard_cache = uu___; guard_counter = uu___1 }
let commit_guard_core (g : guard_commit_token) : unit=
  let uu___ =
    let uu___1 = FStarC_Effect.op_Bang table.counter in
    g.guard_counter <> uu___1 in
  if uu___
  then ()
  else
    (let cache = FStarC_Effect.op_Bang g.guard_cache in
     match cache with
     | FStar_Pervasives_Native.None -> ()
     | FStar_Pervasives_Native.Some cache1 ->
         (FStarC_Effect.op_Colon_Equals g.guard_cache
            FStar_Pervasives_Native.None;
          FStarC_Syntax_Hash.term_map_fold
            (fun term hash_entry1 uu___4 ->
               FStarC_Syntax_TermHashTable.insert term hash_entry1
                 table.table) cache1.term_map ();
          FStarC_Syntax_Hash.term_map_fold
            (fun term guard_entry1 uu___4 ->
               FStarC_Syntax_TermHashTable.insert term guard_entry1
                 table.guard_table) cache1.guard_map ()))
let commit_cache_cb (cache : cache_t) (uu___ : 'uuuuu) : unit=
  let uu___1 = mk_token cache in commit_guard_core uu___1
let commit_guard (cb : unit -> unit) : unit= cb ()
let commit_guard_and_tok_opt
  (t : guard_and_tok_t FStar_Pervasives_Native.option) : unit=
  match t with
  | FStar_Pervasives_Native.None -> ()
  | FStar_Pervasives_Native.Some (uu___, tok) -> commit_guard tok
let return (x : 'a) : 'a result=
  fun uu___ cache -> Success ((x, FStar_Pervasives_Native.None), cache)
let return_with_guard (x : 'a) (g : precondition) : 'a result=
  fun uu___ cache -> Success ((x, g), cache)
let and_pre (p1 : precondition) (p2 : precondition) :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax
    FStar_Pervasives_Native.option=
  match (p1, p2) with
  | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
      FStar_Pervasives_Native.None
  | (FStar_Pervasives_Native.Some p, FStar_Pervasives_Native.None) ->
      FStar_Pervasives_Native.Some p
  | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some p) ->
      FStar_Pervasives_Native.Some p
  | (FStar_Pervasives_Native.Some p11, FStar_Pervasives_Native.Some p21) ->
      let uu___ = FStarC_Syntax_Util.mk_conj p11 p21 in
      FStar_Pervasives_Native.Some uu___
let op_let_Bang (x : 'a result) (y : 'a -> 'b result) : 'b result=
  fun ctx0 cache0 ->
    let uu___ = x ctx0 cache0 in
    match uu___ with
    | Success ((x1, g1), cache1) ->
        let uu___1 = let uu___2 = y x1 in uu___2 ctx0 cache1 in
        (match uu___1 with
         | Success ((y1, g2), cache2) ->
             let uu___2 =
               let uu___3 = let uu___4 = and_pre g1 g2 in (y1, uu___4) in
               (uu___3, cache2) in
             Success uu___2
         | err -> err)
    | Error err -> Error err
let op_and_Bang (x : 'a result) (y : 'b result) : ('a * 'b) result=
  fun ctx0 cache0 ->
    let uu___ = x ctx0 cache0 in
    match uu___ with
    | Success ((x1, g1), cache1) ->
        let uu___1 =
          let uu___2 ctx01 cache01 =
            let uu___3 = y ctx01 cache01 in
            match uu___3 with
            | Success ((x2, g11), cache11) ->
                let uu___4 =
                  let uu___5 uu___6 cache =
                    Success (((x1, x2), FStar_Pervasives_Native.None), cache) in
                  uu___5 ctx01 cache11 in
                (match uu___4 with
                 | Success ((y1, g2), cache2) ->
                     let uu___5 =
                       let uu___6 =
                         let uu___7 = and_pre g11 g2 in (y1, uu___7) in
                       (uu___6, cache2) in
                     Success uu___5
                 | err -> err)
            | Error err -> Error err in
          uu___2 ctx0 cache1 in
        (match uu___1 with
         | Success ((y1, g2), cache2) ->
             let uu___2 =
               let uu___3 = let uu___4 = and_pre g1 g2 in (y1, uu___4) in
               (uu___3, cache2) in
             Success uu___2
         | err -> err)
    | Error err -> Error err
let with_guard (x : 'a result)
  (f : ('a success, error) FStar_Pervasives.either -> 'b result) : 'b result=
  fun ctx cache ->
    let uu___ = x ctx cache in
    match uu___ with
    | Success (r, cache') ->
        let uu___1 = f (FStar_Pervasives.Inl r) in uu___1 ctx cache'
    | Error err ->
        let uu___1 = f (FStar_Pervasives.Inr err) in uu___1 ctx cache
let op_let_Question (x : 'a FStar_Pervasives_Native.option)
  (f : 'a -> 'b FStar_Pervasives_Native.option) :
  'b FStar_Pervasives_Native.option=
  match x with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some x1 -> f x1
let fail_str (msg : Prims.string) : 'a result=
  fun ctx cache ->
    let uu___ = let uu___1 = FStarC_Errors_Msg.mkmsg msg in (ctx, uu___1) in
    Error uu___
let fail (msg : FStarC_Errors_Msg.error_message) : 'a result=
  fun ctx cache -> Error (ctx, msg)
let fail_propagate (err : error) : 'a result= fun uu___ cache -> Error err
let dump_context : unit result=
  fun ctx cache ->
    (let uu___1 = print_context ctx in FStarC_Format.print_string uu___1);
    (let uu___1 uu___2 cache1 =
       Success (((), FStar_Pervasives_Native.None), cache1) in
     uu___1 ctx cache)
let handle_with (x : 'a result) (h : unit -> 'a result) : 'a result=
  fun ctx cache ->
    let uu___ = x ctx cache in
    match uu___ with
    | Error uu___1 -> let uu___2 = h () in uu___2 ctx cache
    | res -> res
let with_context (msg : Prims.string)
  (t : context_term FStar_Pervasives_Native.option) (x : unit -> 'a result) :
  'a result=
  fun ctx cache ->
    let ctx1 =
      {
        no_guard = (ctx.no_guard);
        unfolding_ok = (ctx.unfolding_ok);
        error_context = ((msg, t) :: (ctx.error_context))
      } in
    let uu___ = x () in uu___ ctx1 cache
let mk_type (u : FStarC_Syntax_Syntax.universe) :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax=
  FStarC_Syntax_Syntax.mk (FStarC_Syntax_Syntax.Tm_type u)
    FStarC_Range_Type.dummyRange
let is_type (g : env) (t : FStarC_Syntax_Syntax.term) :
  FStarC_Syntax_Syntax.universe result=
  let aux t1 =
    let uu___ =
      let uu___1 = FStarC_Syntax_Subst.compress t1 in
      uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_type u ->
        (fun uu___1 cache ->
           Success ((u, FStar_Pervasives_Native.None), cache))
    | uu___1 ->
        let uu___2 =
          let uu___3 =
            let uu___4 = FStarC_Errors_Msg.text "Expected a type, got" in
            let uu___5 =
              FStarC_Class_PP.pp FStarC_Syntax_Print.pretty_term t1 in
            FStar_Pprint.op_Hat_Slash_Hat uu___4 uu___5 in
          [uu___3] in
        fail uu___2 in
  fun ctx cache ->
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
      fun ctx2 cache1 ->
        let uu___2 = uu___1 ctx2 cache1 in
        match uu___2 with
        | Error uu___3 ->
            let uu___4 =
              let uu___5 =
                let uu___6 =
                  FStarC_TypeChecker_Normalize.unfold_whnf g.tcenv t in
                FStarC_Syntax_Util.unrefine uu___6 in
              aux uu___5 in
            uu___4 ctx2 cache1
        | res -> res in
    uu___ ctx1 cache
let rec is_arrow (g : env) (t : FStarC_Syntax_Syntax.term) :
  (FStarC_Syntax_Syntax.binder * tot_or_ghost * FStarC_Syntax_Syntax.typ)
    result=
  let rec aux t1 =
    let uu___ =
      let uu___1 = FStarC_Syntax_Subst.compress t1 in
      uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_arrow
        { FStarC_Syntax_Syntax.bs1 = x::[]; FStarC_Syntax_Syntax.comp = c;_}
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
               let uu___3 =
                 let uu___4 = FStarC_Syntax_Util.comp_result c1 in
                 (x1, eff, uu___4) in
               (fun uu___4 cache ->
                  Success ((uu___3, FStar_Pervasives_Native.None), cache)))
        else
          (let uu___3 = c.FStarC_Syntax_Syntax.n in
           match uu___3 with
           | FStarC_Syntax_Syntax.Comp ct ->
               let e_tag =
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
               (match e_tag with
                | FStar_Pervasives_Native.None ->
                    let uu___4 =
                      let uu___5 =
                        let uu___6 =
                          FStarC_Errors_Msg.text
                            "Expected total or gtot arrow, got" in
                        let uu___7 =
                          let uu___8 = FStarC_Syntax_Util.comp_effect_name c in
                          FStarC_Class_PP.pp FStarC_Ident.pretty_lident
                            uu___8 in
                        FStar_Pprint.op_Hat_Slash_Hat uu___6 uu___7 in
                      [uu___5] in
                    fail uu___4
                | FStar_Pervasives_Native.Some e_tag1 ->
                    let uu___4 = arrow_formals_comp g t1 in
                    (match uu___4 with
                     | (g1, x1::[], c1) ->
                         (debug g1
                            (fun uu___6 ->
                               let uu___7 =
                                 FStarC_Class_Show.show
                                   FStarC_Syntax_Print.showable_term t1 in
                               let uu___8 =
                                 FStarC_Class_Show.show
                                   FStarC_Syntax_Print.showable_binder x1 in
                               let uu___9 =
                                 FStarC_Class_Show.show
                                   FStarC_Syntax_Print.showable_term
                                   (x1.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                               let uu___10 =
                                 FStarC_Class_Show.show
                                   FStarC_Syntax_Print.showable_comp c1 in
                               FStarC_Format.print4
                                 "is_arrow (%s): arg (%s:%s) and comp %s\n"
                                 uu___7 uu___8 uu___9 uu___10);
                          (let uu___6 =
                             FStarC_Syntax_Util.comp_effect_args c1 in
                           match uu___6 with
                           | (pre, uu___7)::(post, uu___8)::uu___9 ->
                               let arg_typ =
                                 FStarC_Syntax_Util.refine
                                   x1.FStarC_Syntax_Syntax.binder_bv pre in
                               let res_typ =
                                 let uu___10 =
                                   let uu___11 =
                                     FStarC_Syntax_Util.comp_result c1 in
                                   let uu___12 =
                                     let uu___13 =
                                       FStarC_Syntax_Util.comp_result c1 in
                                     uu___13.FStarC_Syntax_Syntax.pos in
                                   new_binder g1 uu___11 uu___12 in
                                 match uu___10 with
                                 | (g2, r) ->
                                     let post1 =
                                       let uu___11 =
                                         let uu___12 =
                                           let uu___13 =
                                             FStarC_Syntax_Syntax.bv_to_name
                                               r.FStarC_Syntax_Syntax.binder_bv in
                                           (uu___13,
                                             FStar_Pervasives_Native.None) in
                                         [uu___12] in
                                       FStarC_Syntax_Syntax.mk_Tm_app post
                                         uu___11
                                         post.FStarC_Syntax_Syntax.pos in
                                     FStarC_Syntax_Util.refine
                                       r.FStarC_Syntax_Syntax.binder_bv post1 in
                               let xbv =
                                 let uu___10 =
                                   x1.FStarC_Syntax_Syntax.binder_bv in
                                 {
                                   FStarC_Syntax_Syntax.ppname =
                                     (uu___10.FStarC_Syntax_Syntax.ppname);
                                   FStarC_Syntax_Syntax.index =
                                     (uu___10.FStarC_Syntax_Syntax.index);
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
                               (fun uu___10 cache ->
                                  Success
                                    (((x2, e_tag1, res_typ),
                                       FStar_Pervasives_Native.None), cache)))))))
    | FStarC_Syntax_Syntax.Tm_arrow
        { FStarC_Syntax_Syntax.bs1 = x::xs; FStarC_Syntax_Syntax.comp = c;_}
        ->
        let t2 =
          FStarC_Syntax_Syntax.mk
            (FStarC_Syntax_Syntax.Tm_arrow
               { FStarC_Syntax_Syntax.bs1 = xs; FStarC_Syntax_Syntax.comp = c
               }) t1.FStarC_Syntax_Syntax.pos in
        let uu___1 = open_term g x t2 in
        (match uu___1 with
         | (g1, x1, t3) ->
             (fun uu___2 cache ->
                Success
                  (((x1, E_Total, t3), FStar_Pervasives_Native.None), cache)))
    | FStarC_Syntax_Syntax.Tm_refine
        { FStarC_Syntax_Syntax.b = x; FStarC_Syntax_Syntax.phi = uu___1;_} ->
        is_arrow g x.FStarC_Syntax_Syntax.sort
    | FStarC_Syntax_Syntax.Tm_meta
        { FStarC_Syntax_Syntax.tm2 = t2;
          FStarC_Syntax_Syntax.meta = uu___1;_}
        -> aux t2
    | FStarC_Syntax_Syntax.Tm_ascribed
        { FStarC_Syntax_Syntax.tm = t2; FStarC_Syntax_Syntax.asc = uu___1;
          FStarC_Syntax_Syntax.eff_opt = uu___2;_}
        -> aux t2
    | uu___1 ->
        let uu___2 =
          let uu___3 =
            let uu___4 = FStarC_Errors_Msg.text "Expected an arrow, got a" in
            let uu___5 =
              let uu___6 =
                let uu___7 =
                  FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term
                    t1 in
                FStar_Pprint.doc_of_string uu___7 in
              let uu___7 =
                let uu___8 =
                  FStarC_Class_PP.pp FStarC_Syntax_Print.pretty_term t1 in
                FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu___8 in
              FStar_Pprint.op_Hat_Hat uu___6 uu___7 in
            FStar_Pprint.op_Hat_Slash_Hat uu___4 uu___5 in
          [uu___3] in
        fail uu___2 in
  fun ctx cache ->
    let ctx1 =
      {
        no_guard = (ctx.no_guard);
        unfolding_ok = (ctx.unfolding_ok);
        error_context = (("is_arrow", FStar_Pervasives_Native.None) ::
          (ctx.error_context))
      } in
    let uu___ =
      let uu___1 = aux t in
      fun ctx2 cache1 ->
        let uu___2 = uu___1 ctx2 cache1 in
        match uu___2 with
        | Error uu___3 ->
            let uu___4 =
              let uu___5 = FStarC_TypeChecker_Normalize.unfold_whnf g.tcenv t in
              aux uu___5 in
            uu___4 ctx2 cache1
        | res -> res in
    uu___ ctx1 cache
let check_arg_qual (a : FStarC_Syntax_Syntax.aqual)
  (b : FStarC_Syntax_Syntax.bqual) : unit result=
  match b with
  | FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Implicit uu___) ->
      (match a with
       | FStar_Pervasives_Native.Some
           { FStarC_Syntax_Syntax.aqual_implicit = true;
             FStarC_Syntax_Syntax.aqual_attributes = uu___1;_}
           ->
           (fun uu___2 cache ->
              Success (((), FStar_Pervasives_Native.None), cache))
       | uu___1 -> fail_str "missing arg qualifier implicit")
  | FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Meta uu___) ->
      (match a with
       | FStar_Pervasives_Native.Some
           { FStarC_Syntax_Syntax.aqual_implicit = true;
             FStarC_Syntax_Syntax.aqual_attributes = uu___1;_}
           ->
           (fun uu___2 cache ->
              Success (((), FStar_Pervasives_Native.None), cache))
       | uu___1 -> fail_str "missing arg qualifier implicit")
  | uu___ ->
      (match a with
       | FStar_Pervasives_Native.Some
           { FStarC_Syntax_Syntax.aqual_implicit = true;
             FStarC_Syntax_Syntax.aqual_attributes = uu___1;_}
           -> fail_str "extra arg qualifier implicit"
       | uu___1 ->
           (fun uu___2 cache ->
              Success (((), FStar_Pervasives_Native.None), cache)))
let check_bqual (b0 : FStarC_Syntax_Syntax.bqual)
  (b1 : FStarC_Syntax_Syntax.bqual) : unit result=
  match (b0, b1) with
  | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
      (fun uu___ cache -> Success (((), FStar_Pervasives_Native.None), cache))
  | (FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Implicit b01),
     FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Implicit b11)) ->
      (fun uu___ cache -> Success (((), FStar_Pervasives_Native.None), cache))
  | (FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Equality),
     FStar_Pervasives_Native.None) ->
      (fun uu___ cache -> Success (((), FStar_Pervasives_Native.None), cache))
  | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some
     (FStarC_Syntax_Syntax.Equality)) ->
      (fun uu___ cache -> Success (((), FStar_Pervasives_Native.None), cache))
  | (FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Equality),
     FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Equality)) ->
      (fun uu___ cache -> Success (((), FStar_Pervasives_Native.None), cache))
  | (FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Meta t1),
     FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Meta t2)) when
      equal_term t1 t2 ->
      (fun uu___ cache -> Success (((), FStar_Pervasives_Native.None), cache))
  | uu___ ->
      let uu___1 =
        let uu___2 =
          FStarC_Class_Show.show
            (FStarC_Class_Show.show_option FStarC_Syntax_Print.showable_bqual)
            b0 in
        let uu___3 =
          FStarC_Class_Show.show
            (FStarC_Class_Show.show_option FStarC_Syntax_Print.showable_bqual)
            b1 in
        FStarC_Format.fmt2 "Binder qualifier mismatch, %s vs %s" uu___2
          uu___3 in
      fail_str uu___1
let check_aqual (a0 : FStarC_Syntax_Syntax.aqual)
  (a1 : FStarC_Syntax_Syntax.aqual) : unit result=
  match (a0, a1) with
  | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
      (fun uu___ cache -> Success (((), FStar_Pervasives_Native.None), cache))
  | (FStar_Pervasives_Native.Some
     { FStarC_Syntax_Syntax.aqual_implicit = b0;
       FStarC_Syntax_Syntax.aqual_attributes = uu___;_},
     FStar_Pervasives_Native.Some
     { FStarC_Syntax_Syntax.aqual_implicit = b1;
       FStarC_Syntax_Syntax.aqual_attributes = uu___1;_})
      ->
      if b0 = b1
      then
        (fun uu___2 cache ->
           Success (((), FStar_Pervasives_Native.None), cache))
      else
        (let uu___3 =
           let uu___4 =
             let uu___5 =
               FStarC_Errors_Msg.text "Unequal arg qualifiers: lhs implicit=" in
             let uu___6 =
               let uu___7 = FStarC_Class_PP.pp FStarC_Class_PP.pp_bool b0 in
               let uu___8 =
                 let uu___9 = FStarC_Errors_Msg.text "and rhs implicit=" in
                 let uu___10 = FStarC_Class_PP.pp FStarC_Class_PP.pp_bool b1 in
                 FStar_Pprint.op_Hat_Hat uu___9 uu___10 in
               FStar_Pprint.op_Hat_Slash_Hat uu___7 uu___8 in
             FStar_Pprint.op_Hat_Hat uu___5 uu___6 in
           [uu___4] in
         fail uu___3)
  | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some
     { FStarC_Syntax_Syntax.aqual_implicit = false;
       FStarC_Syntax_Syntax.aqual_attributes = uu___;_})
      ->
      (fun uu___1 cache ->
         Success (((), FStar_Pervasives_Native.None), cache))
  | (FStar_Pervasives_Native.Some
     { FStarC_Syntax_Syntax.aqual_implicit = false;
       FStarC_Syntax_Syntax.aqual_attributes = uu___;_},
     FStar_Pervasives_Native.None) ->
      (fun uu___1 cache ->
         Success (((), FStar_Pervasives_Native.None), cache))
  | uu___ ->
      let uu___1 =
        let uu___2 =
          let uu___3 = FStarC_Errors_Msg.text "Unequal arg qualifiers: lhs" in
          let uu___4 =
            let uu___5 =
              FStarC_Class_PP.pp FStarC_Syntax_Print.pretty_aqual a0 in
            let uu___6 =
              let uu___7 = FStarC_Errors_Msg.text "and rhs" in
              let uu___8 =
                FStarC_Class_PP.pp FStarC_Syntax_Print.pretty_aqual a1 in
              FStar_Pprint.op_Hat_Slash_Hat uu___7 uu___8 in
            FStar_Pprint.op_Hat_Hat uu___5 uu___6 in
          FStar_Pprint.op_Hat_Slash_Hat uu___3 uu___4 in
        [uu___2] in
      fail uu___1
let check_positivity_qual (rel : relation)
  (p0 :
    FStarC_Syntax_Syntax.positivity_qualifier FStar_Pervasives_Native.option)
  (p1 :
    FStarC_Syntax_Syntax.positivity_qualifier FStar_Pervasives_Native.option)
  : unit result=
  let uu___ =
    FStarC_TypeChecker_Common.check_positivity_qual (uu___is_SUBTYPING rel)
      p0 p1 in
  if uu___
  then
    fun uu___1 cache -> Success (((), FStar_Pervasives_Native.None), cache)
  else fail_str "Unequal positivity qualifiers"
let mk_forall_l (us : FStarC_Syntax_Syntax.universes)
  (xs : FStarC_Syntax_Syntax.binders) (t : FStarC_Syntax_Syntax.term) :
  FStarC_Syntax_Syntax.term=
  FStarC_List.fold_right2
    (fun u x t1 ->
       FStarC_Syntax_Util.mk_forall u x.FStarC_Syntax_Syntax.binder_bv t1) us
    xs t
let close_guard (xs : FStarC_Syntax_Syntax.binders)
  (us : FStarC_Syntax_Syntax.universes) (g : precondition) : precondition=
  match g with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some t ->
      let uu___ = mk_forall_l us xs t in FStar_Pervasives_Native.Some uu___
let close_with_definition (x : FStarC_Syntax_Syntax.binder)
  (u : FStarC_Syntax_Syntax.universe) (t : FStarC_Syntax_Syntax.term)
  (g : FStarC_Syntax_Syntax.typ) : FStarC_Syntax_Syntax.typ=
  let g' =
    let uu___ =
      let uu___1 =
        FStarC_Syntax_Syntax.bv_to_name x.FStarC_Syntax_Syntax.binder_bv in
      FStarC_Syntax_Util.mk_eq2 u
        (x.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort uu___1 t in
    FStarC_Syntax_Util.mk_imp uu___ g in
  FStarC_Syntax_Util.mk_forall u x.FStarC_Syntax_Syntax.binder_bv g'
let close_guard_with_definition (x : FStarC_Syntax_Syntax.binder)
  (u : FStarC_Syntax_Syntax.universe) (t : FStarC_Syntax_Syntax.term)
  (g : precondition) : precondition=
  match g with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some t' ->
      let uu___ =
        let t'1 =
          let uu___1 =
            let uu___2 =
              FStarC_Syntax_Syntax.bv_to_name
                x.FStarC_Syntax_Syntax.binder_bv in
            FStarC_Syntax_Util.mk_eq2 u
              (x.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort
              uu___2 t in
          FStarC_Syntax_Util.mk_imp uu___1 t' in
        FStarC_Syntax_Util.mk_forall u x.FStarC_Syntax_Syntax.binder_bv t'1 in
      FStar_Pervasives_Native.Some uu___
let abs (g : env) (a : FStarC_Syntax_Syntax.typ)
  (f : FStarC_Syntax_Syntax.binder -> FStarC_Syntax_Syntax.term) :
  FStarC_Syntax_Syntax.term=
  let uu___ = new_binder g a a.FStarC_Syntax_Syntax.pos in
  match uu___ with
  | (g1, xb) ->
      let uu___1 = f xb in
      FStarC_Syntax_Util.abs [xb] uu___1 FStar_Pervasives_Native.None
let weaken_subtyping (p : FStarC_Syntax_Syntax.term)
  (g : FStarC_Syntax_Syntax.term) : FStarC_Syntax_Syntax.term=
  FStarC_Syntax_Util.mk_imp p g
let push_hypothesis (g : env) (h : FStarC_Syntax_Syntax.term) : env=
  let uu___ = new_binder g h h.FStarC_Syntax_Syntax.pos in
  match uu___ with | (g1, h1) -> g1
let no_guard (g : 'a result) : 'a result=
  fun ctx cache ->
    let uu___ =
      g
        {
          no_guard = true;
          unfolding_ok = (ctx.unfolding_ok);
          error_context = (ctx.error_context)
        } cache in
    match uu___ with
    | Success ((x, FStar_Pervasives_Native.None), cache1) ->
        Success ((x, FStar_Pervasives_Native.None), cache1)
    | Success ((x, FStar_Pervasives_Native.Some g1), cache1) ->
        let uu___1 =
          let uu___2 =
            let uu___3 =
              FStarC_Class_Show.show FStarC_Syntax_Print.showable_term g1 in
            FStarC_Format.fmt1 "Unexpected guard: %s" uu___3 in
          fail_str uu___2 in
        uu___1 ctx cache1
    | err -> err
let equatable (g : env) (t : FStarC_Syntax_Syntax.term) : Prims.bool=
  let uu___ = FStarC_Syntax_Util.leftmost_head t in
  FStarC_TypeChecker_Rel.may_relate_with_logical_guard g.tcenv true uu___
let apply_predicate (x : FStarC_Syntax_Syntax.binder)
  (p : FStarC_Syntax_Syntax.term)
  (e : FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax) :
  FStarC_Syntax_Syntax.term=
  FStarC_Syntax_Subst.subst
    [FStarC_Syntax_Syntax.NT ((x.FStarC_Syntax_Syntax.binder_bv), e)] p
let curry_arrow (x : FStarC_Syntax_Syntax.binder)
  (xs : FStarC_Syntax_Syntax.binders) (c : FStarC_Syntax_Syntax.comp) :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax=
  let tail =
    FStarC_Syntax_Syntax.mk
      (FStarC_Syntax_Syntax.Tm_arrow
         { FStarC_Syntax_Syntax.bs1 = xs; FStarC_Syntax_Syntax.comp = c })
      FStarC_Range_Type.dummyRange in
  let uu___ =
    let uu___1 =
      let uu___2 = FStarC_Syntax_Syntax.mk_Total tail in
      { FStarC_Syntax_Syntax.bs1 = [x]; FStarC_Syntax_Syntax.comp = uu___2 } in
    FStarC_Syntax_Syntax.Tm_arrow uu___1 in
  FStarC_Syntax_Syntax.mk uu___ FStarC_Range_Type.dummyRange
let curry_abs (b0 : FStarC_Syntax_Syntax.binder)
  (b1 : FStarC_Syntax_Syntax.binder) (bs : FStarC_Syntax_Syntax.binders)
  (body : FStarC_Syntax_Syntax.term)
  (ropt : FStarC_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option)
  : FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax=
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
let is_gtot_comp (c : FStarC_Syntax_Syntax.comp) : Prims.bool=
  (FStarC_Syntax_Util.is_tot_or_gtot_comp c) &&
    (let uu___ = FStarC_Syntax_Util.is_total_comp c in
     Prims.op_Negation uu___)
let rec context_included (g0 : FStarC_Syntax_Syntax.binding Prims.list)
  (g1 : FStarC_Syntax_Syntax.binding Prims.list) : Prims.bool=
  let uu___ = FStarC_Util.physical_equality g0 g1 in
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
                x0.FStarC_Syntax_Syntax.index = x1.FStarC_Syntax_Syntax.index
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
let curry_application
  (hd : FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  (arg :
    (FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax *
      FStarC_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option))
  (args :
    (FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax *
      FStarC_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
      Prims.list)
  (p : FStarC_Range_Type.range) :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax=
  let head =
    FStarC_Syntax_Syntax.mk
      (FStarC_Syntax_Syntax.Tm_app
         { FStarC_Syntax_Syntax.hd = hd; FStarC_Syntax_Syntax.args = [arg] })
      p in
  let t =
    FStarC_Syntax_Syntax.mk
      (FStarC_Syntax_Syntax.Tm_app
         { FStarC_Syntax_Syntax.hd = head; FStarC_Syntax_Syntax.args = args })
      p in
  t
let replace_all_use_ranges (r : FStarC_Range_Type.t)
  (t : FStarC_Syntax_Syntax.term) : FStarC_Syntax_Syntax.term=
  let ur = FStarC_Range_Type.use_range r in
  FStarC_Syntax_Visit.visit_term false
    (fun t1 ->
       let uu___ =
         FStarC_Range_Type.set_use_range t1.FStarC_Syntax_Syntax.pos ur in
       {
         FStarC_Syntax_Syntax.n = (t1.FStarC_Syntax_Syntax.n);
         FStarC_Syntax_Syntax.pos = uu___;
         FStarC_Syntax_Syntax.vars = (t1.FStarC_Syntax_Syntax.vars);
         FStarC_Syntax_Syntax.hash_code = (t1.FStarC_Syntax_Syntax.hash_code)
       }) t
let get_cache (uu___ : unit) : cache_t result=
  fun uu___1 cache -> Success ((cache, FStar_Pervasives_Native.None), cache)
let put_cache (cache : cache_t) : unit result=
  fun uu___ uu___1 -> Success (((), FStar_Pervasives_Native.None), cache)
let raw_lookup (e : FStarC_Syntax_Syntax.term) :
  hash_entry FStar_Pervasives_Native.option result=
  let uu___ = get_cache () in
  fun ctx0 cache0 ->
    let uu___1 = uu___ ctx0 cache0 in
    match uu___1 with
    | Success ((x, g1), cache1) ->
        let uu___2 =
          let uu___3 =
            let uu___4 = FStarC_Syntax_Hash.term_map_lookup e x.term_map in
            match uu___4 with
            | FStar_Pervasives_Native.Some he ->
                (fun uu___5 cache ->
                   Success
                     (((FStar_Pervasives_Native.Some he),
                        FStar_Pervasives_Native.None), cache))
            | FStar_Pervasives_Native.None ->
                let uu___5 = FStarC_Syntax_TermHashTable.lookup e table.table in
                (fun uu___6 cache ->
                   Success ((uu___5, FStar_Pervasives_Native.None), cache)) in
          uu___3 ctx0 cache1 in
        (match uu___2 with
         | Success ((y, g2), cache2) ->
             let uu___3 =
               let uu___4 = let uu___5 = and_pre g1 g2 in (y, uu___5) in
               (uu___4, cache2) in
             Success uu___3
         | err -> err)
    | Error err -> Error err
let raw_lookup_guard (e : FStarC_Syntax_Syntax.term) :
  guard_entry FStar_Pervasives_Native.option result=
  let uu___ = get_cache () in
  fun ctx0 cache0 ->
    let uu___1 = uu___ ctx0 cache0 in
    match uu___1 with
    | Success ((x, g1), cache1) ->
        let uu___2 =
          let uu___3 =
            let uu___4 = FStarC_Syntax_Hash.term_map_lookup e x.guard_map in
            match uu___4 with
            | FStar_Pervasives_Native.Some he ->
                (fun uu___5 cache ->
                   Success
                     (((FStar_Pervasives_Native.Some he),
                        FStar_Pervasives_Native.None), cache))
            | FStar_Pervasives_Native.None ->
                let uu___5 =
                  FStarC_Syntax_TermHashTable.lookup e table.guard_table in
                (fun uu___6 cache ->
                   Success ((uu___5, FStar_Pervasives_Native.None), cache)) in
          uu___3 ctx0 cache1 in
        (match uu___2 with
         | Success ((y, g2), cache2) ->
             let uu___3 =
               let uu___4 = let uu___5 = and_pre g1 g2 in (y, uu___5) in
               (uu___4, cache2) in
             Success uu___3
         | err -> err)
    | Error err -> Error err
let insert_guard (g : env) (guard : FStarC_Syntax_Syntax.typ) : unit result=
  let uu___ = get_cache () in
  fun ctx0 cache0 ->
    let uu___1 = uu___ ctx0 cache0 in
    match uu___1 with
    | Success ((x, g1), cache1) ->
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 =
                FStarC_Syntax_Hash.term_map_add guard
                  { ge_gamma = ((g.tcenv).FStarC_TypeChecker_Env.gamma) }
                  x.guard_map in
              { term_map = (x.term_map); guard_map = uu___5 } in
            put_cache uu___4 in
          uu___3 ctx0 cache1 in
        (match uu___2 with
         | Success ((y, g2), cache2) ->
             let uu___3 =
               let uu___4 = let uu___5 = and_pre g1 g2 in ((), uu___5) in
               (uu___4, cache2) in
             Success uu___3
         | err -> err)
    | Error err -> Error err
let guard (g : env) (guard1 : FStarC_Syntax_Syntax.typ) : unit result=
  let uu___ = raw_lookup_guard guard1 in
  fun ctx0 cache0 ->
    let uu___1 = uu___ ctx0 cache0 in
    match uu___1 with
    | Success ((x, g1), cache1) ->
        let uu___2 =
          let uu___3 =
            match x with
            | FStar_Pervasives_Native.Some ge ->
                let uu___4 =
                  context_included ge.ge_gamma
                    (g.tcenv).FStarC_TypeChecker_Env.gamma in
                if uu___4
                then
                  (fun uu___5 cache ->
                     Success (((), FStar_Pervasives_Native.None), cache))
                else
                  (let uu___6 = insert_guard g guard1 in
                   fun ctx01 cache01 ->
                     let uu___7 = uu___6 ctx01 cache01 in
                     match uu___7 with
                     | Success ((x1, g11), cache11) ->
                         let uu___8 =
                           let uu___9 uu___10 cache =
                             Success
                               (((), (FStar_Pervasives_Native.Some guard1)),
                                 cache) in
                           uu___9 ctx01 cache11 in
                         (match uu___8 with
                          | Success ((y, g2), cache2) ->
                              let uu___9 =
                                let uu___10 =
                                  let uu___11 = and_pre g11 g2 in
                                  ((), uu___11) in
                                (uu___10, cache2) in
                              Success uu___9
                          | err -> err)
                     | Error err -> Error err)
            | uu___4 ->
                let uu___5 = insert_guard g guard1 in
                (fun ctx01 cache01 ->
                   let uu___6 = uu___5 ctx01 cache01 in
                   match uu___6 with
                   | Success ((x1, g11), cache11) ->
                       let uu___7 =
                         let uu___8 uu___9 cache =
                           Success
                             (((), (FStar_Pervasives_Native.Some guard1)),
                               cache) in
                         uu___8 ctx01 cache11 in
                       (match uu___7 with
                        | Success ((y, g2), cache2) ->
                            let uu___8 =
                              let uu___9 =
                                let uu___10 = and_pre g11 g2 in ((), uu___10) in
                              (uu___9, cache2) in
                            Success uu___8
                        | err -> err)
                   | Error err -> Error err) in
          uu___3 ctx0 cache1 in
        (match uu___2 with
         | Success ((y, g2), cache2) ->
             let uu___3 =
               let uu___4 = let uu___5 = and_pre g1 g2 in ((), uu___5) in
               (uu___4, cache2) in
             Success uu___3
         | err -> err)
    | Error err -> Error err
let with_binders (initial_env : env) (xs : FStarC_Syntax_Syntax.binders)
  (us : FStarC_Syntax_Syntax.universes) (f : 'a result) : 'a result=
  fun ctx cache ->
    let uu___ = f ctx cache in
    match uu___ with
    | Success (r, cache') ->
        let uu___1 =
          match FStar_Pervasives.Inl r with
          | FStar_Pervasives.Inr err -> fail_propagate err
          | FStar_Pervasives.Inl (res, FStar_Pervasives_Native.None) ->
              (fun uu___2 cache1 ->
                 Success ((res, FStar_Pervasives_Native.None), cache1))
          | FStar_Pervasives.Inl (res, FStar_Pervasives_Native.Some form) ->
              let form1 = mk_forall_l us xs form in
              let uu___2 = guard initial_env form1 in
              (fun ctx0 cache0 ->
                 let uu___3 = uu___2 ctx0 cache0 in
                 match uu___3 with
                 | Success ((x, g1), cache1) ->
                     let uu___4 =
                       let uu___5 uu___6 cache2 =
                         Success
                           ((res, FStar_Pervasives_Native.None), cache2) in
                       uu___5 ctx0 cache1 in
                     (match uu___4 with
                      | Success ((y, g2), cache2) ->
                          let uu___5 =
                            let uu___6 =
                              let uu___7 = and_pre g1 g2 in (y, uu___7) in
                            (uu___6, cache2) in
                          Success uu___5
                      | err -> err)
                 | Error err -> Error err) in
        uu___1 ctx cache'
    | Error err -> let uu___1 = fail_propagate err in uu___1 ctx cache
let with_definition (initial_env : env) (x : FStarC_Syntax_Syntax.binder)
  (u : FStarC_Syntax_Syntax.universe) (t : FStarC_Syntax_Syntax.term)
  (f : 'a result) : 'a result=
  fun ctx cache ->
    let uu___ = f ctx cache in
    match uu___ with
    | Success (r, cache') ->
        let uu___1 =
          match FStar_Pervasives.Inl r with
          | FStar_Pervasives.Inr err -> fail_propagate err
          | FStar_Pervasives.Inl (res, FStar_Pervasives_Native.None) ->
              (fun uu___2 cache1 ->
                 Success ((res, FStar_Pervasives_Native.None), cache1))
          | FStar_Pervasives.Inl (res, FStar_Pervasives_Native.Some form) ->
              let form1 = close_with_definition x u t form in
              let uu___2 = guard initial_env form1 in
              (fun ctx0 cache0 ->
                 let uu___3 = uu___2 ctx0 cache0 in
                 match uu___3 with
                 | Success ((x1, g1), cache1) ->
                     let uu___4 =
                       let uu___5 uu___6 cache2 =
                         Success
                           ((res, FStar_Pervasives_Native.None), cache2) in
                       uu___5 ctx0 cache1 in
                     (match uu___4 with
                      | Success ((y, g2), cache2) ->
                          let uu___5 =
                            let uu___6 =
                              let uu___7 = and_pre g1 g2 in (y, uu___7) in
                            (uu___6, cache2) in
                          Success uu___5
                      | err -> err)
                 | Error err -> Error err) in
        uu___1 ctx cache'
    | Error err -> let uu___1 = fail_propagate err in uu___1 ctx cache
let weaken (initial_env : env) (p : FStarC_Syntax_Syntax.term)
  (f : 'a result) : 'a result=
  fun ctx cache ->
    let uu___ = f ctx cache in
    match uu___ with
    | Success (r, cache') ->
        let uu___1 =
          match FStar_Pervasives.Inl r with
          | FStar_Pervasives.Inr err -> fail_propagate err
          | FStar_Pervasives.Inl (res, FStar_Pervasives_Native.None) ->
              (fun uu___2 cache1 ->
                 Success ((res, FStar_Pervasives_Native.None), cache1))
          | FStar_Pervasives.Inl (res, FStar_Pervasives_Native.Some form) ->
              let form1 = weaken_subtyping p form in
              let uu___2 = guard initial_env form1 in
              (fun ctx0 cache0 ->
                 let uu___3 = uu___2 ctx0 cache0 in
                 match uu___3 with
                 | Success ((x, g1), cache1) ->
                     let uu___4 =
                       let uu___5 uu___6 cache2 =
                         Success
                           ((res, FStar_Pervasives_Native.None), cache2) in
                       uu___5 ctx0 cache1 in
                     (match uu___4 with
                      | Success ((y, g2), cache2) ->
                          let uu___5 =
                            let uu___6 =
                              let uu___7 = and_pre g1 g2 in (y, uu___7) in
                            (uu___6, cache2) in
                          Success uu___5
                      | err -> err)
                 | Error err -> Error err) in
        uu___1 ctx cache'
    | Error err -> let uu___1 = fail_propagate err in uu___1 ctx cache
let weaken_with_guard_formula (env1 : env)
  (p : FStarC_TypeChecker_Common.guard_formula) (g : 'a result) : 'a result=
  match p with
  | FStarC_TypeChecker_Common.Trivial -> g
  | FStarC_TypeChecker_Common.NonTrivial p1 -> weaken env1 p1 g
let insert (g : env) (e : FStarC_Syntax_Syntax.term)
  (res : (tot_or_ghost * FStarC_Syntax_Syntax.typ) success) : unit result=
  let uu___ = get_cache () in
  fun ctx0 cache0 ->
    let uu___1 = uu___ ctx0 cache0 in
    match uu___1 with
    | Success ((x, g1), cache1) ->
        let uu___2 =
          let uu___3 =
            let uu___4 = res in
            match uu___4 with
            | ((eff, typ), uu___5) ->
                let entry =
                  {
                    he_term = e;
                    he_gamma = ((g.tcenv).FStarC_TypeChecker_Env.gamma);
                    he_eff = eff;
                    he_typ = typ
                  } in
                (debug g
                   (fun uu___7 ->
                      let uu___8 =
                        FStarC_Class_Show.show
                          FStarC_Syntax_Print.showable_term e in
                      let uu___9 =
                        FStarC_Class_Show.show
                          FStarC_Syntax_Print.showable_term
                          (FStar_Pervasives_Native.snd
                             (FStar_Pervasives_Native.fst res)) in
                      let uu___10 =
                        FStarC_Class_Show.show
                          (FStarC_Class_Show.show_list
                             FStarC_Syntax_Print.showable_binding)
                          (g.tcenv).FStarC_TypeChecker_Env.gamma in
                      FStarC_Format.print3
                        "Inserting into cache\n %s : %s\nwith\n\tenv %s\n"
                        uu___8 uu___9 uu___10);
                 (let new_cache =
                    let uu___7 =
                      FStarC_Syntax_Hash.term_map_add e entry x.term_map in
                    { term_map = uu___7; guard_map = (x.guard_map) } in
                  put_cache new_cache)) in
          uu___3 ctx0 cache1 in
        (match uu___2 with
         | Success ((y, g2), cache2) ->
             let uu___3 =
               let uu___4 = let uu___5 = and_pre g1 g2 in ((), uu___5) in
               (uu___4, cache2) in
             Success uu___3
         | err -> err)
    | Error err -> Error err
let lookup (g : env) (e : FStarC_Syntax_Syntax.term) :
  (tot_or_ghost * FStarC_Syntax_Syntax.typ) result=
  let uu___ = raw_lookup e in
  fun ctx0 cache0 ->
    let uu___1 = uu___ ctx0 cache0 in
    match uu___1 with
    | Success ((x, g1), cache1) ->
        let uu___2 =
          let uu___3 =
            match x with
            | FStar_Pervasives_Native.None ->
                (record_cache_miss (); fail_str "not in cache")
            | FStar_Pervasives_Native.Some he ->
                let uu___4 =
                  (context_included he.he_gamma
                     (g.tcenv).FStarC_TypeChecker_Env.gamma)
                    &&
                    (let uu___5 = FStarC_Effect.op_Bang dbg_DisableCoreCache in
                     Prims.op_Negation uu___5) in
                if uu___4
                then
                  (record_cache_hit ();
                   (let uu___7 = FStarC_Effect.op_Bang dbg in
                    if uu___7
                    then
                      let uu___8 =
                        FStarC_Class_Show.show
                          FStarC_Syntax_Print.showable_term e in
                      let uu___9 =
                        FStarC_Class_Show.show
                          FStarC_Syntax_Print.showable_term he.he_typ in
                      let uu___10 =
                        FStarC_Class_Show.show
                          (FStarC_Class_Show.show_list
                             FStarC_Syntax_Print.showable_binding)
                          (g.tcenv).FStarC_TypeChecker_Env.gamma in
                      let uu___11 =
                        FStarC_Class_Show.show
                          (FStarC_Class_Show.show_list
                             FStarC_Syntax_Print.showable_binding)
                          he.he_gamma in
                      FStarC_Format.print4
                        "cache hit\n %s : %s\nmatching\n\tenv0 %s\n\tenv1 %s\n"
                        uu___8 uu___9 uu___10 uu___11
                    else ());
                   (let ty =
                      let uu___7 =
                        FStarC_Class_HasRange.pos
                          (FStarC_Syntax_Syntax.has_range_syntax ()) e in
                      replace_all_use_ranges uu___7 he.he_typ in
                    fun uu___7 cache ->
                      Success
                        ((((he.he_eff), ty), FStar_Pervasives_Native.None),
                          cache)))
                else fail_str "not in cache" in
          uu___3 ctx0 cache1 in
        (match uu___2 with
         | Success ((y, g2), cache2) ->
             let uu___3 =
               let uu___4 = let uu___5 = and_pre g1 g2 in (y, uu___5) in
               (uu___4, cache2) in
             Success uu___3
         | err -> err)
    | Error err -> Error err
let check_no_escape (bs : FStarC_Syntax_Syntax.binders)
  (t : FStarC_Syntax_Syntax.term) : unit result=
  let xs = FStarC_Syntax_Free.names t in
  let uu___ =
    FStarC_Util.for_all
      (fun b ->
         let uu___1 =
           FStarC_Class_Setlike.mem ()
             (Obj.magic
                (FStarC_FlatSet.setlike_flat_set FStarC_Syntax_Syntax.ord_bv))
             b.FStarC_Syntax_Syntax.binder_bv (Obj.magic xs) in
         Prims.op_Negation uu___1) bs in
  if uu___
  then
    fun uu___1 cache -> Success (((), FStar_Pervasives_Native.None), cache)
  else fail_str "Name escapes its scope"
let rec map :
  'a 'b . ('a -> 'b result) -> 'a Prims.list -> 'b Prims.list result =
  fun f l ->
    match l with
    | [] ->
        (fun uu___ cache ->
           Success (([], FStar_Pervasives_Native.None), cache))
    | hd::tl ->
        let uu___ = f hd in
        (fun ctx0 cache0 ->
           let uu___1 = uu___ ctx0 cache0 in
           match uu___1 with
           | Success ((x, g1), cache1) ->
               let uu___2 =
                 let uu___3 =
                   let uu___4 = map f tl in
                   fun ctx01 cache01 ->
                     let uu___5 = uu___4 ctx01 cache01 in
                     match uu___5 with
                     | Success ((x1, g11), cache11) ->
                         let uu___6 =
                           let uu___7 uu___8 cache =
                             Success
                               (((x :: x1), FStar_Pervasives_Native.None),
                                 cache) in
                           uu___7 ctx01 cache11 in
                         (match uu___6 with
                          | Success ((y, g2), cache2) ->
                              let uu___7 =
                                let uu___8 =
                                  let uu___9 = and_pre g11 g2 in (y, uu___9) in
                                (uu___8, cache2) in
                              Success uu___7
                          | err -> err)
                     | Error err -> Error err in
                 uu___3 ctx0 cache1 in
               (match uu___2 with
                | Success ((y, g2), cache2) ->
                    let uu___3 =
                      let uu___4 = let uu___5 = and_pre g1 g2 in (y, uu___5) in
                      (uu___4, cache2) in
                    Success uu___3
                | err -> err)
           | Error err -> Error err)
let mapi (f : Prims.int -> 'a -> 'b result) (l : 'a Prims.list) :
  'b Prims.list result=
  let rec aux i l1 =
    match l1 with
    | [] ->
        (fun uu___ cache ->
           Success (([], FStar_Pervasives_Native.None), cache))
    | hd::tl ->
        let uu___ = f i hd in
        (fun ctx0 cache0 ->
           let uu___1 = uu___ ctx0 cache0 in
           match uu___1 with
           | Success ((x, g1), cache1) ->
               let uu___2 =
                 let uu___3 =
                   let uu___4 = aux (i + Prims.int_one) tl in
                   fun ctx01 cache01 ->
                     let uu___5 = uu___4 ctx01 cache01 in
                     match uu___5 with
                     | Success ((x1, g11), cache11) ->
                         let uu___6 =
                           let uu___7 uu___8 cache =
                             Success
                               (((x :: x1), FStar_Pervasives_Native.None),
                                 cache) in
                           uu___7 ctx01 cache11 in
                         (match uu___6 with
                          | Success ((y, g2), cache2) ->
                              let uu___7 =
                                let uu___8 =
                                  let uu___9 = and_pre g11 g2 in (y, uu___9) in
                                (uu___8, cache2) in
                              Success uu___7
                          | err -> err)
                     | Error err -> Error err in
                 uu___3 ctx0 cache1 in
               (match uu___2 with
                | Success ((y, g2), cache2) ->
                    let uu___3 =
                      let uu___4 = let uu___5 = and_pre g1 g2 in (y, uu___5) in
                      (uu___4, cache2) in
                    Success uu___3
                | err -> err)
           | Error err -> Error err) in
  aux Prims.int_zero l
let rec map2 :
  'a 'b 'c .
    ('a -> 'b -> 'c result) ->
      'a Prims.list -> 'b Prims.list -> 'c Prims.list result
  =
  fun f l1 l2 ->
    match (l1, l2) with
    | ([], []) ->
        (fun uu___ cache ->
           Success (([], FStar_Pervasives_Native.None), cache))
    | (hd1::tl1, hd2::tl2) ->
        let uu___ = f hd1 hd2 in
        (fun ctx0 cache0 ->
           let uu___1 = uu___ ctx0 cache0 in
           match uu___1 with
           | Success ((x, g1), cache1) ->
               let uu___2 =
                 let uu___3 =
                   let uu___4 = map2 f tl1 tl2 in
                   fun ctx01 cache01 ->
                     let uu___5 = uu___4 ctx01 cache01 in
                     match uu___5 with
                     | Success ((x1, g11), cache11) ->
                         let uu___6 =
                           let uu___7 uu___8 cache =
                             Success
                               (((x :: x1), FStar_Pervasives_Native.None),
                                 cache) in
                           uu___7 ctx01 cache11 in
                         (match uu___6 with
                          | Success ((y, g2), cache2) ->
                              let uu___7 =
                                let uu___8 =
                                  let uu___9 = and_pre g11 g2 in (y, uu___9) in
                                (uu___8, cache2) in
                              Success uu___7
                          | err -> err)
                     | Error err -> Error err in
                 uu___3 ctx0 cache1 in
               (match uu___2 with
                | Success ((y, g2), cache2) ->
                    let uu___3 =
                      let uu___4 = let uu___5 = and_pre g1 g2 in (y, uu___5) in
                      (uu___4, cache2) in
                    Success uu___3
                | err -> err)
           | Error err -> Error err)
let rec fold :
  'a 'b . ('a -> 'b -> 'a result) -> 'a -> 'b Prims.list -> 'a result =
  fun f x l ->
    match l with
    | [] ->
        (fun uu___ cache ->
           Success ((x, FStar_Pervasives_Native.None), cache))
    | hd::tl ->
        let uu___ = f x hd in
        (fun ctx0 cache0 ->
           let uu___1 = uu___ ctx0 cache0 in
           match uu___1 with
           | Success ((x1, g1), cache1) ->
               let uu___2 = let uu___3 = fold f x1 tl in uu___3 ctx0 cache1 in
               (match uu___2 with
                | Success ((y, g2), cache2) ->
                    let uu___3 =
                      let uu___4 = let uu___5 = and_pre g1 g2 in (y, uu___5) in
                      (uu___4, cache2) in
                    Success uu___3
                | err -> err)
           | Error err -> Error err)
let rec fold2 :
  'a 'b 'c .
    ('a -> 'b -> 'c -> 'a result) ->
      'a -> 'b Prims.list -> 'c Prims.list -> 'a result
  =
  fun f x l1 l2 ->
    match (l1, l2) with
    | ([], []) ->
        (fun uu___ cache ->
           Success ((x, FStar_Pervasives_Native.None), cache))
    | (hd1::tl1, hd2::tl2) ->
        let uu___ = f x hd1 hd2 in
        (fun ctx0 cache0 ->
           let uu___1 = uu___ ctx0 cache0 in
           match uu___1 with
           | Success ((x1, g1), cache1) ->
               let uu___2 =
                 let uu___3 = fold2 f x1 tl1 tl2 in uu___3 ctx0 cache1 in
               (match uu___2 with
                | Success ((y, g2), cache2) ->
                    let uu___3 =
                      let uu___4 = let uu___5 = and_pre g1 g2 in (y, uu___5) in
                      (uu___4, cache2) in
                    Success uu___3
                | err -> err)
           | Error err -> Error err)
let rec iter2 :
  'a 'b .
    'a Prims.list ->
      'a Prims.list -> ('a -> 'a -> 'b -> 'b result) -> 'b -> 'b result
  =
  fun xs ys f b1 ->
    match (xs, ys) with
    | ([], []) ->
        (fun uu___ cache ->
           Success ((b1, FStar_Pervasives_Native.None), cache))
    | (x::xs1, y::ys1) ->
        let uu___ = f x y b1 in
        (fun ctx0 cache0 ->
           let uu___1 = uu___ ctx0 cache0 in
           match uu___1 with
           | Success ((x1, g1), cache1) ->
               let uu___2 =
                 let uu___3 = iter2 xs1 ys1 f x1 in uu___3 ctx0 cache1 in
               (match uu___2 with
                | Success ((y1, g2), cache2) ->
                    let uu___3 =
                      let uu___4 = let uu___5 = and_pre g1 g2 in (y1, uu___5) in
                      (uu___4, cache2) in
                    Success uu___3
                | err -> err)
           | Error err -> Error err)
    | uu___ -> fail_str "Lists of differing length"
let is_non_informative (g : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.typ) : Prims.bool=
  FStarC_TypeChecker_Normalize.non_info_norm g t
let non_informative (g : env) (t : FStarC_Syntax_Syntax.typ) : Prims.bool=
  is_non_informative g.tcenv t
let as_comp (g : env) (et : (tot_or_ghost * FStarC_Syntax_Syntax.typ)) :
  FStarC_Syntax_Syntax.comp=
  match et with
  | (E_Total, t) -> FStarC_Syntax_Syntax.mk_Total t
  | (E_Ghost, t) ->
      let uu___ = non_informative g t in
      if uu___
      then FStarC_Syntax_Syntax.mk_Total t
      else FStarC_Syntax_Syntax.mk_GTotal t
let comp_as_tot_or_ghost_and_type (c : FStarC_Syntax_Syntax.comp) :
  (tot_or_ghost * FStarC_Syntax_Syntax.typ) FStar_Pervasives_Native.option=
  let uu___ = FStarC_Syntax_Util.is_total_comp c in
  if uu___
  then
    let uu___1 =
      let uu___2 = FStarC_Syntax_Util.comp_result c in (E_Total, uu___2) in
    FStar_Pervasives_Native.Some uu___1
  else
    (let uu___2 = FStarC_Syntax_Util.is_tot_or_gtot_comp c in
     if uu___2
     then
       let uu___3 =
         let uu___4 = FStarC_Syntax_Util.comp_result c in (E_Ghost, uu___4) in
       FStar_Pervasives_Native.Some uu___3
     else FStar_Pervasives_Native.None)
let join_eff (e0 : tot_or_ghost) (e1 : tot_or_ghost) : tot_or_ghost=
  match (e0, e1) with
  | (E_Ghost, uu___) -> E_Ghost
  | (uu___, E_Ghost) -> E_Ghost
  | uu___ -> E_Total
let join_eff_l (es : tot_or_ghost Prims.list) : tot_or_ghost=
  FStar_List_Tot_Base.fold_right join_eff es E_Total
let guard_not_allowed : Prims.bool result=
  fun ctx cache ->
    Success (((ctx.no_guard), FStar_Pervasives_Native.None), cache)
let unfolding_ok : Prims.bool result=
  fun ctx cache ->
    Success (((ctx.unfolding_ok), FStar_Pervasives_Native.None), cache)
let showable_tot_or_ghost : tot_or_ghost FStarC_Class_Show.showable=
  {
    FStarC_Class_Show.show =
      (fun uu___ ->
         match uu___ with | E_Total -> "E_Total" | E_Ghost -> "E_Ghost")
  }
type side =
  | Left 
  | Right 
  | Both 
  | Neither 
let uu___is_Left (projectee : side) : Prims.bool=
  match projectee with | Left -> true | uu___ -> false
let uu___is_Right (projectee : side) : Prims.bool=
  match projectee with | Right -> true | uu___ -> false
let uu___is_Both (projectee : side) : Prims.bool=
  match projectee with | Both -> true | uu___ -> false
let uu___is_Neither (projectee : side) : Prims.bool=
  match projectee with | Neither -> true | uu___ -> false
let showable_side : side FStarC_Class_Show.showable=
  {
    FStarC_Class_Show.show =
      (fun uu___ ->
         match uu___ with
         | Left -> "Left"
         | Right -> "Right"
         | Both -> "Both"
         | Neither -> "Neither")
  }
let boolean_negation_simp (b : FStarC_Syntax_Syntax.term) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  let uu___ =
    FStarC_Syntax_Hash.equal_term b FStarC_Syntax_Util.exp_false_bool in
  if uu___
  then FStar_Pervasives_Native.None
  else
    (let uu___2 = FStarC_Syntax_Util.mk_boolean_negation b in
     FStar_Pervasives_Native.Some uu___2)
let combine_path_and_branch_condition
  (path_condition : FStarC_Syntax_Syntax.term)
  (branch_condition :
    FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option)
  (branch_equality : FStarC_Syntax_Syntax.term) :
  (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.term)=
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
let maybe_relate_after_unfolding (g : FStarC_TypeChecker_Env.env)
  (t0 : FStarC_Syntax_Syntax.term) (t1 : FStarC_Syntax_Syntax.term) : 
  side=
  let dd0 = FStarC_TypeChecker_Env.delta_depth_of_term g t0 in
  let dd1 = FStarC_TypeChecker_Env.delta_depth_of_term g t1 in
  if dd0 = dd1
  then Both
  else
    (let uu___1 = FStarC_TypeChecker_Common.delta_depth_greater_than dd0 dd1 in
     if uu___1 then Left else Right)
let showable_rel : relation FStarC_Class_Show.showable=
  {
    FStarC_Class_Show.show =
      (fun rel ->
         match rel with | EQUALITY -> "=?=" | SUBTYPING uu___ -> "<:?")
  }
let rec check_relation' (g : env) (rel : relation)
  (t0 : FStarC_Syntax_Syntax.typ) (t1 : FStarC_Syntax_Syntax.typ) :
  unit result=
  let err lbl =
    match rel with
    | EQUALITY ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 = FStarC_Errors_Msg.text lbl in
              FStar_Pprint.parens uu___3 in
            let uu___3 =
              let uu___4 = FStarC_Errors_Msg.text "not equal terms:" in
              let uu___5 =
                let uu___6 =
                  FStarC_Class_PP.pp FStarC_Syntax_Print.pretty_term t0 in
                let uu___7 =
                  let uu___8 = FStarC_Errors_Msg.text "<>" in
                  let uu___9 =
                    FStarC_Class_PP.pp FStarC_Syntax_Print.pretty_term t1 in
                  FStar_Pprint.op_Hat_Slash_Hat uu___8 uu___9 in
                FStar_Pprint.op_Hat_Slash_Hat uu___6 uu___7 in
              FStar_Pprint.op_Hat_Slash_Hat uu___4 uu___5 in
            FStar_Pprint.op_Hat_Slash_Hat uu___2 uu___3 in
          [uu___1] in
        fail uu___
    | uu___ ->
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 = FStarC_Errors_Msg.text lbl in
              FStar_Pprint.parens uu___4 in
            let uu___4 =
              let uu___5 =
                FStarC_Class_PP.pp FStarC_Syntax_Print.pretty_term t0 in
              let uu___6 =
                let uu___7 = FStarC_Errors_Msg.text "is not a subtype of" in
                let uu___8 =
                  FStarC_Class_PP.pp FStarC_Syntax_Print.pretty_term t1 in
                FStar_Pprint.op_Hat_Slash_Hat uu___7 uu___8 in
              FStar_Pprint.op_Hat_Slash_Hat uu___5 uu___6 in
            FStar_Pprint.op_Hat_Slash_Hat uu___3 uu___4 in
          [uu___2] in
        fail uu___1 in
  fun ctx0 cache0 ->
    let uu___ = guard_not_allowed ctx0 cache0 in
    match uu___ with
    | Success ((x, g1), cache1) ->
        let uu___1 =
          let uu___2 =
            let guard_ok = Prims.op_Negation x in
            let head_matches t01 t11 =
              let head0 = FStarC_Syntax_Util.leftmost_head t01 in
              let head1 = FStarC_Syntax_Util.leftmost_head t11 in
              let uu___3 =
                let uu___4 =
                  let uu___5 = FStarC_Syntax_Util.un_uinst head0 in
                  uu___5.FStarC_Syntax_Syntax.n in
                let uu___5 =
                  let uu___6 = FStarC_Syntax_Util.un_uinst head1 in
                  uu___6.FStarC_Syntax_Syntax.n in
                (uu___4, uu___5) in
              match uu___3 with
              | (FStarC_Syntax_Syntax.Tm_fvar fv0,
                 FStarC_Syntax_Syntax.Tm_fvar fv1) ->
                  FStarC_Syntax_Syntax.fv_eq fv0 fv1
              | (FStarC_Syntax_Syntax.Tm_name x0,
                 FStarC_Syntax_Syntax.Tm_name x1) ->
                  FStarC_Syntax_Syntax.bv_eq x0 x1
              | (FStarC_Syntax_Syntax.Tm_constant c0,
                 FStarC_Syntax_Syntax.Tm_constant c1) ->
                  equal_term head0 head1
              | (FStarC_Syntax_Syntax.Tm_type uu___4,
                 FStarC_Syntax_Syntax.Tm_type uu___5) -> true
              | (FStarC_Syntax_Syntax.Tm_arrow uu___4,
                 FStarC_Syntax_Syntax.Tm_arrow uu___5) -> true
              | (FStarC_Syntax_Syntax.Tm_match uu___4,
                 FStarC_Syntax_Syntax.Tm_match uu___5) -> true
              | uu___4 -> false in
            let which_side_to_unfold t01 t11 =
              maybe_relate_after_unfolding g.tcenv t01 t11 in
            let maybe_unfold_side side1 t01 t11 =
              FStarC_Profiling.profile
                (fun uu___3 ->
                   match side1 with
                   | Neither -> FStar_Pervasives_Native.None
                   | Both ->
                       let uu___4 =
                         let uu___5 =
                           FStarC_TypeChecker_Normalize.maybe_unfold_head
                             g.tcenv t01 in
                         let uu___6 =
                           FStarC_TypeChecker_Normalize.maybe_unfold_head
                             g.tcenv t11 in
                         (uu___5, uu___6) in
                       (match uu___4 with
                        | (FStar_Pervasives_Native.Some t02,
                           FStar_Pervasives_Native.Some t12) ->
                            FStar_Pervasives_Native.Some (t02, t12)
                        | (FStar_Pervasives_Native.Some t02,
                           FStar_Pervasives_Native.None) ->
                            FStar_Pervasives_Native.Some (t02, t11)
                        | (FStar_Pervasives_Native.None,
                           FStar_Pervasives_Native.Some t12) ->
                            FStar_Pervasives_Native.Some (t01, t12)
                        | uu___5 -> FStar_Pervasives_Native.None)
                   | Left ->
                       let uu___4 =
                         FStarC_TypeChecker_Normalize.maybe_unfold_head
                           g.tcenv t01 in
                       (match uu___4 with
                        | FStar_Pervasives_Native.Some t02 ->
                            FStar_Pervasives_Native.Some (t02, t11)
                        | uu___5 -> FStar_Pervasives_Native.None)
                   | Right ->
                       let uu___4 =
                         FStarC_TypeChecker_Normalize.maybe_unfold_head
                           g.tcenv t11 in
                       (match uu___4 with
                        | FStar_Pervasives_Native.Some t12 ->
                            FStar_Pervasives_Native.Some (t01, t12)
                        | uu___5 -> FStar_Pervasives_Native.None))
                FStar_Pervasives_Native.None
                "FStarC.TypeChecker.Core.maybe_unfold_side" in
            let maybe_unfold t01 t11 ctx01 cache01 =
              let uu___3 = unfolding_ok ctx01 cache01 in
              match uu___3 with
              | Success ((x1, g11), cache11) ->
                  let uu___4 =
                    let uu___5 =
                      if x1
                      then
                        let uu___6 =
                          let uu___7 = which_side_to_unfold t01 t11 in
                          maybe_unfold_side uu___7 t01 t11 in
                        fun uu___7 cache ->
                          Success
                            ((uu___6, FStar_Pervasives_Native.None), cache)
                      else
                        (fun uu___7 cache ->
                           Success
                             ((FStar_Pervasives_Native.None,
                                FStar_Pervasives_Native.None), cache)) in
                    uu___5 ctx01 cache11 in
                  (match uu___4 with
                   | Success ((y, g2), cache2) ->
                       let uu___5 =
                         let uu___6 =
                           let uu___7 = and_pre g11 g2 in (y, uu___7) in
                         (uu___6, cache2) in
                       Success uu___5
                   | err1 -> err1)
              | Error err1 -> Error err1 in
            let emit_guard t01 t11 =
              let uu___3 ctx cache =
                let ctx1 =
                  {
                    no_guard = (ctx.no_guard);
                    unfolding_ok = (ctx.unfolding_ok);
                    error_context =
                      (("checking lhs while emitting guard",
                         FStar_Pervasives_Native.None) ::
                      (ctx.error_context))
                  } in
                let uu___4 = do_check g t01 in uu___4 ctx1 cache in
              fun ctx01 cache01 ->
                let uu___4 = uu___3 ctx01 cache01 in
                match uu___4 with
                | Success ((x1, g11), cache11) ->
                    let uu___5 =
                      let uu___6 =
                        match x1 with
                        | (uu___7, t_typ) ->
                            let uu___8 = universe_of_well_typed_term g t_typ in
                            (fun ctx02 cache02 ->
                               let uu___9 = uu___8 ctx02 cache02 in
                               match uu___9 with
                               | Success ((x2, g12), cache12) ->
                                   let uu___10 =
                                     let uu___11 =
                                       let uu___12 =
                                         FStarC_Syntax_Util.mk_eq2 x2 t_typ
                                           t01 t11 in
                                       guard g uu___12 in
                                     uu___11 ctx02 cache12 in
                                   (match uu___10 with
                                    | Success ((y, g2), cache2) ->
                                        let uu___11 =
                                          let uu___12 =
                                            let uu___13 = and_pre g12 g2 in
                                            ((), uu___13) in
                                          (uu___12, cache2) in
                                        Success uu___11
                                    | err1 -> err1)
                               | Error err1 -> Error err1) in
                      uu___6 ctx01 cache11 in
                    (match uu___5 with
                     | Success ((y, g2), cache2) ->
                         let uu___6 =
                           let uu___7 =
                             let uu___8 = and_pre g11 g2 in ((), uu___8) in
                           (uu___7, cache2) in
                         Success uu___6
                     | err1 -> err1)
                | Error err1 -> Error err1 in
            let fallback t01 t11 =
              if guard_ok
              then
                let uu___3 = (equatable g t01) || (equatable g t11) in
                (if uu___3 then emit_guard t01 t11 else err "not equatable")
              else err "guards not allowed" in
            let maybe_unfold_side_and_retry side1 t01 t11 ctx01 cache01 =
              let uu___3 = unfolding_ok ctx01 cache01 in
              match uu___3 with
              | Success ((x1, g11), cache11) ->
                  let uu___4 =
                    let uu___5 =
                      if x1
                      then
                        let uu___6 = maybe_unfold_side side1 t01 t11 in
                        match uu___6 with
                        | FStar_Pervasives_Native.None -> fallback t01 t11
                        | FStar_Pervasives_Native.Some (t02, t12) ->
                            check_relation g rel t02 t12
                      else fallback t01 t11 in
                    uu___5 ctx01 cache11 in
                  (match uu___4 with
                   | Success ((y, g2), cache2) ->
                       let uu___5 =
                         let uu___6 =
                           let uu___7 = and_pre g11 g2 in ((), uu___7) in
                         (uu___6, cache2) in
                       Success uu___5
                   | err1 -> err1)
              | Error err1 -> Error err1 in
            let maybe_unfold_and_retry t01 t11 =
              let uu___3 = which_side_to_unfold t01 t11 in
              maybe_unfold_side_and_retry uu___3 t01 t11 in
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
              | FStarC_Syntax_Syntax.Tm_refine uu___3 ->
                  FStarC_Syntax_Util.flatten_refinement t3
              | uu___3 -> t3 in
            let beta_iota_reduce1 t =
              FStarC_Profiling.profile (fun uu___3 -> beta_iota_reduce t)
                FStar_Pervasives_Native.None
                "FStarC.TypeChecker.Core.beta_iota_reduce" in
            let t01 =
              let uu___3 =
                let uu___4 = beta_iota_reduce1 t0 in
                FStarC_Syntax_Subst.compress uu___4 in
              FStarC_Syntax_Util.unlazy_emb uu___3 in
            let t11 =
              let uu___3 =
                let uu___4 = beta_iota_reduce1 t1 in
                FStarC_Syntax_Subst.compress uu___4 in
              FStarC_Syntax_Util.unlazy_emb uu___3 in
            let check_relation1 g2 rel1 t02 t12 ctx cache =
              let ctx1 =
                {
                  no_guard = (ctx.no_guard);
                  unfolding_ok = (ctx.unfolding_ok);
                  error_context =
                    (("check_relation",
                       (FStar_Pervasives_Native.Some
                          (CtxRel (t02, rel1, t12)))) :: (ctx.error_context))
                } in
              let uu___3 = check_relation g2 rel1 t02 t12 in
              uu___3 ctx1 cache in
            let uu___3 = equal_term t01 t11 in
            if uu___3
            then
              fun uu___4 cache ->
                Success (((), FStar_Pervasives_Native.None), cache)
            else
              (match ((t01.FStarC_Syntax_Syntax.n),
                       (t11.FStarC_Syntax_Syntax.n))
               with
               | (FStarC_Syntax_Syntax.Tm_type u0,
                  FStarC_Syntax_Syntax.Tm_type u1) ->
                   let uu___5 =
                     FStarC_TypeChecker_Rel.teq_nosmt_force g.tcenv t01 t11 in
                   if uu___5
                   then
                     (fun uu___6 cache ->
                        Success (((), FStar_Pervasives_Native.None), cache))
                   else err "teq_nosmt_force over Types failed"
               | (FStarC_Syntax_Syntax.Tm_meta
                  { FStarC_Syntax_Syntax.tm2 = t02;
                    FStarC_Syntax_Syntax.meta =
                      FStarC_Syntax_Syntax.Meta_pattern uu___5;_},
                  uu___6) -> check_relation1 g rel t02 t11
               | (FStarC_Syntax_Syntax.Tm_meta
                  { FStarC_Syntax_Syntax.tm2 = t02;
                    FStarC_Syntax_Syntax.meta =
                      FStarC_Syntax_Syntax.Meta_named uu___5;_},
                  uu___6) -> check_relation1 g rel t02 t11
               | (FStarC_Syntax_Syntax.Tm_meta
                  { FStarC_Syntax_Syntax.tm2 = t02;
                    FStarC_Syntax_Syntax.meta =
                      FStarC_Syntax_Syntax.Meta_labeled uu___5;_},
                  uu___6) -> check_relation1 g rel t02 t11
               | (FStarC_Syntax_Syntax.Tm_meta
                  { FStarC_Syntax_Syntax.tm2 = t02;
                    FStarC_Syntax_Syntax.meta =
                      FStarC_Syntax_Syntax.Meta_desugared uu___5;_},
                  uu___6) -> check_relation1 g rel t02 t11
               | (FStarC_Syntax_Syntax.Tm_ascribed
                  { FStarC_Syntax_Syntax.tm = t02;
                    FStarC_Syntax_Syntax.asc = uu___5;
                    FStarC_Syntax_Syntax.eff_opt = uu___6;_},
                  uu___7) -> check_relation1 g rel t02 t11
               | (uu___5, FStarC_Syntax_Syntax.Tm_meta
                  { FStarC_Syntax_Syntax.tm2 = t12;
                    FStarC_Syntax_Syntax.meta =
                      FStarC_Syntax_Syntax.Meta_pattern uu___6;_})
                   -> check_relation1 g rel t01 t12
               | (uu___5, FStarC_Syntax_Syntax.Tm_meta
                  { FStarC_Syntax_Syntax.tm2 = t12;
                    FStarC_Syntax_Syntax.meta =
                      FStarC_Syntax_Syntax.Meta_named uu___6;_})
                   -> check_relation1 g rel t01 t12
               | (uu___5, FStarC_Syntax_Syntax.Tm_meta
                  { FStarC_Syntax_Syntax.tm2 = t12;
                    FStarC_Syntax_Syntax.meta =
                      FStarC_Syntax_Syntax.Meta_labeled uu___6;_})
                   -> check_relation1 g rel t01 t12
               | (uu___5, FStarC_Syntax_Syntax.Tm_meta
                  { FStarC_Syntax_Syntax.tm2 = t12;
                    FStarC_Syntax_Syntax.meta =
                      FStarC_Syntax_Syntax.Meta_desugared uu___6;_})
                   -> check_relation1 g rel t01 t12
               | (uu___5, FStarC_Syntax_Syntax.Tm_ascribed
                  { FStarC_Syntax_Syntax.tm = t12;
                    FStarC_Syntax_Syntax.asc = uu___6;
                    FStarC_Syntax_Syntax.eff_opt = uu___7;_})
                   -> check_relation1 g rel t01 t12
               | (FStarC_Syntax_Syntax.Tm_uinst (f0, us0),
                  FStarC_Syntax_Syntax.Tm_uinst (f1, us1)) ->
                   let uu___5 = equal_term f0 f1 in
                   if uu___5
                   then
                     let uu___6 =
                       FStarC_TypeChecker_Rel.teq_nosmt_force g.tcenv t01 t11 in
                     (if uu___6
                      then
                        fun uu___7 cache ->
                          Success (((), FStar_Pervasives_Native.None), cache)
                      else err "teq_nosmt_force over Tm_uinst failed")
                   else maybe_unfold_and_retry t01 t11
               | (FStarC_Syntax_Syntax.Tm_fvar uu___5,
                  FStarC_Syntax_Syntax.Tm_fvar uu___6) ->
                   maybe_unfold_and_retry t01 t11
               | (FStarC_Syntax_Syntax.Tm_refine
                  { FStarC_Syntax_Syntax.b = x0;
                    FStarC_Syntax_Syntax.phi = f0;_},
                  FStarC_Syntax_Syntax.Tm_refine
                  { FStarC_Syntax_Syntax.b = x1;
                    FStarC_Syntax_Syntax.phi = f1;_})
                   ->
                   let uu___5 =
                     head_matches x0.FStarC_Syntax_Syntax.sort
                       x1.FStarC_Syntax_Syntax.sort in
                   if uu___5
                   then
                     let uu___6 =
                       check_relation1 g EQUALITY
                         x0.FStarC_Syntax_Syntax.sort
                         x1.FStarC_Syntax_Syntax.sort in
                     (fun ctx01 cache01 ->
                        let uu___7 = uu___6 ctx01 cache01 in
                        match uu___7 with
                        | Success ((x2, g11), cache11) ->
                            let uu___8 =
                              let uu___9 =
                                let uu___10 =
                                  universe_of_well_typed_term g
                                    x0.FStarC_Syntax_Syntax.sort in
                                fun ctx02 cache02 ->
                                  let uu___11 = uu___10 ctx02 cache02 in
                                  match uu___11 with
                                  | Success ((x3, g12), cache12) ->
                                      let uu___12 =
                                        let uu___13 =
                                          let g0 = g in
                                          let uu___14 =
                                            let uu___15 =
                                              FStarC_Syntax_Syntax.mk_binder
                                                x0 in
                                            open_term g uu___15 f0 in
                                          match uu___14 with
                                          | (g2, b, f01) ->
                                              let f11 =
                                                FStarC_Syntax_Subst.subst
                                                  [FStarC_Syntax_Syntax.DB
                                                     (Prims.int_zero,
                                                       (b.FStarC_Syntax_Syntax.binder_bv))]
                                                  f1 in
                                              (fun ctx03 cache03 ->
                                                 let uu___15 =
                                                   guard_not_allowed ctx03
                                                     cache03 in
                                                 match uu___15 with
                                                 | Success
                                                     ((x4, g13), cache13) ->
                                                     let uu___16 =
                                                       let uu___17 =
                                                         if x4
                                                         then
                                                           let uu___18 =
                                                             check_relation1
                                                               g2 EQUALITY
                                                               f01 f11 in
                                                           with_binders g0
                                                             [b] [x3] uu___18
                                                         else
                                                           (match rel with
                                                            | EQUALITY ->
                                                                let uu___19 =
                                                                  let uu___20
                                                                    =
                                                                    check_relation1
                                                                    g2
                                                                    EQUALITY
                                                                    f01 f11 in
                                                                  fun ctx
                                                                    cache ->
                                                                    let uu___21
                                                                    =
                                                                    uu___20
                                                                    ctx cache in
                                                                    match uu___21
                                                                    with
                                                                    | 
                                                                    Error
                                                                    uu___22
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    FStarC_Syntax_Util.mk_iff
                                                                    f01 f11 in
                                                                    guard g2
                                                                    uu___24 in
                                                                    uu___23
                                                                    ctx cache
                                                                    | 
                                                                    res ->
                                                                    res in
                                                                with_binders
                                                                  g0 
                                                                  [b] 
                                                                  [x3]
                                                                  uu___19
                                                            | SUBTYPING
                                                                (FStar_Pervasives_Native.Some
                                                                tm) ->
                                                                let uu___19 =
                                                                  let uu___20
                                                                    =
                                                                    FStarC_Syntax_Util.mk_imp
                                                                    f01 f11 in
                                                                  FStarC_Syntax_Subst.subst
                                                                    [
                                                                    FStarC_Syntax_Syntax.NT
                                                                    ((b.FStarC_Syntax_Syntax.binder_bv),
                                                                    tm)]
                                                                    uu___20 in
                                                                guard g0
                                                                  uu___19
                                                            | SUBTYPING
                                                                (FStar_Pervasives_Native.None)
                                                                ->
                                                                let uu___19 =
                                                                  let uu___20
                                                                    =
                                                                    FStarC_Syntax_Util.mk_imp
                                                                    f01 f11 in
                                                                  FStarC_Syntax_Util.mk_forall
                                                                    x3
                                                                    b.FStarC_Syntax_Syntax.binder_bv
                                                                    uu___20 in
                                                                guard g0
                                                                  uu___19) in
                                                       uu___17 ctx03 cache13 in
                                                     (match uu___16 with
                                                      | Success
                                                          ((y, g21), cache2)
                                                          ->
                                                          let uu___17 =
                                                            let uu___18 =
                                                              let uu___19 =
                                                                and_pre g13
                                                                  g21 in
                                                              ((), uu___19) in
                                                            (uu___18, cache2) in
                                                          Success uu___17
                                                      | err1 -> err1)
                                                 | Error err1 -> Error err1) in
                                        uu___13 ctx02 cache12 in
                                      (match uu___12 with
                                       | Success ((y, g2), cache2) ->
                                           let uu___13 =
                                             let uu___14 =
                                               let uu___15 = and_pre g12 g2 in
                                               ((), uu___15) in
                                             (uu___14, cache2) in
                                           Success uu___13
                                       | err1 -> err1)
                                  | Error err1 -> Error err1 in
                              uu___9 ctx01 cache11 in
                            (match uu___8 with
                             | Success ((y, g2), cache2) ->
                                 let uu___9 =
                                   let uu___10 =
                                     let uu___11 = and_pre g11 g2 in
                                     ((), uu___11) in
                                   (uu___10, cache2) in
                                 Success uu___9
                             | err1 -> err1)
                        | Error err1 -> Error err1)
                   else
                     (let uu___7 =
                        maybe_unfold x0.FStarC_Syntax_Syntax.sort
                          x1.FStarC_Syntax_Syntax.sort in
                      fun ctx01 cache01 ->
                        let uu___8 = uu___7 ctx01 cache01 in
                        match uu___8 with
                        | Success ((x2, g11), cache11) ->
                            let uu___9 =
                              let uu___10 =
                                match x2 with
                                | FStar_Pervasives_Native.None ->
                                    ((let uu___12 = FStarC_Effect.op_Bang dbg in
                                      if uu___12
                                      then
                                        let uu___13 =
                                          FStarC_Class_Show.show
                                            FStarC_Syntax_Print.showable_term
                                            x0.FStarC_Syntax_Syntax.sort in
                                        let uu___14 =
                                          FStarC_Class_Show.show
                                            FStarC_Syntax_Print.showable_term
                                            x1.FStarC_Syntax_Syntax.sort in
                                        FStarC_Format.print2
                                          "Cannot match ref heads %s and %s\n"
                                          uu___13 uu___14
                                      else ());
                                     fallback t01 t11)
                                | FStar_Pervasives_Native.Some (t02, t12) ->
                                    let lhs =
                                      FStarC_Syntax_Syntax.mk
                                        (FStarC_Syntax_Syntax.Tm_refine
                                           {
                                             FStarC_Syntax_Syntax.b =
                                               {
                                                 FStarC_Syntax_Syntax.ppname
                                                   =
                                                   (x0.FStarC_Syntax_Syntax.ppname);
                                                 FStarC_Syntax_Syntax.index =
                                                   (x0.FStarC_Syntax_Syntax.index);
                                                 FStarC_Syntax_Syntax.sort =
                                                   t02
                                               };
                                             FStarC_Syntax_Syntax.phi = f0
                                           }) t02.FStarC_Syntax_Syntax.pos in
                                    let rhs =
                                      FStarC_Syntax_Syntax.mk
                                        (FStarC_Syntax_Syntax.Tm_refine
                                           {
                                             FStarC_Syntax_Syntax.b =
                                               {
                                                 FStarC_Syntax_Syntax.ppname
                                                   =
                                                   (x1.FStarC_Syntax_Syntax.ppname);
                                                 FStarC_Syntax_Syntax.index =
                                                   (x1.FStarC_Syntax_Syntax.index);
                                                 FStarC_Syntax_Syntax.sort =
                                                   t12
                                               };
                                             FStarC_Syntax_Syntax.phi = f1
                                           }) t12.FStarC_Syntax_Syntax.pos in
                                    let uu___11 =
                                      FStarC_Syntax_Util.flatten_refinement
                                        lhs in
                                    let uu___12 =
                                      FStarC_Syntax_Util.flatten_refinement
                                        rhs in
                                    check_relation1 g rel uu___11 uu___12 in
                              uu___10 ctx01 cache11 in
                            (match uu___9 with
                             | Success ((y, g2), cache2) ->
                                 let uu___10 =
                                   let uu___11 =
                                     let uu___12 = and_pre g11 g2 in
                                     ((), uu___12) in
                                   (uu___11, cache2) in
                                 Success uu___10
                             | err1 -> err1)
                        | Error err1 -> Error err1)
               | (FStarC_Syntax_Syntax.Tm_refine
                  { FStarC_Syntax_Syntax.b = x0;
                    FStarC_Syntax_Syntax.phi = f0;_},
                  uu___5) ->
                   let uu___6 = head_matches x0.FStarC_Syntax_Syntax.sort t11 in
                   if uu___6
                   then
                     let uu___7 =
                       if rel = EQUALITY
                       then
                         let uu___8 =
                           universe_of_well_typed_term g
                             x0.FStarC_Syntax_Syntax.sort in
                         fun ctx01 cache01 ->
                           let uu___9 = uu___8 ctx01 cache01 in
                           match uu___9 with
                           | Success ((x1, g11), cache11) ->
                               let uu___10 =
                                 let uu___11 =
                                   let g0 = g in
                                   let uu___12 =
                                     let uu___13 =
                                       FStarC_Syntax_Syntax.mk_binder x0 in
                                     open_term g uu___13 f0 in
                                   match uu___12 with
                                   | (g2, b0, f01) ->
                                       (fun ctx02 cache02 ->
                                          let uu___13 =
                                            guard_not_allowed ctx02 cache02 in
                                          match uu___13 with
                                          | Success ((x2, g12), cache12) ->
                                              let uu___14 =
                                                let uu___15 =
                                                  if x2
                                                  then
                                                    let uu___16 =
                                                      check_relation1 g2
                                                        EQUALITY
                                                        FStarC_Syntax_Util.t_true
                                                        f01 in
                                                    with_binders g0 [b0] 
                                                      [x1] uu___16
                                                  else
                                                    (let uu___17 =
                                                       let uu___18 =
                                                         check_relation1 g2
                                                           EQUALITY
                                                           FStarC_Syntax_Util.t_true
                                                           f01 in
                                                       fun ctx cache ->
                                                         let uu___19 =
                                                           uu___18 ctx cache in
                                                         match uu___19 with
                                                         | Error uu___20 ->
                                                             let uu___21 =
                                                               guard g2 f01 in
                                                             uu___21 ctx
                                                               cache
                                                         | res -> res in
                                                     with_binders g0 
                                                       [b0] [x1] uu___17) in
                                                uu___15 ctx02 cache12 in
                                              (match uu___14 with
                                               | Success ((y, g21), cache2)
                                                   ->
                                                   let uu___15 =
                                                     let uu___16 =
                                                       let uu___17 =
                                                         and_pre g12 g21 in
                                                       ((), uu___17) in
                                                     (uu___16, cache2) in
                                                   Success uu___15
                                               | err1 -> err1)
                                          | Error err1 -> Error err1) in
                                 uu___11 ctx01 cache11 in
                               (match uu___10 with
                                | Success ((y, g2), cache2) ->
                                    let uu___11 =
                                      let uu___12 =
                                        let uu___13 = and_pre g11 g2 in
                                        ((), uu___13) in
                                      (uu___12, cache2) in
                                    Success uu___11
                                | err1 -> err1)
                           | Error err1 -> Error err1
                       else
                         (fun uu___9 cache ->
                            Success
                              (((), FStar_Pervasives_Native.None), cache)) in
                     (fun ctx01 cache01 ->
                        let uu___8 = uu___7 ctx01 cache01 in
                        match uu___8 with
                        | Success ((x1, g11), cache11) ->
                            let uu___9 =
                              let uu___10 =
                                check_relation1 g rel
                                  x0.FStarC_Syntax_Syntax.sort t11 in
                              uu___10 ctx01 cache11 in
                            (match uu___9 with
                             | Success ((y, g2), cache2) ->
                                 let uu___10 =
                                   let uu___11 =
                                     let uu___12 = and_pre g11 g2 in
                                     ((), uu___12) in
                                   (uu___11, cache2) in
                                 Success uu___10
                             | err1 -> err1)
                        | Error err1 -> Error err1)
                   else
                     (let uu___8 =
                        maybe_unfold x0.FStarC_Syntax_Syntax.sort t11 in
                      fun ctx01 cache01 ->
                        let uu___9 = uu___8 ctx01 cache01 in
                        match uu___9 with
                        | Success ((x1, g11), cache11) ->
                            let uu___10 =
                              let uu___11 =
                                match x1 with
                                | FStar_Pervasives_Native.None ->
                                    fallback t01 t11
                                | FStar_Pervasives_Native.Some (t02, t12) ->
                                    let lhs =
                                      FStarC_Syntax_Syntax.mk
                                        (FStarC_Syntax_Syntax.Tm_refine
                                           {
                                             FStarC_Syntax_Syntax.b =
                                               {
                                                 FStarC_Syntax_Syntax.ppname
                                                   =
                                                   (x0.FStarC_Syntax_Syntax.ppname);
                                                 FStarC_Syntax_Syntax.index =
                                                   (x0.FStarC_Syntax_Syntax.index);
                                                 FStarC_Syntax_Syntax.sort =
                                                   t02
                                               };
                                             FStarC_Syntax_Syntax.phi = f0
                                           }) t02.FStarC_Syntax_Syntax.pos in
                                    let uu___12 =
                                      FStarC_Syntax_Util.flatten_refinement
                                        lhs in
                                    check_relation1 g rel uu___12 t12 in
                              uu___11 ctx01 cache11 in
                            (match uu___10 with
                             | Success ((y, g2), cache2) ->
                                 let uu___11 =
                                   let uu___12 =
                                     let uu___13 = and_pre g11 g2 in
                                     ((), uu___13) in
                                   (uu___12, cache2) in
                                 Success uu___11
                             | err1 -> err1)
                        | Error err1 -> Error err1)
               | (uu___5, FStarC_Syntax_Syntax.Tm_refine
                  { FStarC_Syntax_Syntax.b = x1;
                    FStarC_Syntax_Syntax.phi = f1;_})
                   ->
                   let uu___6 = head_matches t01 x1.FStarC_Syntax_Syntax.sort in
                   if uu___6
                   then
                     let uu___7 =
                       universe_of_well_typed_term g
                         x1.FStarC_Syntax_Syntax.sort in
                     (fun ctx01 cache01 ->
                        let uu___8 = uu___7 ctx01 cache01 in
                        match uu___8 with
                        | Success ((x2, g11), cache11) ->
                            let uu___9 =
                              let uu___10 =
                                let uu___11 =
                                  check_relation1 g EQUALITY t01
                                    x1.FStarC_Syntax_Syntax.sort in
                                fun ctx02 cache02 ->
                                  let uu___12 = uu___11 ctx02 cache02 in
                                  match uu___12 with
                                  | Success ((x3, g12), cache12) ->
                                      let uu___13 =
                                        let uu___14 =
                                          let g0 = g in
                                          let uu___15 =
                                            let uu___16 =
                                              FStarC_Syntax_Syntax.mk_binder
                                                x1 in
                                            open_term g uu___16 f1 in
                                          match uu___15 with
                                          | (g2, b1, f11) ->
                                              (fun ctx03 cache03 ->
                                                 let uu___16 =
                                                   guard_not_allowed ctx03
                                                     cache03 in
                                                 match uu___16 with
                                                 | Success
                                                     ((x4, g13), cache13) ->
                                                     let uu___17 =
                                                       let uu___18 =
                                                         if x4
                                                         then
                                                           let uu___19 =
                                                             check_relation1
                                                               g2 EQUALITY
                                                               FStarC_Syntax_Util.t_true
                                                               f11 in
                                                           with_binders g0
                                                             [b1] [x2]
                                                             uu___19
                                                         else
                                                           (match rel with
                                                            | EQUALITY ->
                                                                let uu___20 =
                                                                  let uu___21
                                                                    =
                                                                    check_relation1
                                                                    g2
                                                                    EQUALITY
                                                                    FStarC_Syntax_Util.t_true
                                                                    f11 in
                                                                  fun ctx
                                                                    cache ->
                                                                    let uu___22
                                                                    =
                                                                    uu___21
                                                                    ctx cache in
                                                                    match uu___22
                                                                    with
                                                                    | 
                                                                    Error
                                                                    uu___23
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    guard g2
                                                                    f11 in
                                                                    uu___24
                                                                    ctx cache
                                                                    | 
                                                                    res ->
                                                                    res in
                                                                with_binders
                                                                  g0 
                                                                  [b1] 
                                                                  [x2]
                                                                  uu___20
                                                            | SUBTYPING
                                                                (FStar_Pervasives_Native.Some
                                                                tm) ->
                                                                let uu___20 =
                                                                  FStarC_Syntax_Subst.subst
                                                                    [
                                                                    FStarC_Syntax_Syntax.NT
                                                                    ((b1.FStarC_Syntax_Syntax.binder_bv),
                                                                    tm)] f11 in
                                                                guard g0
                                                                  uu___20
                                                            | SUBTYPING
                                                                (FStar_Pervasives_Native.None)
                                                                ->
                                                                let uu___20 =
                                                                  FStarC_Syntax_Util.mk_forall
                                                                    x2
                                                                    b1.FStarC_Syntax_Syntax.binder_bv
                                                                    f11 in
                                                                guard g0
                                                                  uu___20) in
                                                       uu___18 ctx03 cache13 in
                                                     (match uu___17 with
                                                      | Success
                                                          ((y, g21), cache2)
                                                          ->
                                                          let uu___18 =
                                                            let uu___19 =
                                                              let uu___20 =
                                                                and_pre g13
                                                                  g21 in
                                                              ((), uu___20) in
                                                            (uu___19, cache2) in
                                                          Success uu___18
                                                      | err1 -> err1)
                                                 | Error err1 -> Error err1) in
                                        uu___14 ctx02 cache12 in
                                      (match uu___13 with
                                       | Success ((y, g2), cache2) ->
                                           let uu___14 =
                                             let uu___15 =
                                               let uu___16 = and_pre g12 g2 in
                                               ((), uu___16) in
                                             (uu___15, cache2) in
                                           Success uu___14
                                       | err1 -> err1)
                                  | Error err1 -> Error err1 in
                              uu___10 ctx01 cache11 in
                            (match uu___9 with
                             | Success ((y, g2), cache2) ->
                                 let uu___10 =
                                   let uu___11 =
                                     let uu___12 = and_pre g11 g2 in
                                     ((), uu___12) in
                                   (uu___11, cache2) in
                                 Success uu___10
                             | err1 -> err1)
                        | Error err1 -> Error err1)
                   else
                     (let uu___8 =
                        maybe_unfold t01 x1.FStarC_Syntax_Syntax.sort in
                      fun ctx01 cache01 ->
                        let uu___9 = uu___8 ctx01 cache01 in
                        match uu___9 with
                        | Success ((x2, g11), cache11) ->
                            let uu___10 =
                              let uu___11 =
                                match x2 with
                                | FStar_Pervasives_Native.None ->
                                    fallback t01 t11
                                | FStar_Pervasives_Native.Some (t02, t12) ->
                                    let rhs =
                                      FStarC_Syntax_Syntax.mk
                                        (FStarC_Syntax_Syntax.Tm_refine
                                           {
                                             FStarC_Syntax_Syntax.b =
                                               {
                                                 FStarC_Syntax_Syntax.ppname
                                                   =
                                                   (x1.FStarC_Syntax_Syntax.ppname);
                                                 FStarC_Syntax_Syntax.index =
                                                   (x1.FStarC_Syntax_Syntax.index);
                                                 FStarC_Syntax_Syntax.sort =
                                                   t12
                                               };
                                             FStarC_Syntax_Syntax.phi = f1
                                           }) t12.FStarC_Syntax_Syntax.pos in
                                    let uu___12 =
                                      FStarC_Syntax_Util.flatten_refinement
                                        rhs in
                                    check_relation1 g rel t02 uu___12 in
                              uu___11 ctx01 cache11 in
                            (match uu___10 with
                             | Success ((y, g2), cache2) ->
                                 let uu___11 =
                                   let uu___12 =
                                     let uu___13 = and_pre g11 g2 in
                                     ((), uu___13) in
                                   (uu___12, cache2) in
                                 Success uu___11
                             | err1 -> err1)
                        | Error err1 -> Error err1)
               | (FStarC_Syntax_Syntax.Tm_uinst uu___5, uu___6) ->
                   let head_matches1 = head_matches t01 t11 in
                   let uu___7 = FStarC_Syntax_Util.leftmost_head_and_args t01 in
                   (match uu___7 with
                    | (head0, args0) ->
                        let uu___8 =
                          FStarC_Syntax_Util.leftmost_head_and_args t11 in
                        (match uu___8 with
                         | (head1, args1) ->
                             if
                               Prims.op_Negation
                                 (head_matches1 &&
                                    ((FStarC_List.length args0) =
                                       (FStarC_List.length args1)))
                             then maybe_unfold_and_retry t01 t11
                             else
                               (let compare_head_and_args uu___10 =
                                  let uu___11 =
                                    let uu___12 =
                                      check_relation1 g EQUALITY head0 head1 in
                                    fun ctx01 cache01 ->
                                      let uu___13 = uu___12 ctx01 cache01 in
                                      match uu___13 with
                                      | Success ((x1, g11), cache11) ->
                                          let uu___14 =
                                            let uu___15 =
                                              check_relation_args g EQUALITY
                                                args0 args1 in
                                            uu___15 ctx01 cache11 in
                                          (match uu___14 with
                                           | Success ((y, g2), cache2) ->
                                               let uu___15 =
                                                 let uu___16 =
                                                   let uu___17 =
                                                     and_pre g11 g2 in
                                                   ((), uu___17) in
                                                 (uu___16, cache2) in
                                               Success uu___15
                                           | err1 -> err1)
                                      | Error err1 -> Error err1 in
                                  fun ctx cache ->
                                    let uu___12 = uu___11 ctx cache in
                                    match uu___12 with
                                    | Error uu___13 ->
                                        let uu___14 =
                                          maybe_unfold_side_and_retry Both
                                            t01 t11 in
                                        uu___14 ctx cache
                                    | res -> res in
                                let uu___10 =
                                  (guard_ok && (rel = EQUALITY)) &&
                                    ((equatable g t01) || (equatable g t11)) in
                                if uu___10
                                then
                                  let uu___11 =
                                    let uu___12 = compare_head_and_args () in
                                    no_guard uu___12 in
                                  fun ctx cache ->
                                    let uu___12 = uu___11 ctx cache in
                                    match uu___12 with
                                    | Error uu___13 ->
                                        let uu___14 = emit_guard t01 t11 in
                                        uu___14 ctx cache
                                    | res -> res
                                else compare_head_and_args ())))
               | (FStarC_Syntax_Syntax.Tm_fvar uu___5, uu___6) ->
                   let head_matches1 = head_matches t01 t11 in
                   let uu___7 = FStarC_Syntax_Util.leftmost_head_and_args t01 in
                   (match uu___7 with
                    | (head0, args0) ->
                        let uu___8 =
                          FStarC_Syntax_Util.leftmost_head_and_args t11 in
                        (match uu___8 with
                         | (head1, args1) ->
                             if
                               Prims.op_Negation
                                 (head_matches1 &&
                                    ((FStarC_List.length args0) =
                                       (FStarC_List.length args1)))
                             then maybe_unfold_and_retry t01 t11
                             else
                               (let compare_head_and_args uu___10 =
                                  let uu___11 =
                                    let uu___12 =
                                      check_relation1 g EQUALITY head0 head1 in
                                    fun ctx01 cache01 ->
                                      let uu___13 = uu___12 ctx01 cache01 in
                                      match uu___13 with
                                      | Success ((x1, g11), cache11) ->
                                          let uu___14 =
                                            let uu___15 =
                                              check_relation_args g EQUALITY
                                                args0 args1 in
                                            uu___15 ctx01 cache11 in
                                          (match uu___14 with
                                           | Success ((y, g2), cache2) ->
                                               let uu___15 =
                                                 let uu___16 =
                                                   let uu___17 =
                                                     and_pre g11 g2 in
                                                   ((), uu___17) in
                                                 (uu___16, cache2) in
                                               Success uu___15
                                           | err1 -> err1)
                                      | Error err1 -> Error err1 in
                                  fun ctx cache ->
                                    let uu___12 = uu___11 ctx cache in
                                    match uu___12 with
                                    | Error uu___13 ->
                                        let uu___14 =
                                          maybe_unfold_side_and_retry Both
                                            t01 t11 in
                                        uu___14 ctx cache
                                    | res -> res in
                                let uu___10 =
                                  (guard_ok && (rel = EQUALITY)) &&
                                    ((equatable g t01) || (equatable g t11)) in
                                if uu___10
                                then
                                  let uu___11 =
                                    let uu___12 = compare_head_and_args () in
                                    no_guard uu___12 in
                                  fun ctx cache ->
                                    let uu___12 = uu___11 ctx cache in
                                    match uu___12 with
                                    | Error uu___13 ->
                                        let uu___14 = emit_guard t01 t11 in
                                        uu___14 ctx cache
                                    | res -> res
                                else compare_head_and_args ())))
               | (FStarC_Syntax_Syntax.Tm_app uu___5, uu___6) ->
                   let head_matches1 = head_matches t01 t11 in
                   let uu___7 = FStarC_Syntax_Util.leftmost_head_and_args t01 in
                   (match uu___7 with
                    | (head0, args0) ->
                        let uu___8 =
                          FStarC_Syntax_Util.leftmost_head_and_args t11 in
                        (match uu___8 with
                         | (head1, args1) ->
                             if
                               Prims.op_Negation
                                 (head_matches1 &&
                                    ((FStarC_List.length args0) =
                                       (FStarC_List.length args1)))
                             then maybe_unfold_and_retry t01 t11
                             else
                               (let compare_head_and_args uu___10 =
                                  let uu___11 =
                                    let uu___12 =
                                      check_relation1 g EQUALITY head0 head1 in
                                    fun ctx01 cache01 ->
                                      let uu___13 = uu___12 ctx01 cache01 in
                                      match uu___13 with
                                      | Success ((x1, g11), cache11) ->
                                          let uu___14 =
                                            let uu___15 =
                                              check_relation_args g EQUALITY
                                                args0 args1 in
                                            uu___15 ctx01 cache11 in
                                          (match uu___14 with
                                           | Success ((y, g2), cache2) ->
                                               let uu___15 =
                                                 let uu___16 =
                                                   let uu___17 =
                                                     and_pre g11 g2 in
                                                   ((), uu___17) in
                                                 (uu___16, cache2) in
                                               Success uu___15
                                           | err1 -> err1)
                                      | Error err1 -> Error err1 in
                                  fun ctx cache ->
                                    let uu___12 = uu___11 ctx cache in
                                    match uu___12 with
                                    | Error uu___13 ->
                                        let uu___14 =
                                          maybe_unfold_side_and_retry Both
                                            t01 t11 in
                                        uu___14 ctx cache
                                    | res -> res in
                                let uu___10 =
                                  (guard_ok && (rel = EQUALITY)) &&
                                    ((equatable g t01) || (equatable g t11)) in
                                if uu___10
                                then
                                  let uu___11 =
                                    let uu___12 = compare_head_and_args () in
                                    no_guard uu___12 in
                                  fun ctx cache ->
                                    let uu___12 = uu___11 ctx cache in
                                    match uu___12 with
                                    | Error uu___13 ->
                                        let uu___14 = emit_guard t01 t11 in
                                        uu___14 ctx cache
                                    | res -> res
                                else compare_head_and_args ())))
               | (uu___5, FStarC_Syntax_Syntax.Tm_uinst uu___6) ->
                   let head_matches1 = head_matches t01 t11 in
                   let uu___7 = FStarC_Syntax_Util.leftmost_head_and_args t01 in
                   (match uu___7 with
                    | (head0, args0) ->
                        let uu___8 =
                          FStarC_Syntax_Util.leftmost_head_and_args t11 in
                        (match uu___8 with
                         | (head1, args1) ->
                             if
                               Prims.op_Negation
                                 (head_matches1 &&
                                    ((FStarC_List.length args0) =
                                       (FStarC_List.length args1)))
                             then maybe_unfold_and_retry t01 t11
                             else
                               (let compare_head_and_args uu___10 =
                                  let uu___11 =
                                    let uu___12 =
                                      check_relation1 g EQUALITY head0 head1 in
                                    fun ctx01 cache01 ->
                                      let uu___13 = uu___12 ctx01 cache01 in
                                      match uu___13 with
                                      | Success ((x1, g11), cache11) ->
                                          let uu___14 =
                                            let uu___15 =
                                              check_relation_args g EQUALITY
                                                args0 args1 in
                                            uu___15 ctx01 cache11 in
                                          (match uu___14 with
                                           | Success ((y, g2), cache2) ->
                                               let uu___15 =
                                                 let uu___16 =
                                                   let uu___17 =
                                                     and_pre g11 g2 in
                                                   ((), uu___17) in
                                                 (uu___16, cache2) in
                                               Success uu___15
                                           | err1 -> err1)
                                      | Error err1 -> Error err1 in
                                  fun ctx cache ->
                                    let uu___12 = uu___11 ctx cache in
                                    match uu___12 with
                                    | Error uu___13 ->
                                        let uu___14 =
                                          maybe_unfold_side_and_retry Both
                                            t01 t11 in
                                        uu___14 ctx cache
                                    | res -> res in
                                let uu___10 =
                                  (guard_ok && (rel = EQUALITY)) &&
                                    ((equatable g t01) || (equatable g t11)) in
                                if uu___10
                                then
                                  let uu___11 =
                                    let uu___12 = compare_head_and_args () in
                                    no_guard uu___12 in
                                  fun ctx cache ->
                                    let uu___12 = uu___11 ctx cache in
                                    match uu___12 with
                                    | Error uu___13 ->
                                        let uu___14 = emit_guard t01 t11 in
                                        uu___14 ctx cache
                                    | res -> res
                                else compare_head_and_args ())))
               | (uu___5, FStarC_Syntax_Syntax.Tm_fvar uu___6) ->
                   let head_matches1 = head_matches t01 t11 in
                   let uu___7 = FStarC_Syntax_Util.leftmost_head_and_args t01 in
                   (match uu___7 with
                    | (head0, args0) ->
                        let uu___8 =
                          FStarC_Syntax_Util.leftmost_head_and_args t11 in
                        (match uu___8 with
                         | (head1, args1) ->
                             if
                               Prims.op_Negation
                                 (head_matches1 &&
                                    ((FStarC_List.length args0) =
                                       (FStarC_List.length args1)))
                             then maybe_unfold_and_retry t01 t11
                             else
                               (let compare_head_and_args uu___10 =
                                  let uu___11 =
                                    let uu___12 =
                                      check_relation1 g EQUALITY head0 head1 in
                                    fun ctx01 cache01 ->
                                      let uu___13 = uu___12 ctx01 cache01 in
                                      match uu___13 with
                                      | Success ((x1, g11), cache11) ->
                                          let uu___14 =
                                            let uu___15 =
                                              check_relation_args g EQUALITY
                                                args0 args1 in
                                            uu___15 ctx01 cache11 in
                                          (match uu___14 with
                                           | Success ((y, g2), cache2) ->
                                               let uu___15 =
                                                 let uu___16 =
                                                   let uu___17 =
                                                     and_pre g11 g2 in
                                                   ((), uu___17) in
                                                 (uu___16, cache2) in
                                               Success uu___15
                                           | err1 -> err1)
                                      | Error err1 -> Error err1 in
                                  fun ctx cache ->
                                    let uu___12 = uu___11 ctx cache in
                                    match uu___12 with
                                    | Error uu___13 ->
                                        let uu___14 =
                                          maybe_unfold_side_and_retry Both
                                            t01 t11 in
                                        uu___14 ctx cache
                                    | res -> res in
                                let uu___10 =
                                  (guard_ok && (rel = EQUALITY)) &&
                                    ((equatable g t01) || (equatable g t11)) in
                                if uu___10
                                then
                                  let uu___11 =
                                    let uu___12 = compare_head_and_args () in
                                    no_guard uu___12 in
                                  fun ctx cache ->
                                    let uu___12 = uu___11 ctx cache in
                                    match uu___12 with
                                    | Error uu___13 ->
                                        let uu___14 = emit_guard t01 t11 in
                                        uu___14 ctx cache
                                    | res -> res
                                else compare_head_and_args ())))
               | (uu___5, FStarC_Syntax_Syntax.Tm_app uu___6) ->
                   let head_matches1 = head_matches t01 t11 in
                   let uu___7 = FStarC_Syntax_Util.leftmost_head_and_args t01 in
                   (match uu___7 with
                    | (head0, args0) ->
                        let uu___8 =
                          FStarC_Syntax_Util.leftmost_head_and_args t11 in
                        (match uu___8 with
                         | (head1, args1) ->
                             if
                               Prims.op_Negation
                                 (head_matches1 &&
                                    ((FStarC_List.length args0) =
                                       (FStarC_List.length args1)))
                             then maybe_unfold_and_retry t01 t11
                             else
                               (let compare_head_and_args uu___10 =
                                  let uu___11 =
                                    let uu___12 =
                                      check_relation1 g EQUALITY head0 head1 in
                                    fun ctx01 cache01 ->
                                      let uu___13 = uu___12 ctx01 cache01 in
                                      match uu___13 with
                                      | Success ((x1, g11), cache11) ->
                                          let uu___14 =
                                            let uu___15 =
                                              check_relation_args g EQUALITY
                                                args0 args1 in
                                            uu___15 ctx01 cache11 in
                                          (match uu___14 with
                                           | Success ((y, g2), cache2) ->
                                               let uu___15 =
                                                 let uu___16 =
                                                   let uu___17 =
                                                     and_pre g11 g2 in
                                                   ((), uu___17) in
                                                 (uu___16, cache2) in
                                               Success uu___15
                                           | err1 -> err1)
                                      | Error err1 -> Error err1 in
                                  fun ctx cache ->
                                    let uu___12 = uu___11 ctx cache in
                                    match uu___12 with
                                    | Error uu___13 ->
                                        let uu___14 =
                                          maybe_unfold_side_and_retry Both
                                            t01 t11 in
                                        uu___14 ctx cache
                                    | res -> res in
                                let uu___10 =
                                  (guard_ok && (rel = EQUALITY)) &&
                                    ((equatable g t01) || (equatable g t11)) in
                                if uu___10
                                then
                                  let uu___11 =
                                    let uu___12 = compare_head_and_args () in
                                    no_guard uu___12 in
                                  fun ctx cache ->
                                    let uu___12 = uu___11 ctx cache in
                                    match uu___12 with
                                    | Error uu___13 ->
                                        let uu___14 = emit_guard t01 t11 in
                                        uu___14 ctx cache
                                    | res -> res
                                else compare_head_and_args ())))
               | (FStarC_Syntax_Syntax.Tm_abs
                  { FStarC_Syntax_Syntax.bs = b0::b1::bs;
                    FStarC_Syntax_Syntax.body = body;
                    FStarC_Syntax_Syntax.rc_opt = ropt;_},
                  uu___5) ->
                   let t02 = curry_abs b0 b1 bs body ropt in
                   check_relation1 g rel t02 t11
               | (uu___5, FStarC_Syntax_Syntax.Tm_abs
                  { FStarC_Syntax_Syntax.bs = b0::b1::bs;
                    FStarC_Syntax_Syntax.body = body;
                    FStarC_Syntax_Syntax.rc_opt = ropt;_})
                   ->
                   let t12 = curry_abs b0 b1 bs body ropt in
                   check_relation1 g rel t01 t12
               | (FStarC_Syntax_Syntax.Tm_abs
                  { FStarC_Syntax_Syntax.bs = b0::[];
                    FStarC_Syntax_Syntax.body = body0;
                    FStarC_Syntax_Syntax.rc_opt = uu___5;_},
                  FStarC_Syntax_Syntax.Tm_abs
                  { FStarC_Syntax_Syntax.bs = b1::[];
                    FStarC_Syntax_Syntax.body = body1;
                    FStarC_Syntax_Syntax.rc_opt = uu___6;_})
                   ->
                   let uu___7 =
                     check_relation1 g EQUALITY
                       (b0.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort
                       (b1.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                   (fun ctx01 cache01 ->
                      let uu___8 = uu___7 ctx01 cache01 in
                      match uu___8 with
                      | Success ((x1, g11), cache11) ->
                          let uu___9 =
                            let uu___10 =
                              let uu___11 =
                                check_bqual
                                  b0.FStarC_Syntax_Syntax.binder_qual
                                  b1.FStarC_Syntax_Syntax.binder_qual in
                              fun ctx02 cache02 ->
                                let uu___12 = uu___11 ctx02 cache02 in
                                match uu___12 with
                                | Success ((x2, g12), cache12) ->
                                    let uu___13 =
                                      let uu___14 =
                                        let uu___15 =
                                          check_positivity_qual EQUALITY
                                            b0.FStarC_Syntax_Syntax.binder_positivity
                                            b1.FStarC_Syntax_Syntax.binder_positivity in
                                        fun ctx03 cache03 ->
                                          let uu___16 = uu___15 ctx03 cache03 in
                                          match uu___16 with
                                          | Success ((x3, g13), cache13) ->
                                              let uu___17 =
                                                let uu___18 =
                                                  let uu___19 =
                                                    universe_of_well_typed_term
                                                      g
                                                      (b0.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                                                  fun ctx04 cache04 ->
                                                    let uu___20 =
                                                      uu___19 ctx04 cache04 in
                                                    match uu___20 with
                                                    | Success
                                                        ((x4, g14), cache14)
                                                        ->
                                                        let uu___21 =
                                                          let uu___22 =
                                                            let g0 = g in
                                                            let uu___23 =
                                                              open_term g b0
                                                                body0 in
                                                            match uu___23
                                                            with
                                                            | (g2, b01,
                                                               body01) ->
                                                                let body11 =
                                                                  FStarC_Syntax_Subst.subst
                                                                    [
                                                                    FStarC_Syntax_Syntax.DB
                                                                    (Prims.int_zero,
                                                                    (b01.FStarC_Syntax_Syntax.binder_bv))]
                                                                    body1 in
                                                                let uu___24 =
                                                                  check_relation1
                                                                    g2
                                                                    EQUALITY
                                                                    body01
                                                                    body11 in
                                                                with_binders
                                                                  g0 
                                                                  [b01] 
                                                                  [x4]
                                                                  uu___24 in
                                                          uu___22 ctx04
                                                            cache14 in
                                                        (match uu___21 with
                                                         | Success
                                                             ((y, g2),
                                                              cache2)
                                                             ->
                                                             let uu___22 =
                                                               let uu___23 =
                                                                 let uu___24
                                                                   =
                                                                   and_pre
                                                                    g14 g2 in
                                                                 ((),
                                                                   uu___24) in
                                                               (uu___23,
                                                                 cache2) in
                                                             Success uu___22
                                                         | err1 -> err1)
                                                    | Error err1 ->
                                                        Error err1 in
                                                uu___18 ctx03 cache13 in
                                              (match uu___17 with
                                               | Success ((y, g2), cache2) ->
                                                   let uu___18 =
                                                     let uu___19 =
                                                       let uu___20 =
                                                         and_pre g13 g2 in
                                                       ((), uu___20) in
                                                     (uu___19, cache2) in
                                                   Success uu___18
                                               | err1 -> err1)
                                          | Error err1 -> Error err1 in
                                      uu___14 ctx02 cache12 in
                                    (match uu___13 with
                                     | Success ((y, g2), cache2) ->
                                         let uu___14 =
                                           let uu___15 =
                                             let uu___16 = and_pre g12 g2 in
                                             ((), uu___16) in
                                           (uu___15, cache2) in
                                         Success uu___14
                                     | err1 -> err1)
                                | Error err1 -> Error err1 in
                            uu___10 ctx01 cache11 in
                          (match uu___9 with
                           | Success ((y, g2), cache2) ->
                               let uu___10 =
                                 let uu___11 =
                                   let uu___12 = and_pre g11 g2 in
                                   ((), uu___12) in
                                 (uu___11, cache2) in
                               Success uu___10
                           | err1 -> err1)
                      | Error err1 -> Error err1)
               | (FStarC_Syntax_Syntax.Tm_arrow
                  { FStarC_Syntax_Syntax.bs1 = x0::x1::xs;
                    FStarC_Syntax_Syntax.comp = c0;_},
                  uu___5) ->
                   let uu___6 = curry_arrow x0 (x1 :: xs) c0 in
                   check_relation1 g rel uu___6 t11
               | (uu___5, FStarC_Syntax_Syntax.Tm_arrow
                  { FStarC_Syntax_Syntax.bs1 = x0::x1::xs;
                    FStarC_Syntax_Syntax.comp = c1;_})
                   ->
                   let uu___6 = curry_arrow x0 (x1 :: xs) c1 in
                   check_relation1 g rel t01 uu___6
               | (FStarC_Syntax_Syntax.Tm_arrow
                  { FStarC_Syntax_Syntax.bs1 = x0::[];
                    FStarC_Syntax_Syntax.comp = c0;_},
                  FStarC_Syntax_Syntax.Tm_arrow
                  { FStarC_Syntax_Syntax.bs1 = x1::[];
                    FStarC_Syntax_Syntax.comp = c1;_})
                   ->
                   (fun ctx cache ->
                      let ctx1 =
                        {
                          no_guard = (ctx.no_guard);
                          unfolding_ok = (ctx.unfolding_ok);
                          error_context =
                            (("subtype arrow", FStar_Pervasives_Native.None)
                            :: (ctx.error_context))
                        } in
                      let uu___5 =
                        let uu___6 =
                          check_bqual x0.FStarC_Syntax_Syntax.binder_qual
                            x1.FStarC_Syntax_Syntax.binder_qual in
                        fun ctx01 cache01 ->
                          let uu___7 = uu___6 ctx01 cache01 in
                          match uu___7 with
                          | Success ((x2, g11), cache11) ->
                              let uu___8 =
                                let uu___9 =
                                  let uu___10 =
                                    check_positivity_qual rel
                                      x0.FStarC_Syntax_Syntax.binder_positivity
                                      x1.FStarC_Syntax_Syntax.binder_positivity in
                                  fun ctx02 cache02 ->
                                    let uu___11 = uu___10 ctx02 cache02 in
                                    match uu___11 with
                                    | Success ((x3, g12), cache12) ->
                                        let uu___12 =
                                          let uu___13 =
                                            let uu___14 =
                                              universe_of_well_typed_term g
                                                (x1.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                                            fun ctx03 cache03 ->
                                              let uu___15 =
                                                uu___14 ctx03 cache03 in
                                              match uu___15 with
                                              | Success ((x4, g13), cache13)
                                                  ->
                                                  let uu___16 =
                                                    let uu___17 =
                                                      let uu___18 =
                                                        open_comp g x1 c1 in
                                                      match uu___18 with
                                                      | (g_x1, x11, c11) ->
                                                          let c01 =
                                                            FStarC_Syntax_Subst.subst_comp
                                                              [FStarC_Syntax_Syntax.DB
                                                                 (Prims.int_zero,
                                                                   (x11.FStarC_Syntax_Syntax.binder_bv))]
                                                              c0 in
                                                          let uu___19 =
                                                            let rel_arg =
                                                              match rel with
                                                              | EQUALITY ->
                                                                  EQUALITY
                                                              | uu___20 ->
                                                                  let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_to_name
                                                                    x11.FStarC_Syntax_Syntax.binder_bv in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___22 in
                                                                  SUBTYPING
                                                                    uu___21 in
                                                            let rel_comp =
                                                              match rel with
                                                              | EQUALITY ->
                                                                  EQUALITY
                                                              | SUBTYPING e
                                                                  ->
                                                                  let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    FStarC_Syntax_Util.is_pure_or_ghost_comp
                                                                    c01 in
                                                                    if
                                                                    uu___21
                                                                    then
                                                                    op_let_Question
                                                                    e
                                                                    (fun e1
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    FStarC_Syntax_Util.args_of_binders
                                                                    [x11] in
                                                                    FStar_Pervasives_Native.snd
                                                                    uu___24 in
                                                                    FStarC_Syntax_Syntax.mk_Tm_app
                                                                    e1
                                                                    uu___23
                                                                    FStarC_Range_Type.dummyRange in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___22)
                                                                    else
                                                                    FStar_Pervasives_Native.None in
                                                                  SUBTYPING
                                                                    uu___20 in
                                                            let uu___20 =
                                                              check_relation1
                                                                g rel_arg
                                                                (x11.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort
                                                                (x0.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                                                            fun ctx04 cache04
                                                              ->
                                                              let uu___21 =
                                                                uu___20 ctx04
                                                                  cache04 in
                                                              match uu___21
                                                              with
                                                              | Success
                                                                  ((x5, g14),
                                                                   cache14)
                                                                  ->
                                                                  let uu___22
                                                                    =
                                                                    let uu___23
                                                                    ctx2
                                                                    cache2 =
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
                                                                    let uu___24
                                                                    =
                                                                    check_relation_comp
                                                                    g_x1
                                                                    rel_comp
                                                                    c01 c11 in
                                                                    uu___24
                                                                    ctx3
                                                                    cache2 in
                                                                    uu___23
                                                                    ctx04
                                                                    cache14 in
                                                                  (match uu___22
                                                                   with
                                                                   | 
                                                                   Success
                                                                    ((y, g2),
                                                                    cache2)
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    and_pre
                                                                    g14 g2 in
                                                                    ((),
                                                                    uu___25) in
                                                                    (uu___24,
                                                                    cache2) in
                                                                    Success
                                                                    uu___23
                                                                   | 
                                                                   err1 ->
                                                                    err1)
                                                              | Error err1 ->
                                                                  Error err1 in
                                                          with_binders g
                                                            [x11] [x4]
                                                            uu___19 in
                                                    uu___17 ctx03 cache13 in
                                                  (match uu___16 with
                                                   | Success
                                                       ((y, g2), cache2) ->
                                                       let uu___17 =
                                                         let uu___18 =
                                                           let uu___19 =
                                                             and_pre g13 g2 in
                                                           ((), uu___19) in
                                                         (uu___18, cache2) in
                                                       Success uu___17
                                                   | err1 -> err1)
                                              | Error err1 -> Error err1 in
                                          uu___13 ctx02 cache12 in
                                        (match uu___12 with
                                         | Success ((y, g2), cache2) ->
                                             let uu___13 =
                                               let uu___14 =
                                                 let uu___15 = and_pre g12 g2 in
                                                 ((), uu___15) in
                                               (uu___14, cache2) in
                                             Success uu___13
                                         | err1 -> err1)
                                    | Error err1 -> Error err1 in
                                uu___9 ctx01 cache11 in
                              (match uu___8 with
                               | Success ((y, g2), cache2) ->
                                   let uu___9 =
                                     let uu___10 =
                                       let uu___11 = and_pre g11 g2 in
                                       ((), uu___11) in
                                     (uu___10, cache2) in
                                   Success uu___9
                               | err1 -> err1)
                          | Error err1 -> Error err1 in
                      uu___5 ctx1 cache)
               | (FStarC_Syntax_Syntax.Tm_match
                  { FStarC_Syntax_Syntax.scrutinee = e0;
                    FStarC_Syntax_Syntax.ret_opt = uu___5;
                    FStarC_Syntax_Syntax.brs = brs0;
                    FStarC_Syntax_Syntax.rc_opt1 = uu___6;_},
                  FStarC_Syntax_Syntax.Tm_match
                  { FStarC_Syntax_Syntax.scrutinee = e1;
                    FStarC_Syntax_Syntax.ret_opt = uu___7;
                    FStarC_Syntax_Syntax.brs = brs1;
                    FStarC_Syntax_Syntax.rc_opt1 = uu___8;_})
                   ->
                   let relate_branch br0 br1 uu___9 =
                     match (br0, br1) with
                     | ((p0, FStar_Pervasives_Native.None, body0),
                        (p1, FStar_Pervasives_Native.None, body1)) ->
                         let uu___10 =
                           let uu___11 = FStarC_Syntax_Syntax.eq_pat p0 p1 in
                           Prims.op_Negation uu___11 in
                         if uu___10
                         then fail_str "patterns not equal"
                         else
                           (let uu___12 =
                              open_branches_eq_pat g
                                (p0, FStar_Pervasives_Native.None, body0)
                                (p1, FStar_Pervasives_Native.None, body1) in
                            match uu___12 with
                            | (g', (p01, uu___13, body01),
                               (p11, uu___14, body11)) ->
                                let uu___15 =
                                  FStarC_TypeChecker_PatternUtils.raw_pat_as_exp
                                    g.tcenv p01 in
                                (match uu___15 with
                                 | FStar_Pervasives_Native.Some
                                     (uu___16, bvs0) ->
                                     let bs0 =
                                       FStarC_List.map
                                         FStarC_Syntax_Syntax.mk_binder bvs0 in
                                     let uu___17 = check_binders g bs0 in
                                     (fun ctx01 cache01 ->
                                        let uu___18 = uu___17 ctx01 cache01 in
                                        match uu___18 with
                                        | Success ((x1, g11), cache11) ->
                                            let uu___19 =
                                              let uu___20 ctx cache =
                                                let ctx1 =
                                                  {
                                                    no_guard = (ctx.no_guard);
                                                    unfolding_ok =
                                                      (ctx.unfolding_ok);
                                                    error_context =
                                                      (("relate_branch",
                                                         FStar_Pervasives_Native.None)
                                                      :: (ctx.error_context))
                                                  } in
                                                let uu___21 =
                                                  let uu___22 =
                                                    check_relation1 g' rel
                                                      body01 body11 in
                                                  with_binders g bs0 x1
                                                    uu___22 in
                                                uu___21 ctx1 cache in
                                              uu___20 ctx01 cache11 in
                                            (match uu___19 with
                                             | Success ((y, g2), cache2) ->
                                                 let uu___20 =
                                                   let uu___21 =
                                                     let uu___22 =
                                                       and_pre g11 g2 in
                                                     ((), uu___22) in
                                                   (uu___21, cache2) in
                                                 Success uu___20
                                             | err1 -> err1)
                                        | Error err1 -> Error err1)
                                 | uu___16 ->
                                     fail_str
                                       "raw_pat_as_exp failed in check_equality match rule"))
                     | uu___10 ->
                         fail_str "Core does not support branches with when" in
                   let uu___9 =
                     let uu___10 = check_relation1 g EQUALITY e0 e1 in
                     fun ctx01 cache01 ->
                       let uu___11 = uu___10 ctx01 cache01 in
                       match uu___11 with
                       | Success ((x1, g11), cache11) ->
                           let uu___12 =
                             let uu___13 = iter2 brs0 brs1 relate_branch () in
                             uu___13 ctx01 cache11 in
                           (match uu___12 with
                            | Success ((y, g2), cache2) ->
                                let uu___13 =
                                  let uu___14 =
                                    let uu___15 = and_pre g11 g2 in
                                    ((), uu___15) in
                                  (uu___14, cache2) in
                                Success uu___13
                            | err1 -> err1)
                       | Error err1 -> Error err1 in
                   (fun ctx cache ->
                      let uu___10 = uu___9 ctx cache in
                      match uu___10 with
                      | Error uu___11 ->
                          let uu___12 = fallback t01 t11 in uu___12 ctx cache
                      | res -> res)
               | uu___5 -> fallback t01 t11) in
          uu___2 ctx0 cache1 in
        (match uu___1 with
         | Success ((y, g2), cache2) ->
             let uu___2 =
               let uu___3 = let uu___4 = and_pre g1 g2 in ((), uu___4) in
               (uu___3, cache2) in
             Success uu___2
         | err1 -> err1)
    | Error err1 -> Error err1
and check_relation (g : env) (rel : relation) (t0 : FStarC_Syntax_Syntax.typ)
  (t1 : FStarC_Syntax_Syntax.typ) : unit result=
  let uu___ = FStarC_Effect.op_Bang dbg in
  if uu___
  then
    fun ctx cache ->
      ((let uu___2 =
          FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t0 in
        let uu___3 = FStarC_Class_Show.show showable_rel rel in
        let uu___4 =
          FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t1 in
        FStarC_Format.print3 "check_relation (%s, %s, %s) {\n" uu___2 uu___3
          uu___4);
       (let res =
          let uu___2 = check_relation' g rel t0 t1 in uu___2 ctx cache in
        match res with
        | Error err ->
            ((let uu___3 =
                FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t0 in
              let uu___4 = FStarC_Class_Show.show showable_rel rel in
              let uu___5 =
                FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t1 in
              let uu___6 = FStarC_Class_Show.show showable_error err in
              FStarC_Format.print4
                "} check_relation (%s, %s, %s) failed with %s\n" uu___3
                uu___4 uu___5 uu___6);
             Error err)
        | Success ((uu___2, g1), cache1) ->
            ((let uu___4 =
                FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t0 in
              let uu___5 = FStarC_Class_Show.show showable_rel rel in
              let uu___6 =
                FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t1 in
              let uu___7 =
                FStarC_Class_Show.show
                  (FStarC_Class_Show.show_option
                     FStarC_Syntax_Print.showable_term) g1 in
              FStarC_Format.print4
                "} check_relation  (%s, %s, %s) succeeded with guard %s\n"
                uu___4 uu___5 uu___6 uu___7);
             res)))
  else check_relation' g rel t0 t1
and check_relation_args (g : env) (rel : relation)
  (a0 : FStarC_Syntax_Syntax.args) (a1 : FStarC_Syntax_Syntax.args) :
  unit result=
  if (FStarC_List.length a0) = (FStarC_List.length a1)
  then
    iter2 a0 a1
      (fun uu___ uu___1 uu___2 ->
         match (uu___, uu___1) with
         | ((t0, q0), (t1, q1)) ->
             let uu___3 = check_aqual q0 q1 in
             (fun ctx0 cache0 ->
                let uu___4 = uu___3 ctx0 cache0 in
                match uu___4 with
                | Success ((x, g1), cache1) ->
                    let uu___5 =
                      let uu___6 = check_relation g rel t0 t1 in
                      uu___6 ctx0 cache1 in
                    (match uu___5 with
                     | Success ((y, g2), cache2) ->
                         let uu___6 =
                           let uu___7 =
                             let uu___8 = and_pre g1 g2 in ((), uu___8) in
                           (uu___7, cache2) in
                         Success uu___6
                     | err -> err)
                | Error err -> Error err)) ()
  else fail_str "Unequal number of arguments"
and check_relation_comp (g : env) (rel : relation)
  (c0 : FStarC_Syntax_Syntax.comp) (c1 : FStarC_Syntax_Syntax.comp) :
  unit result=
  let destruct_comp c =
    let uu___ = FStarC_Syntax_Util.is_total_comp c in
    if uu___
    then
      let uu___1 =
        let uu___2 = FStarC_Syntax_Util.comp_result c in (E_Total, uu___2) in
      FStar_Pervasives_Native.Some uu___1
    else
      (let uu___2 = FStarC_Syntax_Util.is_tot_or_gtot_comp c in
       if uu___2
       then
         let uu___3 =
           let uu___4 = FStarC_Syntax_Util.comp_result c in (E_Ghost, uu___4) in
         FStar_Pervasives_Native.Some uu___3
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
      then
        (fun uu___3 cache ->
           Success (((), FStar_Pervasives_Native.None), cache))
      else
        (let ct_eq res0 args0 res1 args1 =
           let uu___4 = check_relation g EQUALITY res0 res1 in
           fun ctx0 cache0 ->
             let uu___5 = uu___4 ctx0 cache0 in
             match uu___5 with
             | Success ((x, g1), cache1) ->
                 let uu___6 =
                   let uu___7 = check_relation_args g EQUALITY args0 args1 in
                   uu___7 ctx0 cache1 in
                 (match uu___6 with
                  | Success ((y, g2), cache2) ->
                      let uu___7 =
                        let uu___8 =
                          let uu___9 = and_pre g1 g2 in ((), uu___9) in
                        (uu___8, cache2) in
                      Success uu___7
                  | err -> err)
             | Error err -> Error err in
         let uu___4 = FStarC_Syntax_Util.comp_eff_name_res_and_args c0 in
         match uu___4 with
         | (eff0, res0, args0) ->
             let uu___5 = FStarC_Syntax_Util.comp_eff_name_res_and_args c1 in
             (match uu___5 with
              | (eff1, res1, args1) ->
                  let uu___6 = FStarC_Ident.lid_equals eff0 eff1 in
                  if uu___6
                  then ct_eq res0 args0 res1 args1
                  else
                    (let ct0 =
                       FStarC_TypeChecker_Env.unfold_effect_abbrev g.tcenv c0 in
                     let ct1 =
                       FStarC_TypeChecker_Env.unfold_effect_abbrev g.tcenv c1 in
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
                            let uu___12 =
                              FStarC_Errors_Msg.text
                                "Subcomp failed: Unequal computation types" in
                            let uu___13 =
                              let uu___14 =
                                FStarC_Class_PP.pp FStarC_Ident.pretty_lident
                                  ct0.FStarC_Syntax_Syntax.effect_name in
                              let uu___15 =
                                let uu___16 =
                                  FStarC_Class_PP.pp
                                    FStarC_Ident.pretty_lident
                                    ct1.FStarC_Syntax_Syntax.effect_name in
                                FStar_Pprint.op_Hat_Slash_Hat
                                  (FStar_Pprint.doc_of_string "and") uu___16 in
                              FStar_Pprint.op_Hat_Slash_Hat uu___14 uu___15 in
                            FStar_Pprint.op_Hat_Slash_Hat uu___12 uu___13 in
                          [uu___11] in
                        fail uu___10))))
  | (uu___1, FStar_Pervasives_Native.None) ->
      let uu___2 =
        let uu___3 =
          FStarC_TypeChecker_TermEqAndSimplify.eq_comp g.tcenv c0 c1 in
        uu___3 = FStarC_TypeChecker_TermEqAndSimplify.Equal in
      if uu___2
      then
        (fun uu___3 cache ->
           Success (((), FStar_Pervasives_Native.None), cache))
      else
        (let ct_eq res0 args0 res1 args1 =
           let uu___4 = check_relation g EQUALITY res0 res1 in
           fun ctx0 cache0 ->
             let uu___5 = uu___4 ctx0 cache0 in
             match uu___5 with
             | Success ((x, g1), cache1) ->
                 let uu___6 =
                   let uu___7 = check_relation_args g EQUALITY args0 args1 in
                   uu___7 ctx0 cache1 in
                 (match uu___6 with
                  | Success ((y, g2), cache2) ->
                      let uu___7 =
                        let uu___8 =
                          let uu___9 = and_pre g1 g2 in ((), uu___9) in
                        (uu___8, cache2) in
                      Success uu___7
                  | err -> err)
             | Error err -> Error err in
         let uu___4 = FStarC_Syntax_Util.comp_eff_name_res_and_args c0 in
         match uu___4 with
         | (eff0, res0, args0) ->
             let uu___5 = FStarC_Syntax_Util.comp_eff_name_res_and_args c1 in
             (match uu___5 with
              | (eff1, res1, args1) ->
                  let uu___6 = FStarC_Ident.lid_equals eff0 eff1 in
                  if uu___6
                  then ct_eq res0 args0 res1 args1
                  else
                    (let ct0 =
                       FStarC_TypeChecker_Env.unfold_effect_abbrev g.tcenv c0 in
                     let ct1 =
                       FStarC_TypeChecker_Env.unfold_effect_abbrev g.tcenv c1 in
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
                            let uu___12 =
                              FStarC_Errors_Msg.text
                                "Subcomp failed: Unequal computation types" in
                            let uu___13 =
                              let uu___14 =
                                FStarC_Class_PP.pp FStarC_Ident.pretty_lident
                                  ct0.FStarC_Syntax_Syntax.effect_name in
                              let uu___15 =
                                let uu___16 =
                                  FStarC_Class_PP.pp
                                    FStarC_Ident.pretty_lident
                                    ct1.FStarC_Syntax_Syntax.effect_name in
                                FStar_Pprint.op_Hat_Slash_Hat
                                  (FStar_Pprint.doc_of_string "and") uu___16 in
                              FStar_Pprint.op_Hat_Slash_Hat uu___14 uu___15 in
                            FStar_Pprint.op_Hat_Slash_Hat uu___12 uu___13 in
                          [uu___11] in
                        fail uu___10))))
  | (FStar_Pervasives_Native.Some (E_Total, t0), FStar_Pervasives_Native.Some
     (uu___1, t1)) -> check_relation g rel t0 t1
  | (FStar_Pervasives_Native.Some (E_Ghost, t0), FStar_Pervasives_Native.Some
     (E_Ghost, t1)) -> check_relation g rel t0 t1
  | (FStar_Pervasives_Native.Some (E_Ghost, t0), FStar_Pervasives_Native.Some
     (E_Total, t1)) ->
      let uu___1 = non_informative g t1 in
      if uu___1
      then check_relation g rel t0 t1
      else fail_str "Expected a Total computation, but got Ghost"
and check_subtype (g : env)
  (e : FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option)
  (t0 : FStarC_Syntax_Syntax.typ) (t1 : FStarC_Syntax_Syntax.typ) :
  unit result=
  fun ctx cache ->
    FStarC_Profiling.profile
      (fun uu___ ->
         let rel = SUBTYPING e in
         let uu___1 ctx1 cache1 =
           let ctx2 =
             {
               no_guard = (ctx1.no_guard);
               unfolding_ok = (ctx1.unfolding_ok);
               error_context =
                 (((if ctx.no_guard
                    then "check_subtype(no_guard)"
                    else "check_subtype"),
                    (FStar_Pervasives_Native.Some (CtxRel (t0, rel, t1)))) ::
                 (ctx1.error_context))
             } in
           let uu___2 = check_relation g rel t0 t1 in uu___2 ctx2 cache1 in
         uu___1 ctx cache) FStar_Pervasives_Native.None
      "FStarC.TypeChecker.Core.check_subtype"
and memo_check (g : env) (e : FStarC_Syntax_Syntax.term) :
  (tot_or_ghost * FStarC_Syntax_Syntax.typ) result=
  let check_then_memo g1 e1 =
    let uu___ = do_check_and_promote g1 e1 in
    fun ctx cache ->
      let uu___1 = uu___ ctx cache in
      match uu___1 with
      | Success (r, cache') ->
          let uu___2 =
            match FStar_Pervasives.Inl r with
            | FStar_Pervasives.Inl (res, guard1) ->
                let uu___3 = insert g1 e1 (res, guard1) in
                (fun ctx0 cache0 ->
                   let uu___4 = uu___3 ctx0 cache0 in
                   match uu___4 with
                   | Success ((x, g11), cache1) ->
                       let uu___5 =
                         let uu___6 uu___7 cache2 =
                           Success ((res, guard1), cache2) in
                         uu___6 ctx0 cache1 in
                       (match uu___5 with
                        | Success ((y, g2), cache2) ->
                            let uu___6 =
                              let uu___7 =
                                let uu___8 = and_pre g11 g2 in (y, uu___8) in
                              (uu___7, cache2) in
                            Success uu___6
                        | err -> err)
                   | Error err -> Error err)
            | FStar_Pervasives.Inr err -> fail_propagate err in
          uu___2 ctx cache'
      | Error err -> let uu___2 = fail_propagate err in uu___2 ctx cache in
  if Prims.op_Negation g.should_read_cache
  then check_then_memo g e
  else
    (let uu___1 = lookup g e in
     fun ctx cache ->
       let uu___2 = uu___1 ctx cache in
       match uu___2 with
       | Success (r, cache') ->
           let uu___3 =
             match FStar_Pervasives.Inl r with
             | FStar_Pervasives.Inr uu___4 -> check_then_memo g e
             | FStar_Pervasives.Inl (et, FStar_Pervasives_Native.None) ->
                 (fun uu___4 cache1 ->
                    Success ((et, FStar_Pervasives_Native.None), cache1))
             | FStar_Pervasives.Inl (et, pre) -> failwith "Impossible" in
           uu___3 ctx cache'
       | Error err -> let uu___3 = check_then_memo g e in uu___3 ctx cache)
and check' (msg : Prims.string) (g : env) (e : FStarC_Syntax_Syntax.term) :
  (tot_or_ghost * FStarC_Syntax_Syntax.typ) result=
  fun ctx cache ->
    let ctx1 =
      {
        no_guard = (ctx.no_guard);
        unfolding_ok = (ctx.unfolding_ok);
        error_context = ((msg, (FStar_Pervasives_Native.Some (CtxTerm e))) ::
          (ctx.error_context))
      } in
    let uu___ = memo_check g e in uu___ ctx1 cache
and check (msg : Prims.string) (g : env) (e : FStarC_Syntax_Syntax.term) :
  (tot_or_ghost * FStarC_Syntax_Syntax.typ) result=
  let uu___ = FStarC_Effect.op_Bang dbg in
  if uu___
  then
    fun ctx cache ->
      ((let uu___2 =
          FStarC_Class_Show.show FStarC_Syntax_Print.showable_term e in
        FStarC_Format.print1 "{About to check %s\n" uu___2);
       (let res = let uu___2 = check' msg g e in uu___2 ctx cache in
        match res with
        | Error err -> Error err
        | Success (((eff, typ), guard1), cache1) ->
            ((let uu___3 =
                FStarC_Class_Show.show FStarC_Syntax_Print.showable_term e in
              let uu___4 =
                FStarC_Class_Show.show FStarC_Syntax_Print.showable_term typ in
              let uu___5 =
                FStarC_Class_Show.show
                  (FStarC_Class_Show.show_option
                     FStarC_Syntax_Print.showable_term) guard1 in
              FStarC_Format.print3 "Checked %s at type %s with guard %s}\n"
                uu___3 uu___4 uu___5);
             res)))
  else check' msg g e
and do_check_and_promote (g : env) (e : FStarC_Syntax_Syntax.term) :
  (tot_or_ghost * FStarC_Syntax_Syntax.typ) result=
  let uu___ = do_check g e in
  fun ctx0 cache0 ->
    let uu___1 = uu___ ctx0 cache0 in
    match uu___1 with
    | Success ((x, g1), cache1) ->
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
                (fun uu___4 cache ->
                   Success (((eff1, t), FStar_Pervasives_Native.None), cache)) in
          uu___3 ctx0 cache1 in
        (match uu___2 with
         | Success ((y, g2), cache2) ->
             let uu___3 =
               let uu___4 = let uu___5 = and_pre g1 g2 in (y, uu___5) in
               (uu___4, cache2) in
             Success uu___3
         | err -> err)
    | Error err -> Error err
and do_check (g : env) (e : FStarC_Syntax_Syntax.term) :
  (tot_or_ghost * FStarC_Syntax_Syntax.typ) result=
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
      (fun uu___ cache ->
         Success
           (((E_Total, (i.FStarC_Syntax_Syntax.ltyp)),
              FStar_Pervasives_Native.None), cache))
  | FStarC_Syntax_Syntax.Tm_meta
      { FStarC_Syntax_Syntax.tm2 = t; FStarC_Syntax_Syntax.meta = uu___;_} ->
      memo_check g t
  | FStarC_Syntax_Syntax.Tm_uvar (uv, s) ->
      let uu___ =
        let uu___1 =
          let uu___2 = FStarC_Syntax_Util.ctx_uvar_typ uv in
          FStarC_Syntax_Subst.subst' s uu___2 in
        (E_Total, uu___1) in
      (fun uu___1 cache ->
         Success ((uu___, FStar_Pervasives_Native.None), cache))
  | FStarC_Syntax_Syntax.Tm_name x ->
      let uu___ = FStarC_TypeChecker_Env.try_lookup_bv g.tcenv x in
      (match uu___ with
       | FStar_Pervasives_Native.None ->
           let uu___1 =
             let uu___2 =
               FStarC_Class_Show.show FStarC_Syntax_Print.showable_bv x in
             FStarC_Format.fmt1 "Variable not found: %s" uu___2 in
           fail_str uu___1
       | FStar_Pervasives_Native.Some (t, uu___1) ->
           (fun uu___2 cache ->
              Success (((E_Total, t), FStar_Pervasives_Native.None), cache)))
  | FStarC_Syntax_Syntax.Tm_fvar f ->
      let uu___ =
        FStarC_TypeChecker_Env.try_lookup_lid g.tcenv
          f.FStarC_Syntax_Syntax.fv_name in
      (match uu___ with
       | FStar_Pervasives_Native.Some (([], t), uu___1) ->
           (fun uu___2 cache ->
              Success (((E_Total, t), FStar_Pervasives_Native.None), cache))
       | uu___1 -> fail_str "Missing universes instantiation")
  | FStarC_Syntax_Syntax.Tm_uinst
      ({ FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_fvar f;
         FStarC_Syntax_Syntax.pos = uu___;
         FStarC_Syntax_Syntax.vars = uu___1;
         FStarC_Syntax_Syntax.hash_code = uu___2;_},
       us)
      ->
      let uu___3 =
        FStarC_TypeChecker_Env.try_lookup_and_inst_lid g.tcenv us
          f.FStarC_Syntax_Syntax.fv_name in
      (match uu___3 with
       | FStar_Pervasives_Native.None ->
           let uu___4 =
             let uu___5 =
               FStarC_Ident.string_of_lid f.FStarC_Syntax_Syntax.fv_name in
             FStarC_Format.fmt1 "Top-level name not found: %s" uu___5 in
           fail_str uu___4
       | FStar_Pervasives_Native.Some (t, uu___4) ->
           (fun uu___5 cache ->
              Success (((E_Total, t), FStar_Pervasives_Native.None), cache)))
  | FStarC_Syntax_Syntax.Tm_constant c ->
      (match c with
       | FStarC_Const.Const_range_of -> fail_str "Unhandled constant"
       | FStarC_Const.Const_set_range_of -> fail_str "Unhandled constant"
       | FStarC_Const.Const_reify uu___ -> fail_str "Unhandled constant"
       | FStarC_Const.Const_reflect uu___ -> fail_str "Unhandled constant"
       | uu___ ->
           let t =
             FStarC_TypeChecker_TcTerm.tc_constant g.tcenv
               e1.FStarC_Syntax_Syntax.pos c in
           (fun uu___1 cache ->
              Success (((E_Total, t), FStar_Pervasives_Native.None), cache)))
  | FStarC_Syntax_Syntax.Tm_type u ->
      let uu___ =
        let uu___1 = mk_type (FStarC_Syntax_Syntax.U_succ u) in
        (E_Total, uu___1) in
      (fun uu___1 cache ->
         Success ((uu___, FStar_Pervasives_Native.None), cache))
  | FStarC_Syntax_Syntax.Tm_refine
      { FStarC_Syntax_Syntax.b = x; FStarC_Syntax_Syntax.phi = phi;_} ->
      let uu___ = check "refinement head" g x.FStarC_Syntax_Syntax.sort in
      (fun ctx0 cache0 ->
         let uu___1 = uu___ ctx0 cache0 in
         match uu___1 with
         | Success ((x1, g1), cache1) ->
             let uu___2 =
               let uu___3 =
                 match x1 with
                 | (uu___4, t) ->
                     let uu___5 = is_type g t in
                     (fun ctx01 cache01 ->
                        let uu___6 = uu___5 ctx01 cache01 in
                        match uu___6 with
                        | Success ((x2, g11), cache11) ->
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
                                        check "refinement formula" g' phi1 in
                                      fun ctx02 cache02 ->
                                        let uu___12 = uu___11 ctx02 cache02 in
                                        match uu___12 with
                                        | Success ((x4, g12), cache12) ->
                                            let uu___13 =
                                              let uu___14 =
                                                match x4 with
                                                | (uu___15, t') ->
                                                    let uu___16 =
                                                      is_type g' t' in
                                                    (fun ctx03 cache03 ->
                                                       let uu___17 =
                                                         uu___16 ctx03
                                                           cache03 in
                                                       match uu___17 with
                                                       | Success
                                                           ((x5, g13),
                                                            cache13)
                                                           ->
                                                           let uu___18 =
                                                             let uu___19
                                                               uu___20 cache
                                                               =
                                                               Success
                                                                 (((E_Total,
                                                                    t),
                                                                    FStar_Pervasives_Native.None),
                                                                   cache) in
                                                             uu___19 ctx03
                                                               cache13 in
                                                           (match uu___18
                                                            with
                                                            | Success
                                                                ((y, g2),
                                                                 cache2)
                                                                ->
                                                                let uu___19 =
                                                                  let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    and_pre
                                                                    g13 g2 in
                                                                    (y,
                                                                    uu___21) in
                                                                  (uu___20,
                                                                    cache2) in
                                                                Success
                                                                  uu___19
                                                            | err -> err)
                                                       | Error err ->
                                                           Error err) in
                                              uu___14 ctx02 cache12 in
                                            (match uu___13 with
                                             | Success ((y, g2), cache2) ->
                                                 let uu___14 =
                                                   let uu___15 =
                                                     let uu___16 =
                                                       and_pre g12 g2 in
                                                     (y, uu___16) in
                                                   (uu___15, cache2) in
                                                 Success uu___14
                                             | err -> err)
                                        | Error err -> Error err in
                                    with_binders g [x3] [x2] uu___10 in
                              uu___8 ctx01 cache11 in
                            (match uu___7 with
                             | Success ((y, g2), cache2) ->
                                 let uu___8 =
                                   let uu___9 =
                                     let uu___10 = and_pre g11 g2 in
                                     (y, uu___10) in
                                   (uu___9, cache2) in
                                 Success uu___8
                             | err -> err)
                        | Error err -> Error err) in
               uu___3 ctx0 cache1 in
             (match uu___2 with
              | Success ((y, g2), cache2) ->
                  let uu___3 =
                    let uu___4 = let uu___5 = and_pre g1 g2 in (y, uu___5) in
                    (uu___4, cache2) in
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
           let uu___2 ctx cache =
             let ctx1 =
               {
                 no_guard = (ctx.no_guard);
                 unfolding_ok = (ctx.unfolding_ok);
                 error_context =
                   (("abs binders", FStar_Pervasives_Native.None) ::
                   (ctx.error_context))
               } in
             let uu___3 = check_binders g xs1 in uu___3 ctx1 cache in
           (fun ctx0 cache0 ->
              let uu___3 = uu___2 ctx0 cache0 in
              match uu___3 with
              | Success ((x, g1), cache1) ->
                  let uu___4 =
                    let uu___5 =
                      let uu___6 =
                        let uu___7 = check "abs body" g' body1 in
                        fun ctx01 cache01 ->
                          let uu___8 = uu___7 ctx01 cache01 in
                          match uu___8 with
                          | Success ((x1, g11), cache11) ->
                              let uu___9 =
                                let uu___10 =
                                  let uu___11 =
                                    let uu___12 =
                                      let uu___13 = as_comp g x1 in
                                      FStarC_Syntax_Util.arrow xs1 uu___13 in
                                    (E_Total, uu___12) in
                                  fun uu___12 cache ->
                                    Success
                                      ((uu___11,
                                         FStar_Pervasives_Native.None),
                                        cache) in
                                uu___10 ctx01 cache11 in
                              (match uu___9 with
                               | Success ((y, g2), cache2) ->
                                   let uu___10 =
                                     let uu___11 =
                                       let uu___12 = and_pre g11 g2 in
                                       (y, uu___12) in
                                     (uu___11, cache2) in
                                   Success uu___10
                               | err -> err)
                          | Error err -> Error err in
                      with_binders g xs1 x uu___6 in
                    uu___5 ctx0 cache1 in
                  (match uu___4 with
                   | Success ((y, g2), cache2) ->
                       let uu___5 =
                         let uu___6 =
                           let uu___7 = and_pre g1 g2 in (y, uu___7) in
                         (uu___6, cache2) in
                       Success uu___5
                   | err -> err)
              | Error err -> Error err))
  | FStarC_Syntax_Syntax.Tm_arrow
      { FStarC_Syntax_Syntax.bs1 = xs; FStarC_Syntax_Syntax.comp = c;_} ->
      let uu___ = open_comp_binders g xs c in
      (match uu___ with
       | (g', xs1, c1) ->
           let uu___1 ctx cache =
             let ctx1 =
               {
                 no_guard = (ctx.no_guard);
                 unfolding_ok = (ctx.unfolding_ok);
                 error_context =
                   (("arrow binders", FStar_Pervasives_Native.None) ::
                   (ctx.error_context))
               } in
             let uu___2 = check_binders g xs1 in uu___2 ctx1 cache in
           (fun ctx0 cache0 ->
              let uu___2 = uu___1 ctx0 cache0 in
              match uu___2 with
              | Success ((x, g1), cache1) ->
                  let uu___3 =
                    let uu___4 =
                      let uu___5 =
                        let uu___6 ctx cache =
                          let ctx1 =
                            {
                              no_guard = (ctx.no_guard);
                              unfolding_ok = (ctx.unfolding_ok);
                              error_context =
                                (("arrow comp", FStar_Pervasives_Native.None)
                                :: (ctx.error_context))
                            } in
                          let uu___7 = check_comp g' c1 in uu___7 ctx1 cache in
                        fun ctx01 cache01 ->
                          let uu___7 = uu___6 ctx01 cache01 in
                          match uu___7 with
                          | Success ((x1, g11), cache11) ->
                              let uu___8 =
                                let uu___9 =
                                  let uu___10 =
                                    let uu___11 =
                                      mk_type
                                        (FStarC_Syntax_Syntax.U_max (x1 :: x)) in
                                    (E_Total, uu___11) in
                                  fun uu___11 cache ->
                                    Success
                                      ((uu___10,
                                         FStar_Pervasives_Native.None),
                                        cache) in
                                uu___9 ctx01 cache11 in
                              (match uu___8 with
                               | Success ((y, g2), cache2) ->
                                   let uu___9 =
                                     let uu___10 =
                                       let uu___11 = and_pre g11 g2 in
                                       (y, uu___11) in
                                     (uu___10, cache2) in
                                   Success uu___9
                               | err -> err)
                          | Error err -> Error err in
                      with_binders g xs1 x uu___5 in
                    uu___4 ctx0 cache1 in
                  (match uu___3 with
                   | Success ((y, g2), cache2) ->
                       let uu___4 =
                         let uu___5 =
                           let uu___6 = and_pre g1 g2 in (y, uu___6) in
                         (uu___5, cache2) in
                       Success uu___4
                   | err -> err)
              | Error err -> Error err))
  | FStarC_Syntax_Syntax.Tm_app uu___ ->
      let rec check_app_arg uu___1 uu___2 =
        match (uu___1, uu___2) with
        | ((eff_hd, t_hd), (arg, arg_qual)) ->
            let uu___3 = is_arrow g t_hd in
            (fun ctx0 cache0 ->
               let uu___4 = uu___3 ctx0 cache0 in
               match uu___4 with
               | Success ((x, g1), cache1) ->
                   let uu___5 =
                     let uu___6 =
                       match x with
                       | (x1, eff_arr, t') ->
                           let uu___7 = check "app arg" g arg in
                           (fun ctx01 cache01 ->
                              let uu___8 = uu___7 ctx01 cache01 in
                              match uu___8 with
                              | Success ((x2, g11), cache11) ->
                                  let uu___9 =
                                    let uu___10 =
                                      match x2 with
                                      | (eff_arg, t_arg) ->
                                          let uu___11 ctx cache =
                                            let ctx1 =
                                              {
                                                no_guard = (ctx.no_guard);
                                                unfolding_ok =
                                                  (ctx.unfolding_ok);
                                                error_context =
                                                  (("app subtyping",
                                                     (FStar_Pervasives_Native.Some
                                                        (CtxTerm arg))) ::
                                                  (ctx.error_context))
                                              } in
                                            let uu___12 =
                                              check_subtype g
                                                (FStar_Pervasives_Native.Some
                                                   arg) t_arg
                                                (x1.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                                            uu___12 ctx1 cache in
                                          (fun ctx02 cache02 ->
                                             let uu___12 =
                                               uu___11 ctx02 cache02 in
                                             match uu___12 with
                                             | Success ((x3, g12), cache12)
                                                 ->
                                                 let uu___13 =
                                                   let uu___14 =
                                                     let uu___15 ctx cache =
                                                       let ctx1 =
                                                         {
                                                           no_guard =
                                                             (ctx.no_guard);
                                                           unfolding_ok =
                                                             (ctx.unfolding_ok);
                                                           error_context =
                                                             (("app arg qual",
                                                                FStar_Pervasives_Native.None)
                                                             ::
                                                             (ctx.error_context))
                                                         } in
                                                       let uu___16 =
                                                         check_arg_qual
                                                           arg_qual
                                                           x1.FStarC_Syntax_Syntax.binder_qual in
                                                       uu___16 ctx1 cache in
                                                     fun ctx03 cache03 ->
                                                       let uu___16 =
                                                         uu___15 ctx03
                                                           cache03 in
                                                       match uu___16 with
                                                       | Success
                                                           ((x4, g13),
                                                            cache13)
                                                           ->
                                                           let uu___17 =
                                                             let uu___18 =
                                                               let uu___19 =
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
                                                               fun uu___20
                                                                 cache ->
                                                                 Success
                                                                   ((uu___19,
                                                                    FStar_Pervasives_Native.None),
                                                                    cache) in
                                                             uu___18 ctx03
                                                               cache13 in
                                                           (match uu___17
                                                            with
                                                            | Success
                                                                ((y, g2),
                                                                 cache2)
                                                                ->
                                                                let uu___18 =
                                                                  let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    and_pre
                                                                    g13 g2 in
                                                                    (y,
                                                                    uu___20) in
                                                                  (uu___19,
                                                                    cache2) in
                                                                Success
                                                                  uu___18
                                                            | err -> err)
                                                       | Error err ->
                                                           Error err in
                                                   uu___14 ctx02 cache12 in
                                                 (match uu___13 with
                                                  | Success ((y, g2), cache2)
                                                      ->
                                                      let uu___14 =
                                                        let uu___15 =
                                                          let uu___16 =
                                                            and_pre g12 g2 in
                                                          (y, uu___16) in
                                                        (uu___15, cache2) in
                                                      Success uu___14
                                                  | err -> err)
                                             | Error err -> Error err) in
                                    uu___10 ctx01 cache11 in
                                  (match uu___9 with
                                   | Success ((y, g2), cache2) ->
                                       let uu___10 =
                                         let uu___11 =
                                           let uu___12 = and_pre g11 g2 in
                                           (y, uu___12) in
                                         (uu___11, cache2) in
                                       Success uu___10
                                   | err -> err)
                              | Error err -> Error err) in
                     uu___6 ctx0 cache1 in
                   (match uu___5 with
                    | Success ((y, g2), cache2) ->
                        let uu___6 =
                          let uu___7 =
                            let uu___8 = and_pre g1 g2 in (y, uu___8) in
                          (uu___7, cache2) in
                        Success uu___6
                    | err -> err)
               | Error err -> Error err) in
      let check_app hd args =
        let uu___1 = check "app head" g hd in
        fun ctx0 cache0 ->
          let uu___2 = uu___1 ctx0 cache0 in
          match uu___2 with
          | Success ((x, g1), cache1) ->
              let uu___3 =
                let uu___4 =
                  match x with
                  | (eff_hd, t) -> fold check_app_arg (eff_hd, t) args in
                uu___4 ctx0 cache1 in
              (match uu___3 with
               | Success ((y, g2), cache2) ->
                   let uu___4 =
                     let uu___5 = let uu___6 = and_pre g1 g2 in (y, uu___6) in
                     (uu___5, cache2) in
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
                (fun ctx0 cache0 ->
                   let uu___3 = uu___2 ctx0 cache0 in
                   match uu___3 with
                   | Success ((x, g1), cache1) ->
                       let uu___4 =
                         let uu___5 =
                           match x with
                           | (eff_hd, t_hd) ->
                               let uu___6 = is_arrow g t_hd in
                               (fun ctx01 cache01 ->
                                  let uu___7 = uu___6 ctx01 cache01 in
                                  match uu___7 with
                                  | Success ((x1, g11), cache11) ->
                                      let uu___8 =
                                        let uu___9 =
                                          match x1 with
                                          | (x2, eff_arr1, s1) ->
                                              let uu___10 =
                                                check "app arg" g t1 in
                                              (fun ctx02 cache02 ->
                                                 let uu___11 =
                                                   uu___10 ctx02 cache02 in
                                                 match uu___11 with
                                                 | Success
                                                     ((x3, g12), cache12) ->
                                                     let uu___12 =
                                                       let uu___13 =
                                                         match x3 with
                                                         | (eff_arg1, t_t1)
                                                             ->
                                                             let uu___14 ctx
                                                               cache =
                                                               let ctx1 =
                                                                 {
                                                                   no_guard =
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
                                                               let uu___15 =
                                                                 check_subtype
                                                                   g
                                                                   (FStar_Pervasives_Native.Some
                                                                    t1) t_t1
                                                                   (x2.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                                                               uu___15 ctx1
                                                                 cache in
                                                             (fun ctx03
                                                                cache03 ->
                                                                let uu___15 =
                                                                  uu___14
                                                                    ctx03
                                                                    cache03 in
                                                                match uu___15
                                                                with
                                                                | Success
                                                                    ((x4,
                                                                    g13),
                                                                    cache13)
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
                                                                    cache04
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    uu___18
                                                                    ctx04
                                                                    cache04 in
                                                                    match uu___19
                                                                    with
                                                                    | 
                                                                    Success
                                                                    ((x5,
                                                                    g14),
                                                                    cache14)
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
                                                                    g
                                                                    guard_formula
                                                                    uu___23 in
                                                                    (fun
                                                                    ctx05
                                                                    cache05
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    uu___22
                                                                    ctx05
                                                                    cache05 in
                                                                    match uu___23
                                                                    with
                                                                    | 
                                                                    Success
                                                                    ((x6,
                                                                    g15),
                                                                    cache15)
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
                                                                    ctx cache
                                                                    =
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
                                                                    ctx1
                                                                    cache in
                                                                    (fun
                                                                    ctx06
                                                                    cache06
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    uu___26
                                                                    ctx06
                                                                    cache06 in
                                                                    match uu___27
                                                                    with
                                                                    | 
                                                                    Success
                                                                    ((x7,
                                                                    g16),
                                                                    cache16)
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
                                                                    cache ->
                                                                    Success
                                                                    ((uu___30,
                                                                    FStar_Pervasives_Native.None),
                                                                    cache) in
                                                                    uu___29
                                                                    ctx06
                                                                    cache16 in
                                                                    (match uu___28
                                                                    with
                                                                    | 
                                                                    Success
                                                                    ((y1, g2),
                                                                    cache2)
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    let uu___30
                                                                    =
                                                                    let uu___31
                                                                    =
                                                                    and_pre
                                                                    g16 g2 in
                                                                    (y1,
                                                                    uu___31) in
                                                                    (uu___30,
                                                                    cache2) in
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
                                                                    ctx05
                                                                    cache15 in
                                                                    (match uu___24
                                                                    with
                                                                    | 
                                                                    Success
                                                                    ((y1, g2),
                                                                    cache2)
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    and_pre
                                                                    g15 g2 in
                                                                    (y1,
                                                                    uu___27) in
                                                                    (uu___26,
                                                                    cache2) in
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
                                                                    ctx04
                                                                    cache14 in
                                                                    (match uu___20
                                                                    with
                                                                    | 
                                                                    Success
                                                                    ((y, g2),
                                                                    cache2)
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    and_pre
                                                                    g14 g2 in
                                                                    (y,
                                                                    uu___23) in
                                                                    (uu___22,
                                                                    cache2) in
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
                                                                    ctx03
                                                                    cache13 in
                                                                    (match uu___16
                                                                    with
                                                                    | 
                                                                    Success
                                                                    ((y, g2),
                                                                    cache2)
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    and_pre
                                                                    g13 g2 in
                                                                    (y,
                                                                    uu___19) in
                                                                    (uu___18,
                                                                    cache2) in
                                                                    Success
                                                                    uu___17
                                                                    | 
                                                                    err ->
                                                                    err)
                                                                | Error err
                                                                    ->
                                                                    Error err) in
                                                       uu___13 ctx02 cache12 in
                                                     (match uu___12 with
                                                      | Success
                                                          ((y, g2), cache2)
                                                          ->
                                                          let uu___13 =
                                                            let uu___14 =
                                                              let uu___15 =
                                                                and_pre g12
                                                                  g2 in
                                                              (y, uu___15) in
                                                            (uu___14, cache2) in
                                                          Success uu___13
                                                      | err -> err)
                                                 | Error err -> Error err) in
                                        uu___9 ctx01 cache11 in
                                      (match uu___8 with
                                       | Success ((y, g2), cache2) ->
                                           let uu___9 =
                                             let uu___10 =
                                               let uu___11 = and_pre g11 g2 in
                                               (y, uu___11) in
                                             (uu___10, cache2) in
                                           Success uu___9
                                       | err -> err)
                                  | Error err -> Error err) in
                         uu___5 ctx0 cache1 in
                       (match uu___4 with
                        | Success ((y, g2), cache2) ->
                            let uu___5 =
                              let uu___6 =
                                let uu___7 = and_pre g1 g2 in (y, uu___7) in
                              (uu___6, cache2) in
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
      (fun ctx0 cache0 ->
         let uu___3 = uu___2 ctx0 cache0 in
         match uu___3 with
         | Success ((x, g1), cache1) ->
             let uu___4 =
               let uu___5 =
                 match x with
                 | (eff, te) ->
                     let uu___6 = check "ascription type" g t in
                     (fun ctx01 cache01 ->
                        let uu___7 = uu___6 ctx01 cache01 in
                        match uu___7 with
                        | Success ((x1, g11), cache11) ->
                            let uu___8 =
                              let uu___9 =
                                match x1 with
                                | (uu___10, t') ->
                                    let uu___11 = is_type g t' in
                                    (fun ctx02 cache02 ->
                                       let uu___12 = uu___11 ctx02 cache02 in
                                       match uu___12 with
                                       | Success ((x2, g12), cache12) ->
                                           let uu___13 =
                                             let uu___14 =
                                               let uu___15 ctx cache =
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
                                                 uu___16 ctx1 cache in
                                               fun ctx03 cache03 ->
                                                 let uu___16 =
                                                   uu___15 ctx03 cache03 in
                                                 match uu___16 with
                                                 | Success
                                                     ((x3, g13), cache13) ->
                                                     let uu___17 =
                                                       let uu___18 uu___19
                                                         cache =
                                                         Success
                                                           (((eff, t),
                                                              FStar_Pervasives_Native.None),
                                                             cache) in
                                                       uu___18 ctx03 cache13 in
                                                     (match uu___17 with
                                                      | Success
                                                          ((y, g2), cache2)
                                                          ->
                                                          let uu___18 =
                                                            let uu___19 =
                                                              let uu___20 =
                                                                and_pre g13
                                                                  g2 in
                                                              (y, uu___20) in
                                                            (uu___19, cache2) in
                                                          Success uu___18
                                                      | err -> err)
                                                 | Error err -> Error err in
                                             uu___14 ctx02 cache12 in
                                           (match uu___13 with
                                            | Success ((y, g2), cache2) ->
                                                let uu___14 =
                                                  let uu___15 =
                                                    let uu___16 =
                                                      and_pre g12 g2 in
                                                    (y, uu___16) in
                                                  (uu___15, cache2) in
                                                Success uu___14
                                            | err -> err)
                                       | Error err -> Error err) in
                              uu___9 ctx01 cache11 in
                            (match uu___8 with
                             | Success ((y, g2), cache2) ->
                                 let uu___9 =
                                   let uu___10 =
                                     let uu___11 = and_pre g11 g2 in
                                     (y, uu___11) in
                                   (uu___10, cache2) in
                                 Success uu___9
                             | err -> err)
                        | Error err -> Error err) in
               uu___5 ctx0 cache1 in
             (match uu___4 with
              | Success ((y, g2), cache2) ->
                  let uu___5 =
                    let uu___6 = let uu___7 = and_pre g1 g2 in (y, uu___7) in
                    (uu___6, cache2) in
                  Success uu___5
              | err -> err)
         | Error err -> Error err)
  | FStarC_Syntax_Syntax.Tm_ascribed
      { FStarC_Syntax_Syntax.tm = e2;
        FStarC_Syntax_Syntax.asc = (FStar_Pervasives.Inr c, uu___, uu___1);
        FStarC_Syntax_Syntax.eff_opt = uu___2;_}
      ->
      let uu___3 = FStarC_Syntax_Util.is_tot_or_gtot_comp c in
      if uu___3
      then
        let uu___4 = check "ascription head" g e2 in
        (fun ctx0 cache0 ->
           let uu___5 = uu___4 ctx0 cache0 in
           match uu___5 with
           | Success ((x, g1), cache1) ->
               let uu___6 =
                 let uu___7 =
                   match x with
                   | (eff, te) ->
                       let uu___8 ctx cache =
                         let ctx1 =
                           {
                             no_guard = (ctx.no_guard);
                             unfolding_ok = (ctx.unfolding_ok);
                             error_context =
                               (("ascription comp",
                                  FStar_Pervasives_Native.None) ::
                               (ctx.error_context))
                           } in
                         let uu___9 = check_comp g c in uu___9 ctx1 cache in
                       (fun ctx01 cache01 ->
                          let uu___9 = uu___8 ctx01 cache01 in
                          match uu___9 with
                          | Success ((x1, g11), cache11) ->
                              let uu___10 =
                                let uu___11 =
                                  let c_e = as_comp g (eff, te) in
                                  let uu___12 ctx cache =
                                    let ctx1 =
                                      {
                                        no_guard = (ctx.no_guard);
                                        unfolding_ok = (ctx.unfolding_ok);
                                        error_context =
                                          (("ascription subtyping (comp)",
                                             FStar_Pervasives_Native.None) ::
                                          (ctx.error_context))
                                      } in
                                    let uu___13 =
                                      check_relation_comp g
                                        (SUBTYPING
                                           (FStar_Pervasives_Native.Some e2))
                                        c_e c in
                                    uu___13 ctx1 cache in
                                  fun ctx02 cache02 ->
                                    let uu___13 = uu___12 ctx02 cache02 in
                                    match uu___13 with
                                    | Success ((x2, g12), cache12) ->
                                        let uu___14 =
                                          let uu___15 =
                                            let uu___16 =
                                              comp_as_tot_or_ghost_and_type c in
                                            match uu___16 with
                                            | FStar_Pervasives_Native.Some
                                                (eff1, t) ->
                                                (fun uu___17 cache ->
                                                   Success
                                                     (((eff1, t),
                                                        FStar_Pervasives_Native.None),
                                                       cache)) in
                                          uu___15 ctx02 cache12 in
                                        (match uu___14 with
                                         | Success ((y, g2), cache2) ->
                                             let uu___15 =
                                               let uu___16 =
                                                 let uu___17 = and_pre g12 g2 in
                                                 (y, uu___17) in
                                               (uu___16, cache2) in
                                             Success uu___15
                                         | err -> err)
                                    | Error err -> Error err in
                                uu___11 ctx01 cache11 in
                              (match uu___10 with
                               | Success ((y, g2), cache2) ->
                                   let uu___11 =
                                     let uu___12 =
                                       let uu___13 = and_pre g11 g2 in
                                       (y, uu___13) in
                                     (uu___12, cache2) in
                                   Success uu___11
                               | err -> err)
                          | Error err -> Error err) in
                 uu___7 ctx0 cache1 in
               (match uu___6 with
                | Success ((y, g2), cache2) ->
                    let uu___7 =
                      let uu___8 = let uu___9 = and_pre g1 g2 in (y, uu___9) in
                      (uu___8, cache2) in
                    Success uu___7
                | err -> err)
           | Error err -> Error err)
      else
        (let uu___5 =
           let uu___6 =
             FStarC_Class_Show.show FStarC_Syntax_Print.showable_comp c in
           FStarC_Format.fmt1
             "Effect ascriptions are not fully handled yet: %s" uu___6 in
         fail_str uu___5)
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
                    check "let definition" g lb.FStarC_Syntax_Syntax.lbdef in
                  (fun ctx0 cache0 ->
                     let uu___4 = uu___3 ctx0 cache0 in
                     match uu___4 with
                     | Success ((x2, g1), cache1) ->
                         let uu___5 =
                           let uu___6 =
                             match x2 with
                             | (eff_def, tdef) ->
                                 let uu___7 =
                                   check "let type" g
                                     lb.FStarC_Syntax_Syntax.lbtyp in
                                 (fun ctx01 cache01 ->
                                    let uu___8 = uu___7 ctx01 cache01 in
                                    match uu___8 with
                                    | Success ((x3, g11), cache11) ->
                                        let uu___9 =
                                          let uu___10 =
                                            match x3 with
                                            | (uu___11, ttyp) ->
                                                let uu___12 = is_type g ttyp in
                                                (fun ctx02 cache02 ->
                                                   let uu___13 =
                                                     uu___12 ctx02 cache02 in
                                                   match uu___13 with
                                                   | Success
                                                       ((x4, g12), cache12)
                                                       ->
                                                       let uu___14 =
                                                         let uu___15 =
                                                           let uu___16 ctx
                                                             cache =
                                                             let ctx1 =
                                                               {
                                                                 no_guard =
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
                                                             let uu___17 =
                                                               check_subtype
                                                                 g
                                                                 (FStar_Pervasives_Native.Some
                                                                    (
                                                                    lb.FStarC_Syntax_Syntax.lbdef))
                                                                 tdef
                                                                 lb.FStarC_Syntax_Syntax.lbtyp in
                                                             uu___17 ctx1
                                                               cache in
                                                           fun ctx03 cache03
                                                             ->
                                                             let uu___17 =
                                                               uu___16 ctx03
                                                                 cache03 in
                                                             match uu___17
                                                             with
                                                             | Success
                                                                 ((x5, g13),
                                                                  cache13)
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
                                                                    cache04
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    uu___21
                                                                    ctx04
                                                                    cache04 in
                                                                    match uu___22
                                                                    with
                                                                    | 
                                                                    Success
                                                                    ((x6,
                                                                    g14),
                                                                    cache14)
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
                                                                    ctx05
                                                                    cache05
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    uu___25
                                                                    ctx05
                                                                    cache05 in
                                                                    match uu___26
                                                                    with
                                                                    | 
                                                                    Success
                                                                    ((x7,
                                                                    g15),
                                                                    cache15)
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    let uu___28
                                                                    uu___29
                                                                    cache =
                                                                    Success
                                                                    ((((join_eff
                                                                    eff_def
                                                                    eff_body),
                                                                    t),
                                                                    FStar_Pervasives_Native.None),
                                                                    cache) in
                                                                    uu___28
                                                                    ctx05
                                                                    cache15 in
                                                                    (match uu___27
                                                                    with
                                                                    | 
                                                                    Success
                                                                    ((y, g2),
                                                                    cache2)
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    let uu___29
                                                                    =
                                                                    let uu___30
                                                                    =
                                                                    and_pre
                                                                    g15 g2 in
                                                                    (y,
                                                                    uu___30) in
                                                                    (uu___29,
                                                                    cache2) in
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
                                                                    ctx04
                                                                    cache14 in
                                                                    (match uu___23
                                                                    with
                                                                    | 
                                                                    Success
                                                                    ((y, g2),
                                                                    cache2)
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    and_pre
                                                                    g14 g2 in
                                                                    (y,
                                                                    uu___26) in
                                                                    (uu___25,
                                                                    cache2) in
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
                                                                    g x1 x4
                                                                    lb.FStarC_Syntax_Syntax.lbdef
                                                                    uu___20 in
                                                                   uu___19
                                                                    ctx03
                                                                    cache13 in
                                                                 (match uu___18
                                                                  with
                                                                  | Success
                                                                    ((y, g2),
                                                                    cache2)
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    and_pre
                                                                    g13 g2 in
                                                                    (y,
                                                                    uu___21) in
                                                                    (uu___20,
                                                                    cache2) in
                                                                    Success
                                                                    uu___19
                                                                  | err ->
                                                                    err)
                                                             | Error err ->
                                                                 Error err in
                                                         uu___15 ctx02
                                                           cache12 in
                                                       (match uu___14 with
                                                        | Success
                                                            ((y, g2), cache2)
                                                            ->
                                                            let uu___15 =
                                                              let uu___16 =
                                                                let uu___17 =
                                                                  and_pre g12
                                                                    g2 in
                                                                (y, uu___17) in
                                                              (uu___16,
                                                                cache2) in
                                                            Success uu___15
                                                        | err -> err)
                                                   | Error err -> Error err) in
                                          uu___10 ctx01 cache11 in
                                        (match uu___9 with
                                         | Success ((y, g2), cache2) ->
                                             let uu___10 =
                                               let uu___11 =
                                                 let uu___12 = and_pre g11 g2 in
                                                 (y, uu___12) in
                                               (uu___11, cache2) in
                                             Success uu___10
                                         | err -> err)
                                    | Error err -> Error err) in
                           uu___6 ctx0 cache1 in
                         (match uu___5 with
                          | Success ((y, g2), cache2) ->
                              let uu___6 =
                                let uu___7 =
                                  let uu___8 = and_pre g1 g2 in (y, uu___8) in
                                (uu___7, cache2) in
                              Success uu___6
                          | err -> err)
                     | Error err -> Error err)
                else
                  (let uu___4 =
                     let uu___5 =
                       FStarC_Class_Show.show FStarC_Ident.showable_lident
                         lb.FStarC_Syntax_Syntax.lbeff in
                     FStarC_Format.fmt1
                       "Let binding is effectful (lbeff = %s)" uu___5 in
                   fail_str uu___4)))
  | FStarC_Syntax_Syntax.Tm_match
      { FStarC_Syntax_Syntax.scrutinee = sc;
        FStarC_Syntax_Syntax.ret_opt = FStar_Pervasives_Native.None;
        FStarC_Syntax_Syntax.brs = branches;
        FStarC_Syntax_Syntax.rc_opt1 = rc_opt;_}
      ->
      let uu___ = check "scrutinee" g sc in
      (fun ctx0 cache0 ->
         let uu___1 = uu___ ctx0 cache0 in
         match uu___1 with
         | Success ((x, g1), cache1) ->
             let uu___2 =
               let uu___3 =
                 match x with
                 | (eff_sc, t_sc) ->
                     let uu___4 = universe_of_well_typed_term g t_sc in
                     (fun ctx01 cache01 ->
                        let uu___5 = uu___4 ctx01 cache01 in
                        match uu___5 with
                        | Success ((x1, g11), cache11) ->
                            let uu___6 =
                              let uu___7 =
                                let rec check_branches path_condition
                                  branch_typ_opt branches1 =
                                  match branches1 with
                                  | [] ->
                                      (match branch_typ_opt with
                                       | FStar_Pervasives_Native.None ->
                                           fail_str
                                             "could not compute a type for the match"
                                       | FStar_Pervasives_Native.Some et ->
                                           let uu___8 =
                                             boolean_negation_simp
                                               path_condition in
                                           (match uu___8 with
                                            | FStar_Pervasives_Native.None ->
                                                (fun uu___9 cache ->
                                                   Success
                                                     ((et,
                                                        FStar_Pervasives_Native.None),
                                                       cache))
                                            | FStar_Pervasives_Native.Some
                                                neg_path ->
                                                let uu___9 =
                                                  let uu___10 =
                                                    FStarC_Syntax_Util.b2t
                                                      neg_path in
                                                  guard g uu___10 in
                                                (fun ctx02 cache02 ->
                                                   let uu___10 =
                                                     uu___9 ctx02 cache02 in
                                                   match uu___10 with
                                                   | Success
                                                       ((x2, g12), cache12)
                                                       ->
                                                       let uu___11 =
                                                         let uu___12 uu___13
                                                           cache =
                                                           Success
                                                             ((et,
                                                                FStar_Pervasives_Native.None),
                                                               cache) in
                                                         uu___12 ctx02
                                                           cache12 in
                                                       (match uu___11 with
                                                        | Success
                                                            ((y, g2), cache2)
                                                            ->
                                                            let uu___12 =
                                                              let uu___13 =
                                                                let uu___14 =
                                                                  and_pre g12
                                                                    g2 in
                                                                (y, uu___14) in
                                                              (uu___13,
                                                                cache2) in
                                                            Success uu___12
                                                        | err -> err)
                                                   | Error err -> Error err)))
                                  | (p, FStar_Pervasives_Native.None, b)::rest
                                      ->
                                      let uu___8 =
                                        open_branch g
                                          (p, FStar_Pervasives_Native.None,
                                            b) in
                                      (match uu___8 with
                                       | (uu___9, (p1, uu___10, b1)) ->
                                           let uu___11 ctx cache =
                                             let ctx1 =
                                               {
                                                 no_guard = (ctx.no_guard);
                                                 unfolding_ok =
                                                   (ctx.unfolding_ok);
                                                 error_context =
                                                   (("check_pat",
                                                      FStar_Pervasives_Native.None)
                                                   :: (ctx.error_context))
                                               } in
                                             let uu___12 =
                                               check_pat g p1 t_sc in
                                             uu___12 ctx1 cache in
                                           (fun ctx02 cache02 ->
                                              let uu___12 =
                                                uu___11 ctx02 cache02 in
                                              match uu___12 with
                                              | Success ((x2, g12), cache12)
                                                  ->
                                                  let uu___13 =
                                                    let uu___14 =
                                                      match x2 with
                                                      | (bs, us) ->
                                                          let uu___15 =
                                                            pattern_branch_condition
                                                              g sc p1 in
                                                          (fun ctx03 cache03
                                                             ->
                                                             let uu___16 =
                                                               uu___15 ctx03
                                                                 cache03 in
                                                             match uu___16
                                                             with
                                                             | Success
                                                                 ((x3, g13),
                                                                  cache13)
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
                                                                    FStarC_Option.must
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
                                                                    let g'0 =
                                                                    push_binders
                                                                    g bs in
                                                                    let g' =
                                                                    push_hypothesis
                                                                    g'0
                                                                    this_path_condition in
                                                                    let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    ctx cache
                                                                    =
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
                                                                    g' b1 in
                                                                    uu___24
                                                                    ctx1
                                                                    cache in
                                                                    fun ctx04
                                                                    cache04
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    uu___23
                                                                    ctx04
                                                                    cache04 in
                                                                    match uu___24
                                                                    with
                                                                    | 
                                                                    Success
                                                                    ((x4,
                                                                    g14),
                                                                    cache14)
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
                                                                    ctx05
                                                                    cache05
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    uu___27
                                                                    ctx05
                                                                    cache05 in
                                                                    match uu___28
                                                                    with
                                                                    | 
                                                                    Success
                                                                    ((x5,
                                                                    g15),
                                                                    cache15)
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    let uu___30
                                                                    uu___31
                                                                    cache =
                                                                    Success
                                                                    (((eff_br,
                                                                    tbr),
                                                                    FStar_Pervasives_Native.None),
                                                                    cache) in
                                                                    uu___30
                                                                    ctx05
                                                                    cache15 in
                                                                    (match uu___29
                                                                    with
                                                                    | 
                                                                    Success
                                                                    ((y, g2),
                                                                    cache2)
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    let uu___31
                                                                    =
                                                                    let uu___32
                                                                    =
                                                                    and_pre
                                                                    g15 g2 in
                                                                    (y,
                                                                    uu___32) in
                                                                    (uu___31,
                                                                    cache2) in
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
                                                                    ctx cache
                                                                    =
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
                                                                    g'
                                                                    (FStar_Pervasives_Native.Some
                                                                    b1) tbr
                                                                    expect_tbr in
                                                                    uu___28
                                                                    ctx1
                                                                    cache in
                                                                    (fun
                                                                    ctx05
                                                                    cache05
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    uu___27
                                                                    ctx05
                                                                    cache05 in
                                                                    match uu___28
                                                                    with
                                                                    | 
                                                                    Success
                                                                    ((x5,
                                                                    g15),
                                                                    cache15)
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    let uu___30
                                                                    uu___31
                                                                    cache =
                                                                    Success
                                                                    ((((join_eff
                                                                    eff_br
                                                                    acc_eff),
                                                                    expect_tbr),
                                                                    FStar_Pervasives_Native.None),
                                                                    cache) in
                                                                    uu___30
                                                                    ctx05
                                                                    cache15 in
                                                                    (match uu___29
                                                                    with
                                                                    | 
                                                                    Success
                                                                    ((y, g2),
                                                                    cache2)
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    let uu___31
                                                                    =
                                                                    let uu___32
                                                                    =
                                                                    and_pre
                                                                    g15 g2 in
                                                                    (y,
                                                                    uu___32) in
                                                                    (uu___31,
                                                                    cache2) in
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
                                                                    ctx04
                                                                    cache14 in
                                                                    (match uu___25
                                                                    with
                                                                    | 
                                                                    Success
                                                                    ((y, g2),
                                                                    cache2)
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    and_pre
                                                                    g14 g2 in
                                                                    (y,
                                                                    uu___28) in
                                                                    (uu___27,
                                                                    cache2) in
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
                                                                    g'0
                                                                    this_path_condition
                                                                    uu___22 in
                                                                    with_binders
                                                                    g bs us
                                                                    uu___21 in
                                                                    (fun
                                                                    ctx04
                                                                    cache04
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    uu___20
                                                                    ctx04
                                                                    cache04 in
                                                                    match uu___21
                                                                    with
                                                                    | 
                                                                    Success
                                                                    ((x4,
                                                                    g14),
                                                                    cache14)
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
                                                                    fail_str
                                                                    "Redundant branches after wildcard"
                                                                    | 
                                                                    uu___25
                                                                    ->
                                                                    (fun
                                                                    uu___26
                                                                    cache ->
                                                                    Success
                                                                    (((eff_br,
                                                                    tbr),
                                                                    FStar_Pervasives_Native.None),
                                                                    cache)))
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
                                                                    ctx04
                                                                    cache14 in
                                                                    (match uu___22
                                                                    with
                                                                    | 
                                                                    Success
                                                                    ((y, g2),
                                                                    cache2)
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    and_pre
                                                                    g14 g2 in
                                                                    (y,
                                                                    uu___25) in
                                                                    (uu___24,
                                                                    cache2) in
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
                                                                    ctx03
                                                                    cache13 in
                                                                 (match uu___17
                                                                  with
                                                                  | Success
                                                                    ((y, g2),
                                                                    cache2)
                                                                    ->
                                                                    let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    and_pre
                                                                    g13 g2 in
                                                                    (y,
                                                                    uu___20) in
                                                                    (uu___19,
                                                                    cache2) in
                                                                    Success
                                                                    uu___18
                                                                  | err ->
                                                                    err)
                                                             | Error err ->
                                                                 Error err) in
                                                    uu___14 ctx02 cache12 in
                                                  (match uu___13 with
                                                   | Success
                                                       ((y, g2), cache2) ->
                                                       let uu___14 =
                                                         let uu___15 =
                                                           let uu___16 =
                                                             and_pre g12 g2 in
                                                           (y, uu___16) in
                                                         (uu___15, cache2) in
                                                       Success uu___14
                                                   | err -> err)
                                              | Error err -> Error err)) in
                                let uu___8 =
                                  match rc_opt with
                                  | FStar_Pervasives_Native.Some
                                      {
                                        FStarC_Syntax_Syntax.residual_effect
                                          = uu___9;
                                        FStarC_Syntax_Syntax.residual_typ =
                                          FStar_Pervasives_Native.Some t;
                                        FStarC_Syntax_Syntax.residual_flags =
                                          uu___10;_}
                                      ->
                                      let uu___11 = universe_of g t in
                                      (fun ctx02 cache02 ->
                                         let uu___12 = uu___11 ctx02 cache02 in
                                         match uu___12 with
                                         | Success ((x2, g12), cache12) ->
                                             let uu___13 =
                                               let uu___14 uu___15 cache =
                                                 Success
                                                   (((FStar_Pervasives_Native.Some
                                                        (E_Total, t)),
                                                      FStar_Pervasives_Native.None),
                                                     cache) in
                                               uu___14 ctx02 cache12 in
                                             (match uu___13 with
                                              | Success ((y, g2), cache2) ->
                                                  let uu___14 =
                                                    let uu___15 =
                                                      let uu___16 =
                                                        and_pre g12 g2 in
                                                      (y, uu___16) in
                                                    (uu___15, cache2) in
                                                  Success uu___14
                                              | err -> err)
                                         | Error err -> Error err)
                                  | uu___9 ->
                                      (fun uu___10 cache ->
                                         Success
                                           ((FStar_Pervasives_Native.None,
                                              FStar_Pervasives_Native.None),
                                             cache)) in
                                fun ctx02 cache02 ->
                                  let uu___9 = uu___8 ctx02 cache02 in
                                  match uu___9 with
                                  | Success ((x2, g12), cache12) ->
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
                                            fun ctx1 cache ->
                                              let ctx2 =
                                                {
                                                  no_guard = (ctx1.no_guard);
                                                  unfolding_ok =
                                                    (ctx1.unfolding_ok);
                                                  error_context =
                                                    (("check_branches", ctx)
                                                    :: (ctx1.error_context))
                                                } in
                                              let uu___13 =
                                                check_branches
                                                  FStarC_Syntax_Util.exp_true_bool
                                                  x2 branches in
                                              uu___13 ctx2 cache in
                                          fun ctx03 cache03 ->
                                            let uu___13 =
                                              uu___12 ctx03 cache03 in
                                            match uu___13 with
                                            | Success ((x3, g13), cache13) ->
                                                let uu___14 =
                                                  let uu___15 =
                                                    match x3 with
                                                    | (eff_br, t_br) ->
                                                        (fun uu___16 cache ->
                                                           Success
                                                             ((((join_eff
                                                                   eff_sc
                                                                   eff_br),
                                                                 t_br),
                                                                FStar_Pervasives_Native.None),
                                                               cache)) in
                                                  uu___15 ctx03 cache13 in
                                                (match uu___14 with
                                                 | Success ((y, g2), cache2)
                                                     ->
                                                     let uu___15 =
                                                       let uu___16 =
                                                         let uu___17 =
                                                           and_pre g13 g2 in
                                                         (y, uu___17) in
                                                       (uu___16, cache2) in
                                                     Success uu___15
                                                 | err -> err)
                                            | Error err -> Error err in
                                        uu___11 ctx02 cache12 in
                                      (match uu___10 with
                                       | Success ((y, g2), cache2) ->
                                           let uu___11 =
                                             let uu___12 =
                                               let uu___13 = and_pre g12 g2 in
                                               (y, uu___13) in
                                             (uu___12, cache2) in
                                           Success uu___11
                                       | err -> err)
                                  | Error err -> Error err in
                              uu___7 ctx01 cache11 in
                            (match uu___6 with
                             | Success ((y, g2), cache2) ->
                                 let uu___7 =
                                   let uu___8 =
                                     let uu___9 = and_pre g11 g2 in
                                     (y, uu___9) in
                                   (uu___8, cache2) in
                                 Success uu___7
                             | err -> err)
                        | Error err -> Error err) in
               uu___3 ctx0 cache1 in
             (match uu___2 with
              | Success ((y, g2), cache2) ->
                  let uu___3 =
                    let uu___4 = let uu___5 = and_pre g1 g2 in (y, uu___5) in
                    (uu___4, cache2) in
                  Success uu___3
              | err -> err)
         | Error err -> Error err)
  | FStarC_Syntax_Syntax.Tm_match
      { FStarC_Syntax_Syntax.scrutinee = sc;
        FStarC_Syntax_Syntax.ret_opt = FStar_Pervasives_Native.Some
          (as_x,
           (FStar_Pervasives.Inl returns_ty, FStar_Pervasives_Native.None,
            eq));
        FStarC_Syntax_Syntax.brs = branches;
        FStarC_Syntax_Syntax.rc_opt1 = rc_opt;_}
      ->
      let uu___ = check "scrutinee" g sc in
      (fun ctx0 cache0 ->
         let uu___1 = uu___ ctx0 cache0 in
         match uu___1 with
         | Success ((x, g1), cache1) ->
             let uu___2 =
               let uu___3 =
                 match x with
                 | (eff_sc, t_sc) ->
                     let uu___4 = universe_of_well_typed_term g t_sc in
                     (fun ctx01 cache01 ->
                        let uu___5 = uu___4 ctx01 cache01 in
                        match uu___5 with
                        | Success ((x1, g11), cache11) ->
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
                                    FStarC_Syntax_Syntax.binder_positivity =
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
                                      with_binders g [as_x2] [x1] uu___10 in
                                    (fun ctx02 cache02 ->
                                       let uu___10 = uu___9 ctx02 cache02 in
                                       match uu___10 with
                                       | Success ((x2, g12), cache12) ->
                                           let uu___11 =
                                             let uu___12 =
                                               match x2 with
                                               | (_eff_t, returns_ty_t) ->
                                                   let uu___13 =
                                                     is_type g_as_x
                                                       returns_ty_t in
                                                   (fun ctx03 cache03 ->
                                                      let uu___14 =
                                                        uu___13 ctx03 cache03 in
                                                      match uu___14 with
                                                      | Success
                                                          ((x3, g13),
                                                           cache13)
                                                          ->
                                                          let uu___15 =
                                                            let uu___16 =
                                                              let rec check_branches
                                                                path_condition
                                                                branches1
                                                                acc_eff =
                                                                match branches1
                                                                with
                                                                | [] ->
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
                                                                    cache ->
                                                                    Success
                                                                    ((acc_eff,
                                                                    FStar_Pervasives_Native.None),
                                                                    cache))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    neg_path
                                                                    ->
                                                                    let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    FStarC_Syntax_Util.b2t
                                                                    neg_path in
                                                                    guard g
                                                                    uu___19 in
                                                                    (fun
                                                                    ctx04
                                                                    cache04
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    uu___18
                                                                    ctx04
                                                                    cache04 in
                                                                    match uu___19
                                                                    with
                                                                    | 
                                                                    Success
                                                                    ((x4,
                                                                    g14),
                                                                    cache14)
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    let uu___21
                                                                    uu___22
                                                                    cache =
                                                                    Success
                                                                    ((acc_eff,
                                                                    FStar_Pervasives_Native.None),
                                                                    cache) in
                                                                    uu___21
                                                                    ctx04
                                                                    cache14 in
                                                                    (match uu___20
                                                                    with
                                                                    | 
                                                                    Success
                                                                    ((y, g2),
                                                                    cache2)
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    and_pre
                                                                    g14 g2 in
                                                                    (y,
                                                                    uu___23) in
                                                                    (uu___22,
                                                                    cache2) in
                                                                    Success
                                                                    uu___21
                                                                    | 
                                                                    err ->
                                                                    err)
                                                                    | 
                                                                    Error err
                                                                    ->
                                                                    Error err))
                                                                | (p,
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
                                                                    ctx cache
                                                                    =
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
                                                                    ctx1
                                                                    cache in
                                                                    (fun
                                                                    ctx04
                                                                    cache04
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    uu___20
                                                                    ctx04
                                                                    cache04 in
                                                                    match uu___21
                                                                    with
                                                                    | 
                                                                    Success
                                                                    ((x4,
                                                                    g14),
                                                                    cache14)
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
                                                                    ctx05
                                                                    cache05
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    uu___24
                                                                    ctx05
                                                                    cache05 in
                                                                    match uu___25
                                                                    with
                                                                    | 
                                                                    Success
                                                                    ((x5,
                                                                    g15),
                                                                    cache15)
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
                                                                    FStarC_Option.must
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
                                                                    let g'0 =
                                                                    push_binders
                                                                    g bs in
                                                                    let g' =
                                                                    push_hypothesis
                                                                    g'0
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
                                                                    g' b1 in
                                                                    fun ctx06
                                                                    cache06
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    uu___32
                                                                    ctx06
                                                                    cache06 in
                                                                    match uu___33
                                                                    with
                                                                    | 
                                                                    Success
                                                                    ((x6,
                                                                    g16),
                                                                    cache16)
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
                                                                    ctx cache
                                                                    =
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
                                                                    g' rel
                                                                    tbr
                                                                    expect_tbr in
                                                                    uu___37
                                                                    ctx1
                                                                    cache in
                                                                    (fun
                                                                    ctx07
                                                                    cache07
                                                                    ->
                                                                    let uu___37
                                                                    =
                                                                    uu___36
                                                                    ctx07
                                                                    cache07 in
                                                                    match uu___37
                                                                    with
                                                                    | 
                                                                    Success
                                                                    ((x7,
                                                                    g17),
                                                                    cache17)
                                                                    ->
                                                                    let uu___38
                                                                    =
                                                                    let uu___39
                                                                    uu___40
                                                                    cache =
                                                                    Success
                                                                    ((((join_eff
                                                                    eff_br
                                                                    acc_eff),
                                                                    expect_tbr),
                                                                    FStar_Pervasives_Native.None),
                                                                    cache) in
                                                                    uu___39
                                                                    ctx07
                                                                    cache17 in
                                                                    (match uu___38
                                                                    with
                                                                    | 
                                                                    Success
                                                                    ((y, g2),
                                                                    cache2)
                                                                    ->
                                                                    let uu___39
                                                                    =
                                                                    let uu___40
                                                                    =
                                                                    let uu___41
                                                                    =
                                                                    and_pre
                                                                    g17 g2 in
                                                                    (y,
                                                                    uu___41) in
                                                                    (uu___40,
                                                                    cache2) in
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
                                                                    ctx06
                                                                    cache16 in
                                                                    (match uu___34
                                                                    with
                                                                    | 
                                                                    Success
                                                                    ((y, g2),
                                                                    cache2)
                                                                    ->
                                                                    let uu___35
                                                                    =
                                                                    let uu___36
                                                                    =
                                                                    let uu___37
                                                                    =
                                                                    and_pre
                                                                    g16 g2 in
                                                                    (y,
                                                                    uu___37) in
                                                                    (uu___36,
                                                                    cache2) in
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
                                                                    g'0
                                                                    this_path_condition
                                                                    uu___31 in
                                                                    with_binders
                                                                    g bs us
                                                                    uu___30 in
                                                                    (fun
                                                                    ctx06
                                                                    cache06
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    uu___29
                                                                    ctx06
                                                                    cache06 in
                                                                    match uu___30
                                                                    with
                                                                    | 
                                                                    Success
                                                                    ((x6,
                                                                    g16),
                                                                    cache16)
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
                                                                    fail_str
                                                                    "Redundant branches after wildcard"
                                                                    | 
                                                                    uu___34
                                                                    ->
                                                                    (fun
                                                                    uu___35
                                                                    cache ->
                                                                    Success
                                                                    ((eff_br,
                                                                    FStar_Pervasives_Native.None),
                                                                    cache)))
                                                                    | 
                                                                    uu___33
                                                                    ->
                                                                    check_branches
                                                                    next_path_condition
                                                                    rest
                                                                    eff_br) in
                                                                    uu___32
                                                                    ctx06
                                                                    cache16 in
                                                                    (match uu___31
                                                                    with
                                                                    | 
                                                                    Success
                                                                    ((y, g2),
                                                                    cache2)
                                                                    ->
                                                                    let uu___32
                                                                    =
                                                                    let uu___33
                                                                    =
                                                                    let uu___34
                                                                    =
                                                                    and_pre
                                                                    g16 g2 in
                                                                    (y,
                                                                    uu___34) in
                                                                    (uu___33,
                                                                    cache2) in
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
                                                                    ctx05
                                                                    cache15 in
                                                                    (match uu___26
                                                                    with
                                                                    | 
                                                                    Success
                                                                    ((y, g2),
                                                                    cache2)
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    let uu___29
                                                                    =
                                                                    and_pre
                                                                    g15 g2 in
                                                                    (y,
                                                                    uu___29) in
                                                                    (uu___28,
                                                                    cache2) in
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
                                                                    ctx04
                                                                    cache14 in
                                                                    (match uu___22
                                                                    with
                                                                    | 
                                                                    Success
                                                                    ((y, g2),
                                                                    cache2)
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    and_pre
                                                                    g14 g2 in
                                                                    (y,
                                                                    uu___25) in
                                                                    (uu___24,
                                                                    cache2) in
                                                                    Success
                                                                    uu___23
                                                                    | 
                                                                    err ->
                                                                    err)
                                                                    | 
                                                                    Error err
                                                                    ->
                                                                    Error err)) in
                                                              let uu___17 =
                                                                check_branches
                                                                  FStarC_Syntax_Util.exp_true_bool
                                                                  branches
                                                                  E_Total in
                                                              fun ctx04
                                                                cache04 ->
                                                                let uu___18 =
                                                                  uu___17
                                                                    ctx04
                                                                    cache04 in
                                                                match uu___18
                                                                with
                                                                | Success
                                                                    ((x4,
                                                                    g14),
                                                                    cache14)
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
                                                                    cache ->
                                                                    Success
                                                                    (((x4,
                                                                    ty),
                                                                    FStar_Pervasives_Native.None),
                                                                    cache) in
                                                                    uu___20
                                                                    ctx04
                                                                    cache14 in
                                                                    (match uu___19
                                                                    with
                                                                    | 
                                                                    Success
                                                                    ((y, g2),
                                                                    cache2)
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    and_pre
                                                                    g14 g2 in
                                                                    (y,
                                                                    uu___22) in
                                                                    (uu___21,
                                                                    cache2) in
                                                                    Success
                                                                    uu___20
                                                                    | 
                                                                    err ->
                                                                    err)
                                                                | Error err
                                                                    ->
                                                                    Error err in
                                                            uu___16 ctx03
                                                              cache13 in
                                                          (match uu___15 with
                                                           | Success
                                                               ((y, g2),
                                                                cache2)
                                                               ->
                                                               let uu___16 =
                                                                 let uu___17
                                                                   =
                                                                   let uu___18
                                                                    =
                                                                    and_pre
                                                                    g13 g2 in
                                                                   (y,
                                                                    uu___18) in
                                                                 (uu___17,
                                                                   cache2) in
                                                               Success
                                                                 uu___16
                                                           | err -> err)
                                                      | Error err ->
                                                          Error err) in
                                             uu___12 ctx02 cache12 in
                                           (match uu___11 with
                                            | Success ((y, g2), cache2) ->
                                                let uu___12 =
                                                  let uu___13 =
                                                    let uu___14 =
                                                      and_pre g12 g2 in
                                                    (y, uu___14) in
                                                  (uu___13, cache2) in
                                                Success uu___12
                                            | err -> err)
                                       | Error err -> Error err) in
                              uu___7 ctx01 cache11 in
                            (match uu___6 with
                             | Success ((y, g2), cache2) ->
                                 let uu___7 =
                                   let uu___8 =
                                     let uu___9 = and_pre g11 g2 in
                                     (y, uu___9) in
                                   (uu___8, cache2) in
                                 Success uu___7
                             | err -> err)
                        | Error err -> Error err) in
               uu___3 ctx0 cache1 in
             (match uu___2 with
              | Success ((y, g2), cache2) ->
                  let uu___3 =
                    let uu___4 = let uu___5 = and_pre g1 g2 in (y, uu___5) in
                    (uu___4, cache2) in
                  Success uu___3
              | err -> err)
         | Error err -> Error err)
  | FStarC_Syntax_Syntax.Tm_match uu___ ->
      fail_str "Match with effect returns ascription, or tactic handler"
  | uu___ ->
      let uu___1 =
        let uu___2 =
          FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term e1 in
        FStarC_Format.fmt1 "Unexpected term: %s" uu___2 in
      fail_str uu___1
and check_binders (g_initial : env) (xs : FStarC_Syntax_Syntax.binders) :
  FStarC_Syntax_Syntax.universe Prims.list result=
  let rec aux g xs1 =
    match xs1 with
    | [] ->
        (fun uu___ cache ->
           Success (([], FStar_Pervasives_Native.None), cache))
    | x::xs2 ->
        let uu___ =
          check "binder sort" g
            (x.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
        (fun ctx0 cache0 ->
           let uu___1 = uu___ ctx0 cache0 in
           match uu___1 with
           | Success ((x1, g1), cache1) ->
               let uu___2 =
                 let uu___3 =
                   match x1 with
                   | (uu___4, t) ->
                       let uu___5 = is_type g t in
                       (fun ctx01 cache01 ->
                          let uu___6 = uu___5 ctx01 cache01 in
                          match uu___6 with
                          | Success ((x2, g11), cache11) ->
                              let uu___7 =
                                let uu___8 =
                                  let uu___9 =
                                    let uu___10 =
                                      let uu___11 = push_binder g x in
                                      aux uu___11 xs2 in
                                    fun ctx02 cache02 ->
                                      let uu___11 = uu___10 ctx02 cache02 in
                                      match uu___11 with
                                      | Success ((x3, g12), cache12) ->
                                          let uu___12 =
                                            let uu___13 uu___14 cache =
                                              Success
                                                (((x2 :: x3),
                                                   FStar_Pervasives_Native.None),
                                                  cache) in
                                            uu___13 ctx02 cache12 in
                                          (match uu___12 with
                                           | Success ((y, g2), cache2) ->
                                               let uu___13 =
                                                 let uu___14 =
                                                   let uu___15 =
                                                     and_pre g12 g2 in
                                                   (y, uu___15) in
                                                 (uu___14, cache2) in
                                               Success uu___13
                                           | err -> err)
                                      | Error err -> Error err in
                                  with_binders g [x] [x2] uu___9 in
                                uu___8 ctx01 cache11 in
                              (match uu___7 with
                               | Success ((y, g2), cache2) ->
                                   let uu___8 =
                                     let uu___9 =
                                       let uu___10 = and_pre g11 g2 in
                                       (y, uu___10) in
                                     (uu___9, cache2) in
                                   Success uu___8
                               | err -> err)
                          | Error err -> Error err) in
                 uu___3 ctx0 cache1 in
               (match uu___2 with
                | Success ((y, g2), cache2) ->
                    let uu___3 =
                      let uu___4 = let uu___5 = and_pre g1 g2 in (y, uu___5) in
                      (uu___4, cache2) in
                    Success uu___3
                | err -> err)
           | Error err -> Error err) in
  aux g_initial xs
and check_comp (g : env) (c : FStarC_Syntax_Syntax.comp) :
  FStarC_Syntax_Syntax.universe result=
  match c.FStarC_Syntax_Syntax.n with
  | FStarC_Syntax_Syntax.Total t ->
      let uu___ =
        let uu___1 = FStarC_Syntax_Util.comp_result c in
        check "(G)Tot comp result" g uu___1 in
      (fun ctx0 cache0 ->
         let uu___1 = uu___ ctx0 cache0 in
         match uu___1 with
         | Success ((x, g1), cache1) ->
             let uu___2 =
               let uu___3 = match x with | (uu___4, t1) -> is_type g t1 in
               uu___3 ctx0 cache1 in
             (match uu___2 with
              | Success ((y, g2), cache2) ->
                  let uu___3 =
                    let uu___4 = let uu___5 = and_pre g1 g2 in (y, uu___5) in
                    (uu___4, cache2) in
                  Success uu___3
              | err -> err)
         | Error err -> Error err)
  | FStarC_Syntax_Syntax.GTotal t ->
      let uu___ =
        let uu___1 = FStarC_Syntax_Util.comp_result c in
        check "(G)Tot comp result" g uu___1 in
      (fun ctx0 cache0 ->
         let uu___1 = uu___ ctx0 cache0 in
         match uu___1 with
         | Success ((x, g1), cache1) ->
             let uu___2 =
               let uu___3 = match x with | (uu___4, t1) -> is_type g t1 in
               uu___3 ctx0 cache1 in
             (match uu___2 with
              | Success ((y, g2), cache2) ->
                  let uu___3 =
                    let uu___4 = let uu___5 = and_pre g1 g2 in (y, uu___5) in
                    (uu___4, cache2) in
                  Success uu___3
              | err -> err)
         | Error err -> Error err)
  | FStarC_Syntax_Syntax.Comp ct ->
      if
        (FStarC_List.length ct.FStarC_Syntax_Syntax.comp_univs) <>
          Prims.int_one
      then fail_str "Unexpected/missing universe instantitation in comp"
      else
        (let u = FStarC_List.hd ct.FStarC_Syntax_Syntax.comp_univs in
         let effect_app_tm =
           let head =
             let uu___1 =
               FStarC_Syntax_Syntax.fvar ct.FStarC_Syntax_Syntax.effect_name
                 FStar_Pervasives_Native.None in
             FStarC_Syntax_Syntax.mk_Tm_uinst uu___1 [u] in
           let uu___1 =
             let uu___2 =
               FStarC_Syntax_Syntax.as_arg ct.FStarC_Syntax_Syntax.result_typ in
             uu___2 :: (ct.FStarC_Syntax_Syntax.effect_args) in
           FStarC_Syntax_Syntax.mk_Tm_app head uu___1
             (ct.FStarC_Syntax_Syntax.result_typ).FStarC_Syntax_Syntax.pos in
         let uu___1 = check "effectful comp" g effect_app_tm in
         fun ctx0 cache0 ->
           let uu___2 = uu___1 ctx0 cache0 in
           match uu___2 with
           | Success ((x, g1), cache1) ->
               let uu___3 =
                 let uu___4 =
                   match x with
                   | (uu___5, t) ->
                       let uu___6 ctx cache =
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
                         uu___7 ctx1 cache in
                       (fun ctx01 cache01 ->
                          let uu___7 = uu___6 ctx01 cache01 in
                          match uu___7 with
                          | Success ((x1, g11), cache11) ->
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
                                    FStarC_List.existsb
                                      (fun q ->
                                         q = FStarC_Syntax_Syntax.TotalEffect)
                                      uu___10 in
                                  if Prims.op_Negation is_total
                                  then
                                    fun uu___10 cache ->
                                      Success
                                        ((FStarC_Syntax_Syntax.U_zero,
                                           FStar_Pervasives_Native.None),
                                          cache)
                                  else
                                    (let uu___11 =
                                       FStarC_Syntax_Util.is_pure_or_ghost_effect
                                         c_lid in
                                     if uu___11
                                     then
                                       fun uu___12 cache ->
                                         Success
                                           ((u, FStar_Pervasives_Native.None),
                                             cache)
                                     else
                                       (let uu___13 =
                                          FStarC_TypeChecker_Env.effect_repr
                                            g.tcenv c u in
                                        match uu___13 with
                                        | FStar_Pervasives_Native.None ->
                                            let uu___14 =
                                              let uu___15 =
                                                let uu___16 =
                                                  let uu___17 =
                                                    FStarC_Errors_Msg.text
                                                      "Total effect" in
                                                  let uu___18 =
                                                    let uu___19 =
                                                      let uu___20 =
                                                        FStarC_Syntax_Util.comp_effect_name
                                                          c in
                                                      FStarC_Class_PP.pp
                                                        FStarC_Ident.pretty_lident
                                                        uu___20 in
                                                    let uu___20 =
                                                      let uu___21 =
                                                        FStarC_Errors_Msg.text
                                                          "(normalized to" in
                                                      let uu___22 =
                                                        let uu___23 =
                                                          let uu___24 =
                                                            FStarC_Class_PP.pp
                                                              FStarC_Ident.pretty_lident
                                                              c_lid in
                                                          FStar_Pprint.op_Hat_Hat
                                                            uu___24
                                                            (FStar_Pprint.doc_of_string
                                                               ")") in
                                                        let uu___24 =
                                                          let uu___25 =
                                                            FStarC_Errors_Msg.text
                                                              "does not have a representation." in
                                                          [uu___25] in
                                                        uu___23 :: uu___24 in
                                                      uu___21 :: uu___22 in
                                                    uu___19 :: uu___20 in
                                                  uu___17 :: uu___18 in
                                                FStar_Pprint.flow
                                                  (FStar_Pprint.break_
                                                     Prims.int_one) uu___16 in
                                              [uu___15] in
                                            fail uu___14
                                        | FStar_Pervasives_Native.Some tm ->
                                            universe_of g tm)) in
                                uu___9 ctx01 cache11 in
                              (match uu___8 with
                               | Success ((y, g2), cache2) ->
                                   let uu___9 =
                                     let uu___10 =
                                       let uu___11 = and_pre g11 g2 in
                                       (y, uu___11) in
                                     (uu___10, cache2) in
                                   Success uu___9
                               | err -> err)
                          | Error err -> Error err) in
                 uu___4 ctx0 cache1 in
               (match uu___3 with
                | Success ((y, g2), cache2) ->
                    let uu___4 =
                      let uu___5 = let uu___6 = and_pre g1 g2 in (y, uu___6) in
                      (uu___5, cache2) in
                    Success uu___4
                | err -> err)
           | Error err -> Error err)
and universe_of (g : env) (t : FStarC_Syntax_Syntax.typ) :
  FStarC_Syntax_Syntax.universe result=
  let uu___ = check "universe of" g t in
  fun ctx0 cache0 ->
    let uu___1 = uu___ ctx0 cache0 in
    match uu___1 with
    | Success ((x, g1), cache1) ->
        let uu___2 =
          let uu___3 = match x with | (uu___4, t1) -> is_type g t1 in
          uu___3 ctx0 cache1 in
        (match uu___2 with
         | Success ((y, g2), cache2) ->
             let uu___3 =
               let uu___4 = let uu___5 = and_pre g1 g2 in (y, uu___5) in
               (uu___4, cache2) in
             Success uu___3
         | err -> err)
    | Error err -> Error err
and universe_of_well_typed_term (g : env) (t : FStarC_Syntax_Syntax.typ) :
  FStarC_Syntax_Syntax.universe result=
  try
    (fun uu___ ->
       match () with
       | () ->
           let u = FStarC_TypeChecker_TcTerm.universe_of g.tcenv t in
           (fun uu___1 cache ->
              Success ((u, FStar_Pervasives_Native.None), cache))) ()
  with | uu___ -> universe_of g t
and check_pat (g : env) (p : FStarC_Syntax_Syntax.pat)
  (t_sc : FStarC_Syntax_Syntax.typ) :
  (FStarC_Syntax_Syntax.binders * FStarC_Syntax_Syntax.universes) result=
  let unrefine_tsc t_sc1 =
    let uu___ =
      FStarC_TypeChecker_Normalize.normalize_refinement
        FStarC_TypeChecker_Normalize.whnf_steps g.tcenv t_sc1 in
    FStarC_Syntax_Util.unrefine uu___ in
  match p.FStarC_Syntax_Syntax.v with
  | FStarC_Syntax_Syntax.Pat_constant c ->
      let e =
        match c with
        | FStarC_Const.Const_int (repr, FStar_Pervasives_Native.Some sw) ->
            FStarC_ToSyntax_ToSyntax.desugar_machine_integer
              (g.tcenv).FStarC_TypeChecker_Env.dsenv repr sw
              p.FStarC_Syntax_Syntax.p
        | uu___ ->
            FStarC_Syntax_Syntax.mk (FStarC_Syntax_Syntax.Tm_constant c)
              p.FStarC_Syntax_Syntax.p in
      let uu___ = check "pat_const" g e in
      (fun ctx0 cache0 ->
         let uu___1 = uu___ ctx0 cache0 in
         match uu___1 with
         | Success ((x, g1), cache1) ->
             let uu___2 =
               let uu___3 =
                 match x with
                 | (uu___4, t_const) ->
                     let uu___5 ctx cache =
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
                         check_subtype g (FStar_Pervasives_Native.Some e)
                           t_const uu___7 in
                       uu___6 ctx1 cache in
                     (fun ctx01 cache01 ->
                        let uu___6 = uu___5 ctx01 cache01 in
                        match uu___6 with
                        | Success ((x1, g11), cache11) ->
                            let uu___7 =
                              let uu___8 uu___9 cache =
                                Success
                                  ((([], []), FStar_Pervasives_Native.None),
                                    cache) in
                              uu___8 ctx01 cache11 in
                            (match uu___7 with
                             | Success ((y, g2), cache2) ->
                                 let uu___8 =
                                   let uu___9 =
                                     let uu___10 = and_pre g11 g2 in
                                     (y, uu___10) in
                                   (uu___9, cache2) in
                                 Success uu___8
                             | err -> err)
                        | Error err -> Error err) in
               uu___3 ctx0 cache1 in
             (match uu___2 with
              | Success ((y, g2), cache2) ->
                  let uu___3 =
                    let uu___4 = let uu___5 = and_pre g1 g2 in (y, uu___5) in
                    (uu___4, cache2) in
                  Success uu___3
              | err -> err)
         | Error err -> Error err)
  | FStarC_Syntax_Syntax.Pat_var bv ->
      let b =
        FStarC_Syntax_Syntax.mk_binder
          {
            FStarC_Syntax_Syntax.ppname = (bv.FStarC_Syntax_Syntax.ppname);
            FStarC_Syntax_Syntax.index = (bv.FStarC_Syntax_Syntax.index);
            FStarC_Syntax_Syntax.sort = t_sc
          } in
      let uu___ ctx cache =
        let ctx1 =
          {
            no_guard = (ctx.no_guard);
            unfolding_ok = (ctx.unfolding_ok);
            error_context =
              (("check_pat_binder", FStar_Pervasives_Native.None) ::
              (ctx.error_context))
          } in
        let uu___1 = check_binders g [b] in uu___1 ctx1 cache in
      (fun ctx0 cache0 ->
         let uu___1 = uu___ ctx0 cache0 in
         match uu___1 with
         | Success ((x, g1), cache1) ->
             let uu___2 =
               let uu___3 =
                 match x with
                 | u::[] ->
                     (fun uu___4 cache ->
                        Success
                          ((([b], [u]), FStar_Pervasives_Native.None), cache)) in
               uu___3 ctx0 cache1 in
             (match uu___2 with
              | Success ((y, g2), cache2) ->
                  let uu___3 =
                    let uu___4 = let uu___5 = and_pre g1 g2 in (y, uu___5) in
                    (uu___4, cache2) in
                  Success uu___3
              | err -> err)
         | Error err -> Error err)
  | FStarC_Syntax_Syntax.Pat_cons (fv, usopt, pats) ->
      let us =
        if FStar_Pervasives_Native.uu___is_None usopt
        then []
        else FStarC_Option.must usopt in
      let uu___ =
        let uu___1 =
          let uu___2 = FStarC_Syntax_Syntax.lid_of_fv fv in
          FStarC_TypeChecker_Env.lookup_and_inst_datacon g.tcenv us uu___2 in
        FStarC_Syntax_Util.arrow_formals uu___1 in
      (match uu___ with
       | (formals, t_pat) ->
           let uu___1 =
             let pats1 = FStarC_List.map FStar_Pervasives_Native.fst pats in
             let uu___2 =
               let uu___3 =
                 FStarC_Util.prefix_until
                   (fun p1 ->
                      match p1.FStarC_Syntax_Syntax.v with
                      | FStarC_Syntax_Syntax.Pat_dot_term uu___4 -> false
                      | uu___4 -> true) pats1 in
               FStarC_Option.map
                 (fun uu___4 ->
                    match uu___4 with
                    | (dot_pats, pat, rest_pats) ->
                        (dot_pats, (pat :: rest_pats))) uu___3 in
             FStarC_Option.dflt (pats1, []) uu___2 in
           (match uu___1 with
            | (dot_pats, rest_pats) ->
                let uu___2 =
                  FStarC_List.splitAt (FStarC_List.length dot_pats) formals in
                (match uu___2 with
                 | (dot_formals, rest_formals) ->
                     let uu___3 =
                       fold2
                         (fun ss uu___4 p1 ->
                            match uu___4 with
                            | { FStarC_Syntax_Syntax.binder_bv = f;
                                FStarC_Syntax_Syntax.binder_qual = uu___5;
                                FStarC_Syntax_Syntax.binder_positivity =
                                  uu___6;
                                FStarC_Syntax_Syntax.binder_attrs = uu___7;_}
                                ->
                                let expected_t =
                                  FStarC_Syntax_Subst.subst ss
                                    f.FStarC_Syntax_Syntax.sort in
                                let uu___8 =
                                  match p1.FStarC_Syntax_Syntax.v with
                                  | FStarC_Syntax_Syntax.Pat_dot_term
                                      (FStar_Pervasives_Native.Some t) ->
                                      (fun uu___9 cache ->
                                         Success
                                           ((t, FStar_Pervasives_Native.None),
                                             cache))
                                  | uu___9 ->
                                      fail_str
                                        "check_pat in core has unset dot pattern" in
                                (fun ctx0 cache0 ->
                                   let uu___9 = uu___8 ctx0 cache0 in
                                   match uu___9 with
                                   | Success ((x, g1), cache1) ->
                                       let uu___10 =
                                         let uu___11 =
                                           let uu___12 =
                                             check "pat dot term" g x in
                                           fun ctx01 cache01 ->
                                             let uu___13 =
                                               uu___12 ctx01 cache01 in
                                             match uu___13 with
                                             | Success ((x1, g11), cache11)
                                                 ->
                                                 let uu___14 =
                                                   let uu___15 =
                                                     match x1 with
                                                     | (uu___16, p_t) ->
                                                         let uu___17 ctx
                                                           cache =
                                                           let ctx1 =
                                                             {
                                                               no_guard =
                                                                 (ctx.no_guard);
                                                               unfolding_ok =
                                                                 (ctx.unfolding_ok);
                                                               error_context
                                                                 =
                                                                 (("check_pat cons",
                                                                    FStar_Pervasives_Native.None)
                                                                 ::
                                                                 (ctx.error_context))
                                                             } in
                                                           let uu___18 =
                                                             check_subtype g
                                                               (FStar_Pervasives_Native.Some
                                                                  x) p_t
                                                               expected_t in
                                                           uu___18 ctx1 cache in
                                                         (fun ctx02 cache02
                                                            ->
                                                            let uu___18 =
                                                              uu___17 ctx02
                                                                cache02 in
                                                            match uu___18
                                                            with
                                                            | Success
                                                                ((x2, g12),
                                                                 cache12)
                                                                ->
                                                                let uu___19 =
                                                                  let uu___20
                                                                    uu___21
                                                                    cache =
                                                                    Success
                                                                    (((FStar_List_Tot_Base.op_At
                                                                    ss
                                                                    [
                                                                    FStarC_Syntax_Syntax.NT
                                                                    (f, x)]),
                                                                    FStar_Pervasives_Native.None),
                                                                    cache) in
                                                                  uu___20
                                                                    ctx02
                                                                    cache12 in
                                                                (match uu___19
                                                                 with
                                                                 | Success
                                                                    ((y, g2),
                                                                    cache2)
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    and_pre
                                                                    g12 g2 in
                                                                    (y,
                                                                    uu___22) in
                                                                    (uu___21,
                                                                    cache2) in
                                                                    Success
                                                                    uu___20
                                                                 | err -> err)
                                                            | Error err ->
                                                                Error err) in
                                                   uu___15 ctx01 cache11 in
                                                 (match uu___14 with
                                                  | Success ((y, g2), cache2)
                                                      ->
                                                      let uu___15 =
                                                        let uu___16 =
                                                          let uu___17 =
                                                            and_pre g11 g2 in
                                                          (y, uu___17) in
                                                        (uu___16, cache2) in
                                                      Success uu___15
                                                  | err -> err)
                                             | Error err -> Error err in
                                         uu___11 ctx0 cache1 in
                                       (match uu___10 with
                                        | Success ((y, g2), cache2) ->
                                            let uu___11 =
                                              let uu___12 =
                                                let uu___13 = and_pre g1 g2 in
                                                (y, uu___13) in
                                              (uu___12, cache2) in
                                            Success uu___11
                                        | err -> err)
                                   | Error err -> Error err)) [] dot_formals
                         dot_pats in
                     (fun ctx0 cache0 ->
                        let uu___4 = uu___3 ctx0 cache0 in
                        match uu___4 with
                        | Success ((x, g1), cache1) ->
                            let uu___5 =
                              let uu___6 =
                                let uu___7 =
                                  fold2
                                    (fun uu___8 uu___9 p1 ->
                                       match (uu___8, uu___9) with
                                       | ((g2, ss, bs, us1),
                                          {
                                            FStarC_Syntax_Syntax.binder_bv =
                                              f;
                                            FStarC_Syntax_Syntax.binder_qual
                                              = uu___10;
                                            FStarC_Syntax_Syntax.binder_positivity
                                              = uu___11;
                                            FStarC_Syntax_Syntax.binder_attrs
                                              = uu___12;_})
                                           ->
                                           let expected_t =
                                             FStarC_Syntax_Subst.subst ss
                                               f.FStarC_Syntax_Syntax.sort in
                                           let uu___13 =
                                             let uu___14 =
                                               check_pat g2 p1 expected_t in
                                             with_binders g2 bs us1 uu___14 in
                                           (fun ctx01 cache01 ->
                                              let uu___14 =
                                                uu___13 ctx01 cache01 in
                                              match uu___14 with
                                              | Success ((x1, g11), cache11)
                                                  ->
                                                  let uu___15 =
                                                    let uu___16 =
                                                      match x1 with
                                                      | (bs_p, us_p) ->
                                                          let p_e =
                                                            let uu___17 =
                                                              let uu___18 =
                                                                FStarC_TypeChecker_PatternUtils.raw_pat_as_exp
                                                                  g2.tcenv p1 in
                                                              FStarC_Option.must
                                                                uu___18 in
                                                            FStar_Pervasives_Native.fst
                                                              uu___17 in
                                                          let uu___17 =
                                                            let uu___18 =
                                                              push_binders g2
                                                                bs_p in
                                                            (uu___18,
                                                              (FStar_List_Tot_Base.op_At
                                                                 ss
                                                                 [FStarC_Syntax_Syntax.NT
                                                                    (f, p_e)]),
                                                              (FStar_List_Tot_Base.op_At
                                                                 bs bs_p),
                                                              (FStar_List_Tot_Base.op_At
                                                                 us1 us_p)) in
                                                          (fun uu___18 cache
                                                             ->
                                                             Success
                                                               ((uu___17,
                                                                  FStar_Pervasives_Native.None),
                                                                 cache)) in
                                                    uu___16 ctx01 cache11 in
                                                  (match uu___15 with
                                                   | Success
                                                       ((y, g21), cache2) ->
                                                       let uu___16 =
                                                         let uu___17 =
                                                           let uu___18 =
                                                             and_pre g11 g21 in
                                                           (y, uu___18) in
                                                         (uu___17, cache2) in
                                                       Success uu___16
                                                   | err -> err)
                                              | Error err -> Error err))
                                    (g, x, [], []) rest_formals rest_pats in
                                fun ctx01 cache01 ->
                                  let uu___8 = uu___7 ctx01 cache01 in
                                  match uu___8 with
                                  | Success ((x1, g11), cache11) ->
                                      let uu___9 =
                                        let uu___10 =
                                          match x1 with
                                          | (uu___11, ss, bs, us1) ->
                                              let t_pat1 =
                                                FStarC_Syntax_Subst.subst ss
                                                  t_pat in
                                              let uu___12 =
                                                let uu___13 =
                                                  let uu___14 =
                                                    unrefine_tsc t_sc in
                                                  check_scrutinee_pattern_type_compatible
                                                    g uu___14 t_pat1 in
                                                no_guard uu___13 in
                                              (fun ctx02 cache02 ->
                                                 let uu___13 =
                                                   uu___12 ctx02 cache02 in
                                                 match uu___13 with
                                                 | Success
                                                     ((x2, g12), cache12) ->
                                                     let uu___14 =
                                                       let uu___15 uu___16
                                                         cache =
                                                         Success
                                                           (((bs, us1),
                                                              FStar_Pervasives_Native.None),
                                                             cache) in
                                                       uu___15 ctx02 cache12 in
                                                     (match uu___14 with
                                                      | Success
                                                          ((y, g2), cache2)
                                                          ->
                                                          let uu___15 =
                                                            let uu___16 =
                                                              let uu___17 =
                                                                and_pre g12
                                                                  g2 in
                                                              (y, uu___17) in
                                                            (uu___16, cache2) in
                                                          Success uu___15
                                                      | err -> err)
                                                 | Error err -> Error err) in
                                        uu___10 ctx01 cache11 in
                                      (match uu___9 with
                                       | Success ((y, g2), cache2) ->
                                           let uu___10 =
                                             let uu___11 =
                                               let uu___12 = and_pre g11 g2 in
                                               (y, uu___12) in
                                             (uu___11, cache2) in
                                           Success uu___10
                                       | err -> err)
                                  | Error err -> Error err in
                              uu___6 ctx0 cache1 in
                            (match uu___5 with
                             | Success ((y, g2), cache2) ->
                                 let uu___6 =
                                   let uu___7 =
                                     let uu___8 = and_pre g1 g2 in
                                     (y, uu___8) in
                                   (uu___7, cache2) in
                                 Success uu___6
                             | err -> err)
                        | Error err -> Error err))))
  | uu___ -> fail_str "check_pat called with a dot pattern"
and check_scrutinee_pattern_type_compatible (g : env)
  (t_sc : FStarC_Syntax_Syntax.typ) (t_pat : FStarC_Syntax_Syntax.typ) :
  precondition result=
  let err s =
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStarC_Errors_Msg.text "Scrutinee type" in
          let uu___4 =
            let uu___5 =
              FStarC_Class_PP.pp FStarC_Syntax_Print.pretty_term t_sc in
            let uu___6 =
              let uu___7 = FStarC_Errors_Msg.text "and pattern type" in
              let uu___8 =
                let uu___9 =
                  FStarC_Class_PP.pp FStarC_Syntax_Print.pretty_term t_pat in
                let uu___10 =
                  let uu___11 =
                    FStarC_Errors_Msg.text "are not compatible because" in
                  let uu___12 =
                    let uu___13 = FStarC_Errors_Msg.text s in [uu___13] in
                  uu___11 :: uu___12 in
                uu___9 :: uu___10 in
              uu___7 :: uu___8 in
            uu___5 :: uu___6 in
          uu___3 :: uu___4 in
        FStar_Pprint.flow (FStar_Pprint.break_ Prims.int_one) uu___2 in
      [uu___1] in
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
                 (fun uu___4 cache ->
                    Success ((fv_head, FStar_Pervasives_Native.None), cache))
             | (FStarC_Syntax_Syntax.Tm_uinst
                ({
                   FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_fvar
                     fv_head;
                   FStarC_Syntax_Syntax.pos = uu___4;
                   FStarC_Syntax_Syntax.vars = uu___5;
                   FStarC_Syntax_Syntax.hash_code = uu___6;_},
                 us_head),
                FStarC_Syntax_Syntax.Tm_uinst
                ({
                   FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_fvar
                     fv_pat;
                   FStarC_Syntax_Syntax.pos = uu___7;
                   FStarC_Syntax_Syntax.vars = uu___8;
                   FStarC_Syntax_Syntax.hash_code = uu___9;_},
                 us_pat)) when
                 let uu___10 = FStarC_Syntax_Syntax.lid_of_fv fv_head in
                 let uu___11 = FStarC_Syntax_Syntax.lid_of_fv fv_pat in
                 FStarC_Ident.lid_equals uu___10 uu___11 ->
                 let uu___10 =
                   FStarC_TypeChecker_Rel.teq_nosmt_force g.tcenv head_sc
                     head_pat in
                 if uu___10
                 then
                   (fun uu___11 cache ->
                      Success
                        ((fv_head, FStar_Pervasives_Native.None), cache))
                 else err "Incompatible universe instantiations"
             | (uu___4, uu___5) ->
                 let uu___6 =
                   let uu___7 =
                     FStarC_Class_Tagged.tag_of
                       FStarC_Syntax_Syntax.tagged_term head_sc in
                   let uu___8 =
                     FStarC_Class_Tagged.tag_of
                       FStarC_Syntax_Syntax.tagged_term head_pat in
                   FStarC_Format.fmt2 "Head constructors(%s and %s) not fvar"
                     uu___7 uu___8 in
                 err uu___6 in
           (fun ctx0 cache0 ->
              let uu___3 = uu___2 ctx0 cache0 in
              match uu___3 with
              | Success ((x, g1), cache1) ->
                  let uu___4 =
                    let uu___5 =
                      let uu___6 =
                        let uu___7 =
                          let uu___8 = FStarC_Syntax_Syntax.lid_of_fv x in
                          FStarC_TypeChecker_Env.is_type_constructor 
                            g.tcenv uu___8 in
                        if uu___7
                        then
                          fun uu___8 cache ->
                            Success
                              ((x, FStar_Pervasives_Native.None), cache)
                        else
                          (let uu___9 =
                             let uu___10 =
                               FStarC_Class_Show.show
                                 FStarC_Syntax_Syntax.showable_fv x in
                             FStarC_Format.fmt1
                               "%s is not a type constructor" uu___10 in
                           err uu___9) in
                      fun ctx01 cache01 ->
                        let uu___7 = uu___6 ctx01 cache01 in
                        match uu___7 with
                        | Success ((x1, g11), cache11) ->
                            let uu___8 =
                              let uu___9 =
                                let uu___10 =
                                  if
                                    (FStarC_List.length args_sc) =
                                      (FStarC_List.length args_pat)
                                  then
                                    fun uu___11 cache ->
                                      Success
                                        ((x, FStar_Pervasives_Native.None),
                                          cache)
                                  else
                                    (let uu___12 =
                                       let uu___13 =
                                         FStarC_Class_Show.show
                                           FStarC_Class_Show.showable_nat
                                           (FStarC_List.length args_sc) in
                                       let uu___14 =
                                         FStarC_Class_Show.show
                                           FStarC_Class_Show.showable_nat
                                           (FStarC_List.length args_pat) in
                                       FStarC_Format.fmt2
                                         "Number of arguments don't match (%s and %s)"
                                         uu___13 uu___14 in
                                     err uu___12) in
                                fun ctx02 cache02 ->
                                  let uu___11 = uu___10 ctx02 cache02 in
                                  match uu___11 with
                                  | Success ((x2, g12), cache12) ->
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
                                            | FStar_Pervasives_Native.None ->
                                                (args_sc, args_pat)
                                            | FStar_Pervasives_Native.Some n
                                                ->
                                                let uu___16 =
                                                  let uu___17 =
                                                    FStarC_Util.first_N n
                                                      args_sc in
                                                  FStar_Pervasives_Native.fst
                                                    uu___17 in
                                                let uu___17 =
                                                  let uu___18 =
                                                    FStarC_Util.first_N n
                                                      args_pat in
                                                  FStar_Pervasives_Native.fst
                                                    uu___18 in
                                                (uu___16, uu___17) in
                                          match uu___14 with
                                          | (params_sc, params_pat) ->
                                              let uu___15 =
                                                iter2 params_sc params_pat
                                                  (fun uu___16 uu___17
                                                     uu___18 ->
                                                     match (uu___16, uu___17)
                                                     with
                                                     | ((t_sc1, uu___19),
                                                        (t_pat1, uu___20)) ->
                                                         check_relation g
                                                           EQUALITY t_sc1
                                                           t_pat1) () in
                                              (fun ctx03 cache03 ->
                                                 let uu___16 =
                                                   uu___15 ctx03 cache03 in
                                                 match uu___16 with
                                                 | Success
                                                     ((x3, g13), cache13) ->
                                                     let uu___17 =
                                                       let uu___18 uu___19
                                                         cache =
                                                         Success
                                                           ((FStar_Pervasives_Native.None,
                                                              FStar_Pervasives_Native.None),
                                                             cache) in
                                                       uu___18 ctx03 cache13 in
                                                     (match uu___17 with
                                                      | Success
                                                          ((y, g2), cache2)
                                                          ->
                                                          let uu___18 =
                                                            let uu___19 =
                                                              let uu___20 =
                                                                and_pre g13
                                                                  g2 in
                                                              (y, uu___20) in
                                                            (uu___19, cache2) in
                                                          Success uu___18
                                                      | err1 -> err1)
                                                 | Error err1 -> Error err1) in
                                        uu___13 ctx02 cache12 in
                                      (match uu___12 with
                                       | Success ((y, g2), cache2) ->
                                           let uu___13 =
                                             let uu___14 =
                                               let uu___15 = and_pre g12 g2 in
                                               (y, uu___15) in
                                             (uu___14, cache2) in
                                           Success uu___13
                                       | err1 -> err1)
                                  | Error err1 -> Error err1 in
                              uu___9 ctx01 cache11 in
                            (match uu___8 with
                             | Success ((y, g2), cache2) ->
                                 let uu___9 =
                                   let uu___10 =
                                     let uu___11 = and_pre g11 g2 in
                                     (y, uu___11) in
                                   (uu___10, cache2) in
                                 Success uu___9
                             | err1 -> err1)
                        | Error err1 -> Error err1 in
                    uu___5 ctx0 cache1 in
                  (match uu___4 with
                   | Success ((y, g2), cache2) ->
                       let uu___5 =
                         let uu___6 =
                           let uu___7 = and_pre g1 g2 in (y, uu___7) in
                         (uu___6, cache2) in
                       Success uu___5
                   | err1 -> err1)
              | Error err1 -> Error err1))
and pattern_branch_condition (g : env)
  (scrutinee : FStarC_Syntax_Syntax.term) (pat : FStarC_Syntax_Syntax.pat) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option result=
  match pat.FStarC_Syntax_Syntax.v with
  | FStarC_Syntax_Syntax.Pat_var uu___ ->
      (fun uu___1 cache ->
         Success
           ((FStar_Pervasives_Native.None, FStar_Pervasives_Native.None),
             cache))
  | FStarC_Syntax_Syntax.Pat_constant c ->
      let const_exp =
        let uu___ =
          FStarC_TypeChecker_PatternUtils.raw_pat_as_exp g.tcenv pat in
        match uu___ with
        | FStar_Pervasives_Native.None -> failwith "Impossible"
        | FStar_Pervasives_Native.Some (e, uu___1) -> e in
      let uu___ = check "constant pattern" g const_exp in
      (fun ctx0 cache0 ->
         let uu___1 = uu___ ctx0 cache0 in
         match uu___1 with
         | Success ((x, g1), cache1) ->
             let uu___2 =
               let uu___3 =
                 match x with
                 | (uu___4, t_const) ->
                     let uu___5 =
                       let uu___6 =
                         FStarC_Syntax_Util.mk_decidable_eq t_const scrutinee
                           const_exp in
                       FStar_Pervasives_Native.Some uu___6 in
                     (fun uu___6 cache ->
                        Success
                          ((uu___5, FStar_Pervasives_Native.None), cache)) in
               uu___3 ctx0 cache1 in
             (match uu___2 with
              | Success ((y, g2), cache2) ->
                  let uu___3 =
                    let uu___4 = let uu___5 = and_pre g1 g2 in (y, uu___5) in
                    (uu___4, cache2) in
                  Success uu___3
              | err -> err)
         | Error err -> Error err)
  | FStarC_Syntax_Syntax.Pat_cons (fv, us_opt, sub_pats) ->
      let wild_pat pos =
        let uu___ =
          let uu___1 = wild_bv FStarC_Syntax_Syntax.tun pos in
          FStarC_Syntax_Syntax.Pat_var uu___1 in
        FStarC_Syntax_Syntax.withinfo uu___ pos in
      let mk_head_discriminator uu___ =
        let pat1 =
          let uu___1 =
            let uu___2 =
              let uu___3 =
                FStarC_List.map
                  (fun uu___4 ->
                     match uu___4 with
                     | (s, b) ->
                         let uu___5 = wild_pat s.FStarC_Syntax_Syntax.p in
                         (uu___5, b)) sub_pats in
              (fv, us_opt, uu___3) in
            FStarC_Syntax_Syntax.Pat_cons uu___2 in
          FStarC_Syntax_Syntax.withinfo uu___1 pat.FStarC_Syntax_Syntax.p in
        let branch1 =
          (pat1, FStar_Pervasives_Native.None,
            FStarC_Syntax_Util.exp_true_bool) in
        let branch2 =
          let uu___1 =
            let uu___2 =
              let uu___3 =
                wild_bv FStarC_Syntax_Syntax.tun pat1.FStarC_Syntax_Syntax.p in
              FStarC_Syntax_Syntax.Pat_var uu___3 in
            FStarC_Syntax_Syntax.withinfo uu___2 pat1.FStarC_Syntax_Syntax.p in
          (uu___1, FStar_Pervasives_Native.None,
            FStarC_Syntax_Util.exp_false_bool) in
        FStarC_Syntax_Syntax.mk
          (FStarC_Syntax_Syntax.Tm_match
             {
               FStarC_Syntax_Syntax.scrutinee = scrutinee;
               FStarC_Syntax_Syntax.ret_opt = FStar_Pervasives_Native.None;
               FStarC_Syntax_Syntax.brs = [branch1; branch2];
               FStarC_Syntax_Syntax.rc_opt1 = FStar_Pervasives_Native.None
             }) scrutinee.FStarC_Syntax_Syntax.pos in
      let mk_ith_projector i =
        let uu___ =
          let bv =
            let uu___1 =
              wild_bv FStarC_Syntax_Syntax.tun
                scrutinee.FStarC_Syntax_Syntax.pos in
            {
              FStarC_Syntax_Syntax.ppname =
                (uu___1.FStarC_Syntax_Syntax.ppname);
              FStarC_Syntax_Syntax.index = Prims.int_one;
              FStarC_Syntax_Syntax.sort = (uu___1.FStarC_Syntax_Syntax.sort)
            } in
          let uu___1 =
            FStarC_Syntax_Syntax.withinfo (FStarC_Syntax_Syntax.Pat_var bv)
              scrutinee.FStarC_Syntax_Syntax.pos in
          (bv, uu___1) in
        match uu___ with
        | (ith_pat_var, ith_pat) ->
            let sub_pats1 =
              FStarC_List.mapi
                (fun j uu___1 ->
                   match uu___1 with
                   | (s, b) ->
                       if i <> j
                       then
                         let uu___2 = wild_pat s.FStarC_Syntax_Syntax.p in
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
              fv.FStarC_Syntax_Syntax.fv_name in
          FStarC_TypeChecker_Env.datacons_of_typ g.tcenv uu___1 in
        match uu___ with
        | (is_induc, datacons) ->
            if
              (Prims.op_Negation is_induc) ||
                ((FStarC_List.length datacons) > Prims.int_one)
            then
              let discriminator =
                FStarC_Syntax_Util.mk_discriminator
                  fv.FStarC_Syntax_Syntax.fv_name in
              let uu___1 =
                FStarC_TypeChecker_Env.try_lookup_lid g.tcenv discriminator in
              (match uu___1 with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | uu___2 ->
                   let uu___3 = mk_head_discriminator () in
                   FStar_Pervasives_Native.Some uu___3)
            else FStar_Pervasives_Native.None in
      let uu___ =
        mapi
          (fun i uu___1 ->
             match uu___1 with
             | (pi, uu___2) ->
                 (match pi.FStarC_Syntax_Syntax.v with
                  | FStarC_Syntax_Syntax.Pat_dot_term uu___3 ->
                      (fun uu___4 cache ->
                         Success
                           ((FStar_Pervasives_Native.None,
                              FStar_Pervasives_Native.None), cache))
                  | FStarC_Syntax_Syntax.Pat_var uu___3 ->
                      (fun uu___4 cache ->
                         Success
                           ((FStar_Pervasives_Native.None,
                              FStar_Pervasives_Native.None), cache))
                  | uu___3 ->
                      let scrutinee_sub_term = mk_ith_projector i in
                      pattern_branch_condition g scrutinee_sub_term pi))
          sub_pats in
      (fun ctx0 cache0 ->
         let uu___1 = uu___ ctx0 cache0 in
         match uu___1 with
         | Success ((x, g1), cache1) ->
             let uu___2 =
               let uu___3 =
                 let guards =
                   FStarC_List.collect
                     (fun uu___4 ->
                        match uu___4 with
                        | FStar_Pervasives_Native.None -> []
                        | FStar_Pervasives_Native.Some t -> [t])
                     (discrimination :: x) in
                 match guards with
                 | [] ->
                     (fun uu___4 cache ->
                        Success
                          ((FStar_Pervasives_Native.None,
                             FStar_Pervasives_Native.None), cache))
                 | guards1 ->
                     let uu___4 =
                       let uu___5 = FStarC_Syntax_Util.mk_and_l guards1 in
                       FStar_Pervasives_Native.Some uu___5 in
                     (fun uu___5 cache ->
                        Success
                          ((uu___4, FStar_Pervasives_Native.None), cache)) in
               uu___3 ctx0 cache1 in
             (match uu___2 with
              | Success ((y, g2), cache2) ->
                  let uu___3 =
                    let uu___4 = let uu___5 = and_pre g1 g2 in (y, uu___5) in
                    (uu___4, cache2) in
                  Success uu___3
              | err -> err)
         | Error err -> Error err)
let initial_env (g : FStarC_TypeChecker_Env.env) : env=
  let max_index =
    FStarC_List.fold_left
      (fun index b ->
         match b with
         | FStarC_Syntax_Syntax.Binding_var x ->
             max x.FStarC_Syntax_Syntax.index index
         | uu___ -> index) Prims.int_zero g.FStarC_TypeChecker_Env.gamma in
  {
    tcenv = g;
    allow_universe_instantiation = false;
    should_read_cache = true;
    max_binder_index = max_index
  }
let check_term_top' (g : FStarC_TypeChecker_Env.env)
  (e : FStarC_Syntax_Syntax.term)
  (topt : FStarC_Syntax_Syntax.typ FStar_Pervasives_Native.option)
  (must_tot : Prims.bool) : (tot_or_ghost * FStarC_Syntax_Syntax.typ) result=
  let g1 = initial_env g in
  let uu___ = check "top" g1 e in
  fun ctx0 cache0 ->
    let uu___1 = uu___ ctx0 cache0 in
    match uu___1 with
    | Success ((x, g11), cache1) ->
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
                       then fail_str "expected total effect, found ghost"
                       else
                         (fun uu___7 cache ->
                            Success
                              (((E_Total, t), FStar_Pervasives_Native.None),
                                cache)))
                else
                  (fun uu___5 cache ->
                     Success ((x, FStar_Pervasives_Native.None), cache))
            | FStar_Pervasives_Native.Some t ->
                let uu___4 =
                  if must_tot || ((FStar_Pervasives_Native.fst x) = E_Total)
                  then
                    let uu___5 = FStarC_Syntax_Syntax.mk_Total t in
                    (uu___5, E_Total)
                  else
                    (let uu___6 = FStarC_Syntax_Syntax.mk_GTotal t in
                     (uu___6, E_Ghost)) in
                (match uu___4 with
                 | (target_comp, eff) ->
                     let uu___5 ctx cache =
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
                             should_read_cache = (g1.should_read_cache);
                             max_binder_index = (g1.max_binder_index)
                           } (SUBTYPING (FStar_Pervasives_Native.Some e))
                           uu___7 target_comp in
                       uu___6 ctx1 cache in
                     (fun ctx01 cache01 ->
                        let uu___6 = uu___5 ctx01 cache01 in
                        match uu___6 with
                        | Success ((x1, g12), cache11) ->
                            let uu___7 =
                              let uu___8 uu___9 cache =
                                Success
                                  (((eff, t), FStar_Pervasives_Native.None),
                                    cache) in
                              uu___8 ctx01 cache11 in
                            (match uu___7 with
                             | Success ((y, g2), cache2) ->
                                 let uu___8 =
                                   let uu___9 =
                                     let uu___10 = and_pre g12 g2 in
                                     (y, uu___10) in
                                   (uu___9, cache2) in
                                 Success uu___8
                             | err -> err)
                        | Error err -> Error err)) in
          uu___3 ctx0 cache1 in
        (match uu___2 with
         | Success ((y, g2), cache2) ->
             let uu___3 =
               let uu___4 = let uu___5 = and_pre g11 g2 in (y, uu___5) in
               (uu___4, cache2) in
             Success uu___3
         | err -> err)
    | Error err -> Error err
let simplify_steps : FStarC_TypeChecker_Env.step Prims.list=
  [FStarC_TypeChecker_Env.Beta;
  FStarC_TypeChecker_Env.UnfoldUntil FStarC_Syntax_Syntax.delta_constant;
  FStarC_TypeChecker_Env.UnfoldQual ["unfold"];
  FStarC_TypeChecker_Env.UnfoldOnly
    [FStarC_Parser_Const.pure_wp_monotonic_lid;
    FStarC_Parser_Const.pure_wp_monotonic0_lid];
  FStarC_TypeChecker_Env.Simplify;
  FStarC_TypeChecker_Env.Primops;
  FStarC_TypeChecker_Env.NoFullNorm]
let initial_cache : cache_t=
  let uu___ = FStarC_Syntax_Hash.term_map_empty () in
  let uu___1 = FStarC_Syntax_Hash.term_map_empty () in
  { term_map = uu___; guard_map = uu___1 }
let check_term_top (g : FStarC_TypeChecker_Env.env)
  (e : FStarC_Syntax_Syntax.term)
  (topt : FStarC_Syntax_Syntax.typ FStar_Pervasives_Native.option)
  (must_tot : Prims.bool) :
  ((tot_or_ghost * FStarC_Syntax_Syntax.typ) * precondition) __result=
  (let uu___1 = FStarC_Effect.op_Bang dbg_Eq in
   if uu___1
   then
     let uu___2 =
       let uu___3 = get_goal_ctr () in
       FStarC_Class_Show.show FStarC_Class_Show.showable_int uu___3 in
     FStarC_Format.print1 "(%s) Entering core ... \n" uu___2
   else ());
  (let uu___2 =
     (FStarC_Effect.op_Bang dbg) || (FStarC_Effect.op_Bang dbg_Top) in
   if uu___2
   then
     let uu___3 =
       let uu___4 = get_goal_ctr () in
       FStarC_Class_Show.show FStarC_Class_Show.showable_int uu___4 in
     let uu___4 = FStarC_Class_Show.show FStarC_Syntax_Print.showable_term e in
     let uu___5 =
       FStarC_Class_Show.show
         (FStarC_Class_Show.show_option FStarC_Syntax_Print.showable_term)
         topt in
     FStarC_Format.print3 "(%s) Entering core with %s <: %s\n" uu___3 uu___4
       uu___5
   else ());
  FStarC_Syntax_TermHashTable.reset_counters table.table;
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
          let uu___5 = check_term_top' g e topt must_tot in
          uu___5 ctx initial_cache) FStar_Pervasives_Native.None
       "FStarC.TypeChecker.Core.check_term_top" in
   (let uu___5 =
      (FStarC_Effect.op_Bang dbg) || (FStarC_Effect.op_Bang dbg_Top) in
    if uu___5
    then
      let uu___6 =
        let uu___7 = get_goal_ctr () in
        FStarC_Class_Show.show FStarC_Class_Show.showable_int uu___7 in
      let uu___7 =
        FStarC_Class_Show.show
          (showable_result
             (FStarC_Class_Show.show_tuple2
                (FStarC_Class_Show.show_tuple2 showable_tot_or_ghost
                   FStarC_Syntax_Print.showable_term)
                (FStarC_Class_Show.show_option
                   FStarC_Syntax_Print.showable_term))) res in
      FStarC_Format.print2 "(%s) Core result = %s\n" uu___6 uu___7
    else ());
   (let res1 =
      match res with
      | Success ((et, FStar_Pervasives_Native.Some guard0), cache) ->
          let guard1 =
            FStarC_TypeChecker_Normalize.normalize simplify_steps g guard0 in
          ((let uu___6 =
              ((FStarC_Effect.op_Bang dbg) || (FStarC_Effect.op_Bang dbg_Top))
                || (FStarC_Effect.op_Bang dbg_Exit) in
            if uu___6
            then
              ((let uu___8 =
                  let uu___9 = get_goal_ctr () in
                  FStarC_Class_Show.show FStarC_Class_Show.showable_int
                    uu___9 in
                let uu___9 =
                  FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                    guard0 in
                let uu___10 =
                  FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                    guard1 in
                FStarC_Format.print3
                  "(%s) Exiting core: Simplified guard from {{%s}} to {{%s}}\n"
                  uu___8 uu___9 uu___10);
               (let guard_names =
                  let uu___8 = FStarC_Syntax_Free.names guard1 in
                  FStarC_Class_Setlike.elems ()
                    (Obj.magic
                       (FStarC_FlatSet.setlike_flat_set
                          FStarC_Syntax_Syntax.ord_bv)) (Obj.magic uu___8) in
                let uu___8 =
                  FStarC_List.tryFind
                    (fun bv ->
                       FStarC_List.for_all
                         (fun binding_env ->
                            match binding_env with
                            | FStarC_Syntax_Syntax.Binding_var bv_env ->
                                let uu___9 =
                                  FStarC_Syntax_Syntax.bv_eq bv_env bv in
                                Prims.op_Negation uu___9
                            | uu___9 -> true) g.FStarC_TypeChecker_Env.gamma)
                    guard_names in
                match uu___8 with
                | FStar_Pervasives_Native.Some bv ->
                    let uu___9 =
                      let uu___10 = FStarC_Syntax_Syntax.bv_to_name bv in
                      FStarC_Class_Show.show
                        FStarC_Syntax_Print.showable_term uu___10 in
                    FStarC_Format.print1
                      "WARNING: %s is free in the core generated guard\n"
                      uu___9
                | uu___9 -> ()))
            else ());
           Success ((et, (FStar_Pervasives_Native.Some guard1)), cache))
      | Success uu___5 ->
          ((let uu___7 =
              (FStarC_Effect.op_Bang dbg) || (FStarC_Effect.op_Bang dbg_Top) in
            if uu___7
            then
              let uu___8 =
                let uu___9 = get_goal_ctr () in
                FStarC_Class_Show.show FStarC_Class_Show.showable_int uu___9 in
              FStarC_Format.print1 "(%s) Exiting core (ok)\n" uu___8
            else ());
           res)
      | Error uu___5 ->
          ((let uu___7 =
              (FStarC_Effect.op_Bang dbg) || (FStarC_Effect.op_Bang dbg_Top) in
            if uu___7
            then
              let uu___8 =
                let uu___9 = get_goal_ctr () in
                FStarC_Class_Show.show FStarC_Class_Show.showable_int uu___9 in
              FStarC_Format.print1 "(%s) Exiting core (failed)\n" uu___8
            else ());
           res) in
    (let uu___6 = FStarC_Effect.op_Bang dbg_Eq in
     if uu___6
     then
       (FStarC_Syntax_TermHashTable.print_stats table.table;
        (let cs = report_cache_stats () in
         let uu___8 =
           FStarC_Class_Show.show FStarC_Class_Show.showable_int cs.hits in
         let uu___9 =
           FStarC_Class_Show.show FStarC_Class_Show.showable_int cs.misses in
         FStarC_Format.print2 "Cache_stats { hits = %s; misses = %s }\n"
           uu___8 uu___9))
     else ());
    res1))
let return_my_guard_and_tok_t (g : precondition) (cache : cache_t) :
  (FStarC_Syntax_Syntax.typ * (unit -> unit)) FStar_Pervasives_Native.option=
  let tok = mk_token cache in
  match g with
  | FStar_Pervasives_Native.None ->
      (commit_guard_core tok; FStar_Pervasives_Native.None)
  | FStar_Pervasives_Native.Some guard1 ->
      FStar_Pervasives_Native.Some
        (guard1, ((fun uu___ -> commit_guard_core tok)))
let check_term (g : FStarC_TypeChecker_Env.env)
  (e : FStarC_Syntax_Syntax.term) (t : FStarC_Syntax_Syntax.typ)
  (must_tot : Prims.bool) :
  (guard_and_tok_t FStar_Pervasives_Native.option, error)
    FStar_Pervasives.either=
  let uu___ = check_term_top g e (FStar_Pervasives_Native.Some t) must_tot in
  match uu___ with
  | Success ((uu___1, g1), cache) ->
      let uu___2 = return_my_guard_and_tok_t g1 cache in
      FStar_Pervasives.Inl uu___2
  | Error err -> FStar_Pervasives.Inr err
let check_term_at_type (g : FStarC_TypeChecker_Env.env)
  (e : FStarC_Syntax_Syntax.term) (t : FStarC_Syntax_Syntax.typ) :
  ((tot_or_ghost * guard_and_tok_t FStar_Pervasives_Native.option), error)
    FStar_Pervasives.either=
  let must_tot = false in
  let uu___ = check_term_top g e (FStar_Pervasives_Native.Some t) must_tot in
  match uu___ with
  | Success (((eff, uu___1), g1), cache) ->
      let uu___2 =
        let uu___3 = return_my_guard_and_tok_t g1 cache in (eff, uu___3) in
      FStar_Pervasives.Inl uu___2
  | Error err -> FStar_Pervasives.Inr err
let compute_term_type (g : FStarC_TypeChecker_Env.env)
  (e : FStarC_Syntax_Syntax.term) :
  ((tot_or_ghost * FStarC_Syntax_Syntax.typ * guard_and_tok_t
     FStar_Pervasives_Native.option),
    error) FStar_Pervasives.either=
  let must_tot = false in
  let uu___ = check_term_top g e FStar_Pervasives_Native.None must_tot in
  match uu___ with
  | Success (((eff, ty), g1), cache) ->
      let uu___1 =
        let uu___2 = return_my_guard_and_tok_t g1 cache in (eff, ty, uu___2) in
      FStar_Pervasives.Inl uu___1
  | Error err -> FStar_Pervasives.Inr err
let open_binders_in_term (env1 : FStarC_TypeChecker_Env.env)
  (bs : FStarC_Syntax_Syntax.binders) (t : FStarC_Syntax_Syntax.term) :
  (FStarC_TypeChecker_Env.env * FStarC_Syntax_Syntax.binders *
    FStarC_Syntax_Syntax.term)=
  let g = initial_env env1 in
  let uu___ = open_term_binders g bs t in
  match uu___ with | (g', bs1, t1) -> ((g'.tcenv), bs1, t1)
let open_binders_in_comp (env1 : FStarC_TypeChecker_Env.env)
  (bs : FStarC_Syntax_Syntax.binders) (c : FStarC_Syntax_Syntax.comp) :
  (FStarC_TypeChecker_Env.env * FStarC_Syntax_Syntax.binders *
    FStarC_Syntax_Syntax.comp)=
  let g = initial_env env1 in
  let uu___ = open_comp_binders g bs c in
  match uu___ with | (g', bs1, c1) -> ((g'.tcenv), bs1, c1)
let check_term_equality (guard_ok : Prims.bool) (unfolding_ok1 : Prims.bool)
  (g : FStarC_TypeChecker_Env.env) (t0 : FStarC_Syntax_Syntax.typ)
  (t1 : FStarC_Syntax_Syntax.typ) :
  (guard_and_tok_t FStar_Pervasives_Native.option, error)
    FStar_Pervasives.either=
  let g1 = initial_env g in
  (let uu___1 = FStarC_Effect.op_Bang dbg_Top in
   if uu___1
   then
     let uu___2 = FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t0 in
     let uu___3 = FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t1 in
     let uu___4 =
       FStarC_Class_Show.show FStarC_Class_Show.showable_bool guard_ok in
     let uu___5 =
       FStarC_Class_Show.show FStarC_Class_Show.showable_bool unfolding_ok1 in
     FStarC_Format.print4
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
     let uu___1 = check_relation g1 EQUALITY t0 t1 in
     uu___1 ctx initial_cache in
   (let uu___2 = FStarC_Effect.op_Bang dbg_Top in
    if uu___2
    then
      let uu___3 =
        FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t0 in
      let uu___4 =
        FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t1 in
      let uu___5 =
        FStarC_Class_Show.show
          (showable_result
             (FStarC_Class_Show.show_tuple2 FStarC_Class_Show.showable_unit
                (FStarC_Class_Show.show_option
                   FStarC_Syntax_Print.showable_term))) r in
      FStarC_Format.print3
        "} Exiting check_term_equality (%s, %s). Result = %s.\n" uu___3
        uu___4 uu___5
    else ());
   (let r1 =
      match r with
      | Success ((uu___2, g2), cache) ->
          let uu___3 = return_my_guard_and_tok_t g2 cache in
          FStar_Pervasives.Inl uu___3
      | Error err -> FStar_Pervasives.Inr err in
    r1))
let check_term_subtyping (guard_ok : Prims.bool) (unfolding_ok1 : Prims.bool)
  (g : FStarC_TypeChecker_Env.env) (t0 : FStarC_Syntax_Syntax.typ)
  (t1 : FStarC_Syntax_Syntax.typ) :
  (guard_and_tok_t FStar_Pervasives_Native.option, error)
    FStar_Pervasives.either=
  let g1 = initial_env g in
  let ctx =
    {
      no_guard = (Prims.op_Negation guard_ok);
      unfolding_ok = unfolding_ok1;
      error_context = [("Subtyping", FStar_Pervasives_Native.None)]
    } in
  let uu___ =
    let uu___1 =
      check_relation g1 (SUBTYPING FStar_Pervasives_Native.None) t0 t1 in
    uu___1 ctx initial_cache in
  match uu___ with
  | Success ((uu___1, g2), cache) ->
      let uu___2 = return_my_guard_and_tok_t g2 cache in
      FStar_Pervasives.Inl uu___2
  | Error err -> FStar_Pervasives.Inr err
