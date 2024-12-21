open Prims
let (dbg_PartialApp : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "PartialApp"
let (dbg_SMTEncoding : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "SMTEncoding"
let (dbg_SMTEncodingReify : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "SMTEncodingReify"
let mkForall_fuel' :
  'uuuuu .
    Prims.string ->
      FStarC_Compiler_Range_Type.range ->
        'uuuuu ->
          (FStarC_SMTEncoding_Term.pat Prims.list Prims.list *
            FStarC_SMTEncoding_Term.fvs * FStarC_SMTEncoding_Term.term) ->
            FStarC_SMTEncoding_Term.term
  =
  fun mname ->
    fun r ->
      fun n ->
        fun uu___ ->
          match uu___ with
          | (pats, vars, body) ->
              let fallback uu___1 =
                FStarC_SMTEncoding_Term.mkForall r (pats, vars, body) in
              let uu___1 = FStarC_Options.unthrottle_inductives () in
              if uu___1
              then fallback ()
              else
                (let uu___3 =
                   FStarC_SMTEncoding_Env.fresh_fvar mname "f"
                     FStarC_SMTEncoding_Term.Fuel_sort in
                 match uu___3 with
                 | (fsym, fterm) ->
                     let add_fuel tms =
                       FStarC_Compiler_List.map
                         (fun p ->
                            match p.FStarC_SMTEncoding_Term.tm with
                            | FStarC_SMTEncoding_Term.App
                                (FStarC_SMTEncoding_Term.Var "HasType", args)
                                ->
                                FStarC_SMTEncoding_Util.mkApp
                                  ("HasTypeFuel", (fterm :: args))
                            | uu___4 -> p) tms in
                     let pats1 = FStarC_Compiler_List.map add_fuel pats in
                     let body1 =
                       match body.FStarC_SMTEncoding_Term.tm with
                       | FStarC_SMTEncoding_Term.App
                           (FStarC_SMTEncoding_Term.Imp, guard::body'::[]) ->
                           let guard1 =
                             match guard.FStarC_SMTEncoding_Term.tm with
                             | FStarC_SMTEncoding_Term.App
                                 (FStarC_SMTEncoding_Term.And, guards) ->
                                 let uu___4 = add_fuel guards in
                                 FStarC_SMTEncoding_Util.mk_and_l uu___4
                             | uu___4 ->
                                 let uu___5 = add_fuel [guard] in
                                 FStarC_Compiler_List.hd uu___5 in
                           FStarC_SMTEncoding_Util.mkImp (guard1, body')
                       | uu___4 -> body in
                     let vars1 =
                       let uu___4 =
                         FStarC_SMTEncoding_Term.mk_fv
                           (fsym, FStarC_SMTEncoding_Term.Fuel_sort) in
                       uu___4 :: vars in
                     FStarC_SMTEncoding_Term.mkForall r (pats1, vars1, body1))
let (mkForall_fuel :
  Prims.string ->
    FStarC_Compiler_Range_Type.range ->
      (FStarC_SMTEncoding_Term.pat Prims.list Prims.list *
        FStarC_SMTEncoding_Term.fvs * FStarC_SMTEncoding_Term.term) ->
        FStarC_SMTEncoding_Term.term)
  = fun mname -> fun r -> mkForall_fuel' mname r Prims.int_one
let (head_normal :
  FStarC_SMTEncoding_Env.env_t -> FStarC_Syntax_Syntax.term -> Prims.bool) =
  fun env ->
    fun t ->
      let t1 = FStarC_Syntax_Util.unmeta t in
      match t1.FStarC_Syntax_Syntax.n with
      | FStarC_Syntax_Syntax.Tm_arrow uu___ -> true
      | FStarC_Syntax_Syntax.Tm_refine uu___ -> true
      | FStarC_Syntax_Syntax.Tm_bvar uu___ -> true
      | FStarC_Syntax_Syntax.Tm_uvar uu___ -> true
      | FStarC_Syntax_Syntax.Tm_abs uu___ -> true
      | FStarC_Syntax_Syntax.Tm_constant uu___ -> true
      | FStarC_Syntax_Syntax.Tm_fvar fv ->
          let uu___ =
            FStarC_TypeChecker_Env.lookup_definition
              [FStarC_TypeChecker_Env.Eager_unfolding_only]
              env.FStarC_SMTEncoding_Env.tcenv
              (fv.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v in
          FStarC_Compiler_Option.isNone uu___
      | FStarC_Syntax_Syntax.Tm_app
          {
            FStarC_Syntax_Syntax.hd =
              { FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_fvar fv;
                FStarC_Syntax_Syntax.pos = uu___;
                FStarC_Syntax_Syntax.vars = uu___1;
                FStarC_Syntax_Syntax.hash_code = uu___2;_};
            FStarC_Syntax_Syntax.args = uu___3;_}
          ->
          let uu___4 =
            FStarC_TypeChecker_Env.lookup_definition
              [FStarC_TypeChecker_Env.Eager_unfolding_only]
              env.FStarC_SMTEncoding_Env.tcenv
              (fv.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v in
          FStarC_Compiler_Option.isNone uu___4
      | uu___ -> false
let (head_redex :
  FStarC_SMTEncoding_Env.env_t -> FStarC_Syntax_Syntax.term -> Prims.bool) =
  fun env ->
    fun t ->
      let uu___ =
        let uu___1 = FStarC_Syntax_Util.un_uinst t in
        uu___1.FStarC_Syntax_Syntax.n in
      match uu___ with
      | FStarC_Syntax_Syntax.Tm_abs
          { FStarC_Syntax_Syntax.bs = uu___1;
            FStarC_Syntax_Syntax.body = uu___2;
            FStarC_Syntax_Syntax.rc_opt = FStar_Pervasives_Native.Some rc;_}
          ->
          ((FStarC_Ident.lid_equals rc.FStarC_Syntax_Syntax.residual_effect
              FStarC_Parser_Const.effect_Tot_lid)
             ||
             (FStarC_Ident.lid_equals rc.FStarC_Syntax_Syntax.residual_effect
                FStarC_Parser_Const.effect_GTot_lid))
            ||
            (FStarC_Compiler_List.existsb
               (fun uu___3 ->
                  match uu___3 with
                  | FStarC_Syntax_Syntax.TOTAL -> true
                  | uu___4 -> false) rc.FStarC_Syntax_Syntax.residual_flags)
      | FStarC_Syntax_Syntax.Tm_fvar fv ->
          let uu___1 =
            FStarC_TypeChecker_Env.lookup_definition
              [FStarC_TypeChecker_Env.Eager_unfolding_only]
              env.FStarC_SMTEncoding_Env.tcenv
              (fv.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v in
          FStarC_Compiler_Option.isSome uu___1
      | uu___1 -> false
let (norm_with_steps :
  FStarC_TypeChecker_Env.steps ->
    FStarC_TypeChecker_Env.env ->
      FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  =
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
          uu___ "FStarC.SMTEncoding.EncodeTerm.norm_with_steps"
let (normalize_refinement :
  FStarC_TypeChecker_Env.steps ->
    FStarC_TypeChecker_Env.env ->
      FStarC_Syntax_Syntax.typ -> FStarC_Syntax_Syntax.typ)
  =
  fun steps ->
    fun env ->
      fun t ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStarC_TypeChecker_Env.current_module env in
            FStarC_Ident.string_of_lid uu___2 in
          FStar_Pervasives_Native.Some uu___1 in
        FStarC_Profiling.profile
          (fun uu___1 ->
             FStarC_TypeChecker_Normalize.normalize_refinement steps env t)
          uu___ "FStarC.SMTEncoding.EncodeTerm.normalize_refinement"
let (whnf :
  FStarC_SMTEncoding_Env.env_t ->
    FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  =
  fun env ->
    fun t ->
      let uu___ = head_normal env t in
      if uu___
      then t
      else
        norm_with_steps
          [FStarC_TypeChecker_Env.Beta;
          FStarC_TypeChecker_Env.Weak;
          FStarC_TypeChecker_Env.HNF;
          FStarC_TypeChecker_Env.Exclude FStarC_TypeChecker_Env.Zeta;
          FStarC_TypeChecker_Env.Eager_unfolding;
          FStarC_TypeChecker_Env.EraseUniverses]
          env.FStarC_SMTEncoding_Env.tcenv t
let (norm :
  FStarC_SMTEncoding_Env.env_t ->
    FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  =
  fun env ->
    fun t ->
      norm_with_steps
        [FStarC_TypeChecker_Env.Beta;
        FStarC_TypeChecker_Env.Exclude FStarC_TypeChecker_Env.Zeta;
        FStarC_TypeChecker_Env.Eager_unfolding;
        FStarC_TypeChecker_Env.EraseUniverses]
        env.FStarC_SMTEncoding_Env.tcenv t
let (maybe_whnf :
  FStarC_SMTEncoding_Env.env_t ->
    FStarC_Syntax_Syntax.term ->
      FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t ->
      let t' = whnf env t in
      let uu___ = FStarC_Syntax_Util.head_and_args t' in
      match uu___ with
      | (head', uu___1) ->
          let uu___2 = head_redex env head' in
          if uu___2
          then FStar_Pervasives_Native.None
          else FStar_Pervasives_Native.Some t'
let (trivial_post : FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term) =
  fun t ->
    let uu___ = let uu___1 = FStarC_Syntax_Syntax.null_binder t in [uu___1] in
    let uu___1 =
      FStarC_Syntax_Syntax.fvar FStarC_Parser_Const.true_lid
        FStar_Pervasives_Native.None in
    FStarC_Syntax_Util.abs uu___ uu___1 FStar_Pervasives_Native.None
let (mk_Apply :
  FStarC_SMTEncoding_Term.term ->
    FStarC_SMTEncoding_Term.fvs -> FStarC_SMTEncoding_Term.term)
  =
  fun e ->
    fun vars ->
      FStarC_Compiler_List.fold_left
        (fun out ->
           fun var ->
             let uu___ = FStarC_SMTEncoding_Term.fv_sort var in
             match uu___ with
             | FStarC_SMTEncoding_Term.Fuel_sort ->
                 let uu___1 = FStarC_SMTEncoding_Util.mkFreeV var in
                 FStarC_SMTEncoding_Term.mk_ApplyTF out uu___1
             | s ->
                 let uu___1 = FStarC_SMTEncoding_Util.mkFreeV var in
                 FStarC_SMTEncoding_Util.mk_ApplyTT out uu___1) e vars
let (mk_Apply_args :
  FStarC_SMTEncoding_Term.term ->
    FStarC_SMTEncoding_Term.term Prims.list -> FStarC_SMTEncoding_Term.term)
  =
  fun e ->
    fun args ->
      FStarC_Compiler_List.fold_left FStarC_SMTEncoding_Util.mk_ApplyTT e
        args
let raise_arity_mismatch :
  'a .
    Prims.string ->
      Prims.int -> Prims.int -> FStarC_Compiler_Range_Type.range -> 'a
  =
  fun head ->
    fun arity ->
      fun n_args ->
        fun rng ->
          let uu___ =
            let uu___1 =
              FStarC_Class_Show.show FStarC_Class_Show.showable_int arity in
            let uu___2 =
              FStarC_Class_Show.show FStarC_Class_Show.showable_int n_args in
            FStarC_Compiler_Util.format3
              "Head symbol %s expects at least %s arguments; got only %s"
              head uu___1 uu___2 in
          FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range rng
            FStarC_Errors_Codes.Fatal_SMTEncodingArityMismatch ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___)
let (isTotFun_axioms :
  FStarC_Compiler_Range_Type.range ->
    FStarC_SMTEncoding_Term.term ->
      FStarC_SMTEncoding_Term.fvs ->
        FStarC_SMTEncoding_Term.term Prims.list ->
          Prims.bool -> FStarC_SMTEncoding_Term.term)
  =
  fun pos ->
    fun head ->
      fun vars ->
        fun guards ->
          fun is_pure ->
            let maybe_mkForall pat vars1 body =
              match vars1 with
              | [] -> body
              | uu___ ->
                  FStarC_SMTEncoding_Term.mkForall pos (pat, vars1, body) in
            let rec is_tot_fun_axioms ctx ctx_guard head1 vars1 guards1 =
              match (vars1, guards1) with
              | ([], []) -> FStarC_SMTEncoding_Util.mkTrue
              | (uu___::[], uu___1) ->
                  if is_pure
                  then
                    let uu___2 =
                      let uu___3 =
                        let uu___4 =
                          FStarC_SMTEncoding_Term.mk_IsTotFun head1 in
                        (ctx_guard, uu___4) in
                      FStarC_SMTEncoding_Util.mkImp uu___3 in
                    maybe_mkForall [[head1]] ctx uu___2
                  else FStarC_SMTEncoding_Util.mkTrue
              | (x::vars2, g_x::guards2) ->
                  let is_tot_fun_head =
                    let uu___ =
                      let uu___1 =
                        let uu___2 =
                          FStarC_SMTEncoding_Term.mk_IsTotFun head1 in
                        (ctx_guard, uu___2) in
                      FStarC_SMTEncoding_Util.mkImp uu___1 in
                    maybe_mkForall [[head1]] ctx uu___ in
                  let app = mk_Apply head1 [x] in
                  let ctx1 = FStarC_Compiler_List.op_At ctx [x] in
                  let ctx_guard1 =
                    FStarC_SMTEncoding_Util.mkAnd (ctx_guard, g_x) in
                  let rest =
                    is_tot_fun_axioms ctx1 ctx_guard1 app vars2 guards2 in
                  FStarC_SMTEncoding_Util.mkAnd (is_tot_fun_head, rest)
              | uu___ -> failwith "impossible: isTotFun_axioms" in
            is_tot_fun_axioms [] FStarC_SMTEncoding_Util.mkTrue head vars
              guards
let (maybe_curry_app :
  FStarC_Compiler_Range_Type.range ->
    (FStarC_SMTEncoding_Term.op, FStarC_SMTEncoding_Term.term)
      FStar_Pervasives.either ->
      Prims.int ->
        FStarC_SMTEncoding_Term.term Prims.list ->
          FStarC_SMTEncoding_Term.term)
  =
  fun rng ->
    fun head ->
      fun arity ->
        fun args ->
          let n_args = FStarC_Compiler_List.length args in
          match head with
          | FStar_Pervasives.Inr head1 -> mk_Apply_args head1 args
          | FStar_Pervasives.Inl head1 ->
              if n_args = arity
              then FStarC_SMTEncoding_Util.mkApp' (head1, args)
              else
                if n_args > arity
                then
                  (let uu___1 = FStarC_Compiler_Util.first_N arity args in
                   match uu___1 with
                   | (args1, rest) ->
                       let head2 =
                         FStarC_SMTEncoding_Util.mkApp' (head1, args1) in
                       mk_Apply_args head2 rest)
                else
                  (let uu___2 = FStarC_SMTEncoding_Term.op_to_string head1 in
                   raise_arity_mismatch uu___2 arity n_args rng)
let (maybe_curry_fvb :
  FStarC_Compiler_Range_Type.range ->
    FStarC_SMTEncoding_Env.fvar_binding ->
      FStarC_SMTEncoding_Term.term Prims.list -> FStarC_SMTEncoding_Term.term)
  =
  fun rng ->
    fun fvb ->
      fun args ->
        if fvb.FStarC_SMTEncoding_Env.fvb_thunked
        then
          let uu___ = FStarC_SMTEncoding_Env.force_thunk fvb in
          mk_Apply_args uu___ args
        else
          maybe_curry_app rng
            (FStar_Pervasives.Inl
               (FStarC_SMTEncoding_Term.Var
                  (fvb.FStarC_SMTEncoding_Env.smt_id)))
            fvb.FStarC_SMTEncoding_Env.smt_arity args
let (is_app : FStarC_SMTEncoding_Term.op -> Prims.bool) =
  fun uu___ ->
    match uu___ with
    | FStarC_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStarC_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu___1 -> false
let check_pattern_vars :
  'uuuuu .
    FStarC_SMTEncoding_Env.env_t ->
      FStarC_Syntax_Syntax.binder Prims.list ->
        (FStarC_Syntax_Syntax.term * 'uuuuu) Prims.list -> unit
  =
  fun env ->
    fun vars ->
      fun pats ->
        let pats1 =
          FStarC_Compiler_List.map
            (fun uu___ ->
               match uu___ with
               | (x, uu___1) ->
                   norm_with_steps
                     [FStarC_TypeChecker_Env.Beta;
                     FStarC_TypeChecker_Env.AllowUnboundUniverses;
                     FStarC_TypeChecker_Env.EraseUniverses]
                     env.FStarC_SMTEncoding_Env.tcenv x) pats in
        match pats1 with
        | [] -> ()
        | hd::tl ->
            let pat_vars =
              let uu___ = FStarC_Syntax_Free.names hd in
              FStarC_Compiler_List.fold_left
                (fun uu___2 ->
                   fun uu___1 ->
                     (fun out ->
                        fun x ->
                          let uu___1 = FStarC_Syntax_Free.names x in
                          Obj.magic
                            (FStarC_Class_Setlike.union ()
                               (Obj.magic
                                  (FStarC_Compiler_FlatSet.setlike_flat_set
                                     FStarC_Syntax_Syntax.ord_bv))
                               (Obj.magic out) (Obj.magic uu___1))) uu___2
                       uu___1) uu___ tl in
            let uu___ =
              FStarC_Compiler_Util.find_opt
                (fun uu___1 ->
                   match uu___1 with
                   | { FStarC_Syntax_Syntax.binder_bv = b;
                       FStarC_Syntax_Syntax.binder_qual = uu___2;
                       FStarC_Syntax_Syntax.binder_positivity = uu___3;
                       FStarC_Syntax_Syntax.binder_attrs = uu___4;_} ->
                       let uu___5 =
                         FStarC_Class_Setlike.mem ()
                           (Obj.magic
                              (FStarC_Compiler_FlatSet.setlike_flat_set
                                 FStarC_Syntax_Syntax.ord_bv)) b
                           (Obj.magic pat_vars) in
                       Prims.op_Negation uu___5) vars in
            (match uu___ with
             | FStar_Pervasives_Native.None -> ()
             | FStar_Pervasives_Native.Some
                 { FStarC_Syntax_Syntax.binder_bv = x;
                   FStarC_Syntax_Syntax.binder_qual = uu___1;
                   FStarC_Syntax_Syntax.binder_positivity = uu___2;
                   FStarC_Syntax_Syntax.binder_attrs = uu___3;_}
                 ->
                 let pos =
                   FStarC_Compiler_List.fold_left
                     (fun out ->
                        fun t ->
                          FStarC_Compiler_Range_Ops.union_ranges out
                            t.FStarC_Syntax_Syntax.pos)
                     hd.FStarC_Syntax_Syntax.pos tl in
                 let uu___4 =
                   let uu___5 =
                     FStarC_Class_Show.show FStarC_Syntax_Print.showable_bv x in
                   FStarC_Compiler_Util.format1
                     "SMT pattern misses at least one bound variable: %s"
                     uu___5 in
                 FStarC_Errors.log_issue FStarC_Class_HasRange.hasRange_range
                   pos FStarC_Errors_Codes.Warning_SMTPatternIllFormed ()
                   (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                   (Obj.magic uu___4))
type label =
  (FStarC_SMTEncoding_Term.fv * Prims.string *
    FStarC_Compiler_Range_Type.range)
type labels = label Prims.list
type pattern =
  {
  pat_vars: (FStarC_Syntax_Syntax.bv * FStarC_SMTEncoding_Term.fv) Prims.list ;
  pat_term:
    unit -> (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.decls_t) ;
  guard: FStarC_SMTEncoding_Term.term -> FStarC_SMTEncoding_Term.term ;
  projections:
    FStarC_SMTEncoding_Term.term ->
      (FStarC_Syntax_Syntax.bv * FStarC_SMTEncoding_Term.term) Prims.list
    }
let (__proj__Mkpattern__item__pat_vars :
  pattern ->
    (FStarC_Syntax_Syntax.bv * FStarC_SMTEncoding_Term.fv) Prims.list)
  =
  fun projectee ->
    match projectee with
    | { pat_vars; pat_term; guard; projections;_} -> pat_vars
let (__proj__Mkpattern__item__pat_term :
  pattern ->
    unit -> (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.decls_t))
  =
  fun projectee ->
    match projectee with
    | { pat_vars; pat_term; guard; projections;_} -> pat_term
let (__proj__Mkpattern__item__guard :
  pattern -> FStarC_SMTEncoding_Term.term -> FStarC_SMTEncoding_Term.term) =
  fun projectee ->
    match projectee with
    | { pat_vars; pat_term; guard; projections;_} -> guard
let (__proj__Mkpattern__item__projections :
  pattern ->
    FStarC_SMTEncoding_Term.term ->
      (FStarC_Syntax_Syntax.bv * FStarC_SMTEncoding_Term.term) Prims.list)
  =
  fun projectee ->
    match projectee with
    | { pat_vars; pat_term; guard; projections;_} -> projections
let (as_function_typ :
  FStarC_SMTEncoding_Env.env_t ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
      FStarC_Syntax_Syntax.term)
  =
  fun env ->
    fun t0 ->
      let rec aux norm1 t =
        let t1 = FStarC_Syntax_Subst.compress t in
        match t1.FStarC_Syntax_Syntax.n with
        | FStarC_Syntax_Syntax.Tm_arrow uu___ -> t1
        | FStarC_Syntax_Syntax.Tm_refine uu___ ->
            let uu___1 = FStarC_Syntax_Util.unrefine t1 in aux true uu___1
        | uu___ ->
            if norm1
            then let uu___1 = whnf env t1 in aux false uu___1
            else
              (let uu___2 =
                 let uu___3 =
                   FStarC_Compiler_Range_Ops.string_of_range
                     t0.FStarC_Syntax_Syntax.pos in
                 let uu___4 =
                   FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                     t0 in
                 FStarC_Compiler_Util.format2
                   "(%s) Expected a function typ; got %s" uu___3 uu___4 in
               failwith uu___2) in
      aux true t0
let rec (curried_arrow_formals_comp :
  FStarC_Syntax_Syntax.term ->
    (FStarC_Syntax_Syntax.binders * FStarC_Syntax_Syntax.comp))
  =
  fun k ->
    let k1 = FStarC_Syntax_Subst.compress k in
    match k1.FStarC_Syntax_Syntax.n with
    | FStarC_Syntax_Syntax.Tm_arrow
        { FStarC_Syntax_Syntax.bs1 = bs; FStarC_Syntax_Syntax.comp = c;_} ->
        FStarC_Syntax_Subst.open_comp bs c
    | FStarC_Syntax_Syntax.Tm_refine
        { FStarC_Syntax_Syntax.b = bv; FStarC_Syntax_Syntax.phi = uu___;_} ->
        let uu___1 = curried_arrow_formals_comp bv.FStarC_Syntax_Syntax.sort in
        (match uu___1 with
         | (args, res) ->
             (match args with
              | [] ->
                  let uu___2 = FStarC_Syntax_Syntax.mk_Total k1 in
                  ([], uu___2)
              | uu___2 -> (args, res)))
    | uu___ -> let uu___1 = FStarC_Syntax_Syntax.mk_Total k1 in ([], uu___1)
let is_arithmetic_primitive :
  'uuuuu .
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
      'uuuuu Prims.list -> Prims.bool
  =
  fun head ->
    fun args ->
      match ((head.FStarC_Syntax_Syntax.n), args) with
      | (FStarC_Syntax_Syntax.Tm_fvar fv, uu___::uu___1::[]) ->
          ((((((((((((FStarC_Syntax_Syntax.fv_eq_lid fv
                        FStarC_Parser_Const.op_Addition)
                       ||
                       (FStarC_Syntax_Syntax.fv_eq_lid fv
                          FStarC_Parser_Const.op_Subtraction))
                      ||
                      (FStarC_Syntax_Syntax.fv_eq_lid fv
                         FStarC_Parser_Const.op_Multiply))
                     ||
                     (FStarC_Syntax_Syntax.fv_eq_lid fv
                        FStarC_Parser_Const.op_Division))
                    ||
                    (FStarC_Syntax_Syntax.fv_eq_lid fv
                       FStarC_Parser_Const.op_Modulus))
                   ||
                   (FStarC_Syntax_Syntax.fv_eq_lid fv
                      FStarC_Parser_Const.real_op_LT))
                  ||
                  (FStarC_Syntax_Syntax.fv_eq_lid fv
                     FStarC_Parser_Const.real_op_LTE))
                 ||
                 (FStarC_Syntax_Syntax.fv_eq_lid fv
                    FStarC_Parser_Const.real_op_GT))
                ||
                (FStarC_Syntax_Syntax.fv_eq_lid fv
                   FStarC_Parser_Const.real_op_GTE))
               ||
               (FStarC_Syntax_Syntax.fv_eq_lid fv
                  FStarC_Parser_Const.real_op_Addition))
              ||
              (FStarC_Syntax_Syntax.fv_eq_lid fv
                 FStarC_Parser_Const.real_op_Subtraction))
             ||
             (FStarC_Syntax_Syntax.fv_eq_lid fv
                FStarC_Parser_Const.real_op_Multiply))
            ||
            (FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Parser_Const.real_op_Division)
      | (FStarC_Syntax_Syntax.Tm_fvar fv, uu___::[]) ->
          FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.op_Minus
      | uu___ -> false
let (isInteger : FStarC_Syntax_Syntax.term' -> Prims.bool) =
  fun tm ->
    match tm with
    | FStarC_Syntax_Syntax.Tm_constant (FStarC_Const.Const_int
        (n, FStar_Pervasives_Native.None)) -> true
    | uu___ -> false
let (getInteger : FStarC_Syntax_Syntax.term' -> Prims.int) =
  fun tm ->
    match tm with
    | FStarC_Syntax_Syntax.Tm_constant (FStarC_Const.Const_int
        (n, FStar_Pervasives_Native.None)) ->
        FStarC_Compiler_Util.int_of_string n
    | uu___ -> failwith "Expected an Integer term"
let is_BitVector_primitive :
  'uuuuu .
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
      (FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax * 'uuuuu)
        Prims.list -> Prims.bool
  =
  fun head ->
    fun args ->
      match ((head.FStarC_Syntax_Syntax.n), args) with
      | (FStarC_Syntax_Syntax.Tm_fvar fv,
         (sz_arg, uu___)::uu___1::uu___2::[]) ->
          (((((((((((((((((FStarC_Syntax_Syntax.fv_eq_lid fv
                             FStarC_Parser_Const.bv_and_lid)
                            ||
                            (FStarC_Syntax_Syntax.fv_eq_lid fv
                               FStarC_Parser_Const.bv_xor_lid))
                           ||
                           (FStarC_Syntax_Syntax.fv_eq_lid fv
                              FStarC_Parser_Const.bv_or_lid))
                          ||
                          (FStarC_Syntax_Syntax.fv_eq_lid fv
                             FStarC_Parser_Const.bv_add_lid))
                         ||
                         (FStarC_Syntax_Syntax.fv_eq_lid fv
                            FStarC_Parser_Const.bv_sub_lid))
                        ||
                        (FStarC_Syntax_Syntax.fv_eq_lid fv
                           FStarC_Parser_Const.bv_shift_left_lid))
                       ||
                       (FStarC_Syntax_Syntax.fv_eq_lid fv
                          FStarC_Parser_Const.bv_shift_right_lid))
                      ||
                      (FStarC_Syntax_Syntax.fv_eq_lid fv
                         FStarC_Parser_Const.bv_udiv_lid))
                     ||
                     (FStarC_Syntax_Syntax.fv_eq_lid fv
                        FStarC_Parser_Const.bv_mod_lid))
                    ||
                    (FStarC_Syntax_Syntax.fv_eq_lid fv
                       FStarC_Parser_Const.bv_mul_lid))
                   ||
                   (FStarC_Syntax_Syntax.fv_eq_lid fv
                      FStarC_Parser_Const.bv_shift_left'_lid))
                  ||
                  (FStarC_Syntax_Syntax.fv_eq_lid fv
                     FStarC_Parser_Const.bv_shift_right'_lid))
                 ||
                 (FStarC_Syntax_Syntax.fv_eq_lid fv
                    FStarC_Parser_Const.bv_udiv_unsafe_lid))
                ||
                (FStarC_Syntax_Syntax.fv_eq_lid fv
                   FStarC_Parser_Const.bv_mod_unsafe_lid))
               ||
               (FStarC_Syntax_Syntax.fv_eq_lid fv
                  FStarC_Parser_Const.bv_mul'_lid))
              ||
              (FStarC_Syntax_Syntax.fv_eq_lid fv
                 FStarC_Parser_Const.bv_ult_lid))
             ||
             (FStarC_Syntax_Syntax.fv_eq_lid fv
                FStarC_Parser_Const.bv_uext_lid))
            && (isInteger sz_arg.FStarC_Syntax_Syntax.n)
      | (FStarC_Syntax_Syntax.Tm_fvar fv, (sz_arg, uu___)::uu___1::[]) ->
          ((FStarC_Syntax_Syntax.fv_eq_lid fv
              FStarC_Parser_Const.nat_to_bv_lid)
             ||
             (FStarC_Syntax_Syntax.fv_eq_lid fv
                FStarC_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStarC_Syntax_Syntax.n)
      | uu___ -> false
let rec (encode_const :
  FStarC_Const.sconst ->
    FStarC_SMTEncoding_Env.env_t ->
      (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.decls_elt
        Prims.list))
  =
  fun c ->
    fun env ->
      FStarC_Errors.with_ctx "While encoding a constant to SMT"
        (fun uu___ ->
           match c with
           | FStarC_Const.Const_unit ->
               (FStarC_SMTEncoding_Term.mk_Term_unit, [])
           | FStarC_Const.Const_bool (true) ->
               let uu___1 =
                 FStarC_SMTEncoding_Term.boxBool
                   FStarC_SMTEncoding_Util.mkTrue in
               (uu___1, [])
           | FStarC_Const.Const_bool (false) ->
               let uu___1 =
                 FStarC_SMTEncoding_Term.boxBool
                   FStarC_SMTEncoding_Util.mkFalse in
               (uu___1, [])
           | FStarC_Const.Const_char c1 ->
               let uu___1 =
                 let uu___2 =
                   let uu___3 =
                     let uu___4 =
                       let uu___5 =
                         FStarC_SMTEncoding_Util.mkInteger'
                           (FStarC_Compiler_Util.int_of_char c1) in
                       FStarC_SMTEncoding_Term.boxInt uu___5 in
                     [uu___4] in
                   ("FStar.Char.__char_of_int", uu___3) in
                 FStarC_SMTEncoding_Util.mkApp uu___2 in
               (uu___1, [])
           | FStarC_Const.Const_int (i, FStar_Pervasives_Native.None) ->
               let uu___1 =
                 let uu___2 = FStarC_SMTEncoding_Util.mkInteger i in
                 FStarC_SMTEncoding_Term.boxInt uu___2 in
               (uu___1, [])
           | FStarC_Const.Const_int (repr, FStar_Pervasives_Native.Some sw)
               ->
               let syntax_term =
                 FStarC_ToSyntax_ToSyntax.desugar_machine_integer
                   (env.FStarC_SMTEncoding_Env.tcenv).FStarC_TypeChecker_Env.dsenv
                   repr sw FStarC_Compiler_Range_Type.dummyRange in
               encode_term syntax_term env
           | FStarC_Const.Const_string (s, uu___1) ->
               let uu___2 =
                 let uu___3 = FStarC_SMTEncoding_Util.mk_String_const s in
                 FStarC_SMTEncoding_Term.boxString uu___3 in
               (uu___2, [])
           | FStarC_Const.Const_range uu___1 ->
               let uu___2 = FStarC_SMTEncoding_Term.mk_Range_const () in
               (uu___2, [])
           | FStarC_Const.Const_effect ->
               (FStarC_SMTEncoding_Term.mk_Term_type, [])
           | FStarC_Const.Const_real r ->
               let uu___1 =
                 let uu___2 = FStarC_SMTEncoding_Util.mkReal r in
                 FStarC_SMTEncoding_Term.boxReal uu___2 in
               (uu___1, [])
           | c1 ->
               let uu___1 =
                 let uu___2 =
                   FStarC_Class_Show.show FStarC_Syntax_Print.showable_const
                     c1 in
                 FStarC_Compiler_Util.format1 "Unhandled constant: %s" uu___2 in
               failwith uu___1)
and (encode_binders :
  FStarC_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStarC_Syntax_Syntax.binders ->
      FStarC_SMTEncoding_Env.env_t ->
        (FStarC_SMTEncoding_Term.fv Prims.list * FStarC_SMTEncoding_Term.term
          Prims.list * FStarC_SMTEncoding_Env.env_t *
          FStarC_SMTEncoding_Term.decls_t * FStarC_Syntax_Syntax.bv
          Prims.list))
  =
  fun fuel_opt ->
    fun bs ->
      fun env ->
        (let uu___1 = FStarC_Compiler_Debug.medium () in
         if uu___1
         then
           let uu___2 =
             FStarC_Class_Show.show
               (FStarC_Class_Show.show_list
                  FStarC_Syntax_Print.showable_binder) bs in
           FStarC_Compiler_Util.print1 "Encoding binders %s\n" uu___2
         else ());
        (let uu___1 =
           FStarC_Compiler_List.fold_left
             (fun uu___2 ->
                fun b ->
                  match uu___2 with
                  | (vars, guards, env1, decls, names) ->
                      let uu___3 =
                        let x = b.FStarC_Syntax_Syntax.binder_bv in
                        let uu___4 =
                          FStarC_SMTEncoding_Env.gen_term_var env1 x in
                        match uu___4 with
                        | (xxsym, xx, env') ->
                            let uu___5 =
                              let uu___6 =
                                norm env1 x.FStarC_Syntax_Syntax.sort in
                              encode_term_pred fuel_opt uu___6 env1 xx in
                            (match uu___5 with
                             | (guard_x_t, decls') ->
                                 let uu___6 =
                                   FStarC_SMTEncoding_Term.mk_fv
                                     (xxsym,
                                       FStarC_SMTEncoding_Term.Term_sort) in
                                 (uu___6, guard_x_t, env', decls', x)) in
                      (match uu___3 with
                       | (v, g, env2, decls', n) ->
                           ((v :: vars), (g :: guards), env2,
                             (FStarC_Compiler_List.op_At decls decls'), (n ::
                             names)))) ([], [], env, [], []) bs in
         match uu___1 with
         | (vars, guards, env1, decls, names) ->
             ((FStarC_Compiler_List.rev vars),
               (FStarC_Compiler_List.rev guards), env1, decls,
               (FStarC_Compiler_List.rev names)))
and (encode_term_pred :
  FStarC_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStarC_Syntax_Syntax.typ ->
      FStarC_SMTEncoding_Env.env_t ->
        FStarC_SMTEncoding_Term.term ->
          (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.decls_t))
  =
  fun fuel_opt ->
    fun t ->
      fun env ->
        fun e ->
          let uu___ = encode_term t env in
          match uu___ with
          | (t1, decls) ->
              let uu___1 =
                FStarC_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu___1, decls)
and (encode_arith_term :
  FStarC_SMTEncoding_Env.env_t ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
      FStarC_Syntax_Syntax.args ->
        (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.decls_t))
  =
  fun env ->
    fun head ->
      fun args_e ->
        let uu___ = encode_args args_e env in
        match uu___ with
        | (arg_tms, decls) ->
            let head_fv =
              match head.FStarC_Syntax_Syntax.n with
              | FStarC_Syntax_Syntax.Tm_fvar fv -> fv
              | uu___1 -> failwith "Impossible" in
            let unary unbox arg_tms1 =
              let uu___1 = FStarC_Compiler_List.hd arg_tms1 in unbox uu___1 in
            let binary unbox arg_tms1 =
              let uu___1 =
                let uu___2 = FStarC_Compiler_List.hd arg_tms1 in unbox uu___2 in
              let uu___2 =
                let uu___3 =
                  let uu___4 = FStarC_Compiler_List.tl arg_tms1 in
                  FStarC_Compiler_List.hd uu___4 in
                unbox uu___3 in
              (uu___1, uu___2) in
            let mk_default uu___1 =
              let uu___2 =
                FStarC_SMTEncoding_Env.lookup_free_var_sym env
                  head_fv.FStarC_Syntax_Syntax.fv_name in
              match uu___2 with
              | (fname, fuel_args, arity) ->
                  let args = FStarC_Compiler_List.op_At fuel_args arg_tms in
                  maybe_curry_app head.FStarC_Syntax_Syntax.pos fname arity
                    args in
            let mk_l box op mk_args ts =
              let uu___1 = FStarC_Options.smtencoding_l_arith_native () in
              if uu___1
              then
                let uu___2 = let uu___3 = mk_args ts in op uu___3 in
                box uu___2
              else mk_default () in
            let mk_nl box unbox nm op ts =
              let uu___1 = FStarC_Options.smtencoding_nl_arith_wrapped () in
              if uu___1
              then
                let uu___2 = binary unbox ts in
                match uu___2 with
                | (t1, t2) ->
                    let uu___3 = FStarC_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    box uu___3
              else
                (let uu___3 = FStarC_Options.smtencoding_nl_arith_native () in
                 if uu___3
                 then
                   let uu___4 = let uu___5 = binary unbox ts in op uu___5 in
                   box uu___4
                 else mk_default ()) in
            let add box unbox =
              mk_l box FStarC_SMTEncoding_Util.mkAdd (binary unbox) in
            let sub box unbox =
              mk_l box FStarC_SMTEncoding_Util.mkSub (binary unbox) in
            let minus box unbox =
              mk_l box FStarC_SMTEncoding_Util.mkMinus (unary unbox) in
            let mul box unbox nm =
              mk_nl box unbox nm FStarC_SMTEncoding_Util.mkMul in
            let div box unbox nm =
              mk_nl box unbox nm FStarC_SMTEncoding_Util.mkDiv in
            let modulus box unbox =
              mk_nl box unbox "_mod" FStarC_SMTEncoding_Util.mkMod in
            let ops =
              [(FStarC_Parser_Const.op_Addition,
                 (add FStarC_SMTEncoding_Term.boxInt
                    FStarC_SMTEncoding_Term.unboxInt));
              (FStarC_Parser_Const.op_Subtraction,
                (sub FStarC_SMTEncoding_Term.boxInt
                   FStarC_SMTEncoding_Term.unboxInt));
              (FStarC_Parser_Const.op_Multiply,
                (mul FStarC_SMTEncoding_Term.boxInt
                   FStarC_SMTEncoding_Term.unboxInt "_mul"));
              (FStarC_Parser_Const.op_Division,
                (div FStarC_SMTEncoding_Term.boxInt
                   FStarC_SMTEncoding_Term.unboxInt "_div"));
              (FStarC_Parser_Const.op_Modulus,
                (modulus FStarC_SMTEncoding_Term.boxInt
                   FStarC_SMTEncoding_Term.unboxInt));
              (FStarC_Parser_Const.op_Minus,
                (minus FStarC_SMTEncoding_Term.boxInt
                   FStarC_SMTEncoding_Term.unboxInt));
              (FStarC_Parser_Const.real_op_Addition,
                (add FStarC_SMTEncoding_Term.boxReal
                   FStarC_SMTEncoding_Term.unboxReal));
              (FStarC_Parser_Const.real_op_Subtraction,
                (sub FStarC_SMTEncoding_Term.boxReal
                   FStarC_SMTEncoding_Term.unboxReal));
              (FStarC_Parser_Const.real_op_Multiply,
                (mul FStarC_SMTEncoding_Term.boxReal
                   FStarC_SMTEncoding_Term.unboxReal "_rmul"));
              (FStarC_Parser_Const.real_op_Division,
                (mk_nl FStarC_SMTEncoding_Term.boxReal
                   FStarC_SMTEncoding_Term.unboxReal "_rdiv"
                   FStarC_SMTEncoding_Util.mkRealDiv));
              (FStarC_Parser_Const.real_op_LT,
                (mk_l FStarC_SMTEncoding_Term.boxBool
                   FStarC_SMTEncoding_Util.mkLT
                   (binary FStarC_SMTEncoding_Term.unboxReal)));
              (FStarC_Parser_Const.real_op_LTE,
                (mk_l FStarC_SMTEncoding_Term.boxBool
                   FStarC_SMTEncoding_Util.mkLTE
                   (binary FStarC_SMTEncoding_Term.unboxReal)));
              (FStarC_Parser_Const.real_op_GT,
                (mk_l FStarC_SMTEncoding_Term.boxBool
                   FStarC_SMTEncoding_Util.mkGT
                   (binary FStarC_SMTEncoding_Term.unboxReal)));
              (FStarC_Parser_Const.real_op_GTE,
                (mk_l FStarC_SMTEncoding_Term.boxBool
                   FStarC_SMTEncoding_Util.mkGTE
                   (binary FStarC_SMTEncoding_Term.unboxReal)))] in
            let uu___1 =
              let uu___2 =
                FStarC_Compiler_List.tryFind
                  (fun uu___3 ->
                     match uu___3 with
                     | (l, uu___4) ->
                         FStarC_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStarC_Compiler_Util.must uu___2 in
            (match uu___1 with
             | (uu___2, op) -> let uu___3 = op arg_tms in (uu___3, decls))
and (encode_BitVector_term :
  FStarC_SMTEncoding_Env.env_t ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
      (FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax *
        FStarC_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        Prims.list ->
        (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.decls_elt
          Prims.list))
  =
  fun env ->
    fun head ->
      fun args_e ->
        let uu___ = FStarC_Compiler_List.hd args_e in
        match uu___ with
        | (tm_sz, uu___1) ->
            let uu___2 = uu___ in
            let sz = getInteger tm_sz.FStarC_Syntax_Syntax.n in
            let sz_key =
              FStarC_Compiler_Util.format1 "BitVector_%s"
                (Prims.string_of_int sz) in
            let sz_decls =
              let uu___3 = FStarC_SMTEncoding_Term.mkBvConstructor sz in
              match uu___3 with
              | (t_decls, constr_name, discriminator_name) ->
                  let uu___4 =
                    let uu___5 =
                      let head1 =
                        FStarC_Syntax_Syntax.lid_as_fv
                          FStarC_Parser_Const.bv_t_lid
                          FStar_Pervasives_Native.None in
                      let t =
                        let uu___6 = FStarC_Syntax_Syntax.fv_to_tm head1 in
                        FStarC_Syntax_Util.mk_app uu___6
                          [(tm_sz, FStar_Pervasives_Native.None)] in
                      encode_term t env in
                    match uu___5 with
                    | (bv_t_n, decls) ->
                        let xsym =
                          let uu___6 =
                            let uu___7 =
                              FStarC_SMTEncoding_Env.varops.FStarC_SMTEncoding_Env.fresh
                                env.FStarC_SMTEncoding_Env.current_module_name
                                "x" in
                            (uu___7, FStarC_SMTEncoding_Term.Term_sort) in
                          FStarC_SMTEncoding_Term.mk_fv uu___6 in
                        let x = FStarC_SMTEncoding_Util.mkFreeV xsym in
                        let x_has_type_bv_t_n =
                          FStarC_SMTEncoding_Term.mk_HasType x bv_t_n in
                        let ax =
                          let uu___6 =
                            let uu___7 =
                              let uu___8 =
                                let uu___9 =
                                  FStarC_SMTEncoding_Util.mkApp
                                    (discriminator_name, [x]) in
                                (x_has_type_bv_t_n, uu___9) in
                              FStarC_SMTEncoding_Util.mkImp uu___8 in
                            ([[x_has_type_bv_t_n]], [xsym], uu___7) in
                          FStarC_SMTEncoding_Term.mkForall
                            head.FStarC_Syntax_Syntax.pos uu___6 in
                        let name =
                          Prims.strcat "typing_inversion_for_" constr_name in
                        let uu___6 =
                          FStarC_SMTEncoding_Util.mkAssume
                            (ax, (FStar_Pervasives_Native.Some name), name) in
                        (decls, uu___6) in
                  (match uu___4 with
                   | (decls, typing_inversion) ->
                       let uu___5 =
                         FStarC_SMTEncoding_Term.mk_decls "" sz_key
                           (FStarC_Compiler_List.op_At t_decls
                              [typing_inversion]) [] in
                       FStarC_Compiler_List.op_At decls uu___5) in
            let uu___3 =
              match ((head.FStarC_Syntax_Syntax.n), args_e) with
              | (FStarC_Syntax_Syntax.Tm_fvar fv,
                 uu___4::(sz_arg, uu___5)::uu___6::[]) when
                  (FStarC_Syntax_Syntax.fv_eq_lid fv
                     FStarC_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStarC_Syntax_Syntax.n)
                  ->
                  let uu___7 =
                    let uu___8 = FStarC_Compiler_List.tail args_e in
                    FStarC_Compiler_List.tail uu___8 in
                  let uu___8 =
                    let uu___9 = getInteger sz_arg.FStarC_Syntax_Syntax.n in
                    FStar_Pervasives_Native.Some uu___9 in
                  (uu___7, uu___8)
              | (FStarC_Syntax_Syntax.Tm_fvar fv,
                 uu___4::(sz_arg, uu___5)::uu___6::[]) when
                  FStarC_Syntax_Syntax.fv_eq_lid fv
                    FStarC_Parser_Const.bv_uext_lid
                  ->
                  let uu___7 =
                    let uu___8 =
                      FStarC_Class_Show.show
                        FStarC_Syntax_Print.showable_term sz_arg in
                    FStarC_Compiler_Util.format1
                      "Not a constant bitvector extend size: %s" uu___8 in
                  failwith uu___7
              | uu___4 ->
                  let uu___5 = FStarC_Compiler_List.tail args_e in
                  (uu___5, FStar_Pervasives_Native.None) in
            (match uu___3 with
             | (arg_tms, ext_sz) ->
                 let uu___4 = encode_args arg_tms env in
                 (match uu___4 with
                  | (arg_tms1, decls) ->
                      let head_fv =
                        match head.FStarC_Syntax_Syntax.n with
                        | FStarC_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu___5 -> failwith "Impossible" in
                      let unary arg_tms2 =
                        let uu___5 = FStarC_Compiler_List.hd arg_tms2 in
                        FStarC_SMTEncoding_Term.unboxBitVec sz uu___5 in
                      let unary_arith arg_tms2 =
                        let uu___5 = FStarC_Compiler_List.hd arg_tms2 in
                        FStarC_SMTEncoding_Term.unboxInt uu___5 in
                      let binary arg_tms2 =
                        let uu___5 =
                          let uu___6 = FStarC_Compiler_List.hd arg_tms2 in
                          FStarC_SMTEncoding_Term.unboxBitVec sz uu___6 in
                        let uu___6 =
                          let uu___7 =
                            let uu___8 = FStarC_Compiler_List.tl arg_tms2 in
                            FStarC_Compiler_List.hd uu___8 in
                          FStarC_SMTEncoding_Term.unboxBitVec sz uu___7 in
                        (uu___5, uu___6) in
                      let binary_arith arg_tms2 =
                        let uu___5 =
                          let uu___6 = FStarC_Compiler_List.hd arg_tms2 in
                          FStarC_SMTEncoding_Term.unboxBitVec sz uu___6 in
                        let uu___6 =
                          let uu___7 =
                            let uu___8 = FStarC_Compiler_List.tl arg_tms2 in
                            FStarC_Compiler_List.hd uu___8 in
                          FStarC_SMTEncoding_Term.unboxInt uu___7 in
                        (uu___5, uu___6) in
                      let mk_bv op mk_args resBox ts =
                        let uu___5 = let uu___6 = mk_args ts in op uu___6 in
                        resBox uu___5 in
                      let bv_and =
                        mk_bv FStarC_SMTEncoding_Util.mkBvAnd binary
                          (FStarC_SMTEncoding_Term.boxBitVec sz) in
                      let bv_xor =
                        mk_bv FStarC_SMTEncoding_Util.mkBvXor binary
                          (FStarC_SMTEncoding_Term.boxBitVec sz) in
                      let bv_or =
                        mk_bv FStarC_SMTEncoding_Util.mkBvOr binary
                          (FStarC_SMTEncoding_Term.boxBitVec sz) in
                      let bv_add =
                        mk_bv FStarC_SMTEncoding_Util.mkBvAdd binary
                          (FStarC_SMTEncoding_Term.boxBitVec sz) in
                      let bv_sub =
                        mk_bv FStarC_SMTEncoding_Util.mkBvSub binary
                          (FStarC_SMTEncoding_Term.boxBitVec sz) in
                      let bv_shl =
                        mk_bv (FStarC_SMTEncoding_Util.mkBvShl sz)
                          binary_arith (FStarC_SMTEncoding_Term.boxBitVec sz) in
                      let bv_shr =
                        mk_bv (FStarC_SMTEncoding_Util.mkBvShr sz)
                          binary_arith (FStarC_SMTEncoding_Term.boxBitVec sz) in
                      let bv_udiv =
                        mk_bv (FStarC_SMTEncoding_Util.mkBvUdiv sz)
                          binary_arith (FStarC_SMTEncoding_Term.boxBitVec sz) in
                      let bv_mod =
                        mk_bv (FStarC_SMTEncoding_Util.mkBvMod sz)
                          binary_arith (FStarC_SMTEncoding_Term.boxBitVec sz) in
                      let bv_mul =
                        mk_bv (FStarC_SMTEncoding_Util.mkBvMul sz)
                          binary_arith (FStarC_SMTEncoding_Term.boxBitVec sz) in
                      let bv_shl' =
                        mk_bv (FStarC_SMTEncoding_Util.mkBvShl' sz) binary
                          (FStarC_SMTEncoding_Term.boxBitVec sz) in
                      let bv_shr' =
                        mk_bv (FStarC_SMTEncoding_Util.mkBvShr' sz) binary
                          (FStarC_SMTEncoding_Term.boxBitVec sz) in
                      let bv_udiv_unsafe =
                        mk_bv (FStarC_SMTEncoding_Util.mkBvUdivUnsafe sz)
                          binary (FStarC_SMTEncoding_Term.boxBitVec sz) in
                      let bv_mod_unsafe =
                        mk_bv (FStarC_SMTEncoding_Util.mkBvModUnsafe sz)
                          binary (FStarC_SMTEncoding_Term.boxBitVec sz) in
                      let bv_mul' =
                        mk_bv (FStarC_SMTEncoding_Util.mkBvMul' sz) binary
                          (FStarC_SMTEncoding_Term.boxBitVec sz) in
                      let bv_ult =
                        mk_bv FStarC_SMTEncoding_Util.mkBvUlt binary
                          FStarC_SMTEncoding_Term.boxBool in
                      let bv_uext arg_tms2 =
                        let uu___5 =
                          let uu___6 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None ->
                                failwith "impossible" in
                          FStarC_SMTEncoding_Util.mkBvUext uu___6 in
                        let uu___6 =
                          let uu___7 =
                            let uu___8 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None ->
                                  failwith "impossible" in
                            sz + uu___8 in
                          FStarC_SMTEncoding_Term.boxBitVec uu___7 in
                        mk_bv uu___5 unary uu___6 arg_tms2 in
                      let to_int =
                        mk_bv FStarC_SMTEncoding_Util.mkBvToNat unary
                          FStarC_SMTEncoding_Term.boxInt in
                      let bv_to =
                        mk_bv (FStarC_SMTEncoding_Util.mkNatToBv sz)
                          unary_arith (FStarC_SMTEncoding_Term.boxBitVec sz) in
                      let ops =
                        [(FStarC_Parser_Const.bv_and_lid, bv_and);
                        (FStarC_Parser_Const.bv_xor_lid, bv_xor);
                        (FStarC_Parser_Const.bv_or_lid, bv_or);
                        (FStarC_Parser_Const.bv_add_lid, bv_add);
                        (FStarC_Parser_Const.bv_sub_lid, bv_sub);
                        (FStarC_Parser_Const.bv_shift_left_lid, bv_shl);
                        (FStarC_Parser_Const.bv_shift_right_lid, bv_shr);
                        (FStarC_Parser_Const.bv_udiv_lid, bv_udiv);
                        (FStarC_Parser_Const.bv_mod_lid, bv_mod);
                        (FStarC_Parser_Const.bv_mul_lid, bv_mul);
                        (FStarC_Parser_Const.bv_shift_left'_lid, bv_shl');
                        (FStarC_Parser_Const.bv_shift_right'_lid, bv_shr');
                        (FStarC_Parser_Const.bv_udiv_unsafe_lid,
                          bv_udiv_unsafe);
                        (FStarC_Parser_Const.bv_mod_unsafe_lid,
                          bv_mod_unsafe);
                        (FStarC_Parser_Const.bv_mul'_lid, bv_mul');
                        (FStarC_Parser_Const.bv_ult_lid, bv_ult);
                        (FStarC_Parser_Const.bv_uext_lid, bv_uext);
                        (FStarC_Parser_Const.bv_to_nat_lid, to_int);
                        (FStarC_Parser_Const.nat_to_bv_lid, bv_to)] in
                      let uu___5 =
                        let uu___6 =
                          FStarC_Compiler_List.tryFind
                            (fun uu___7 ->
                               match uu___7 with
                               | (l, uu___8) ->
                                   FStarC_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops in
                        FStarC_Compiler_Util.must uu___6 in
                      (match uu___5 with
                       | (uu___6, op) ->
                           let uu___7 = op arg_tms1 in
                           (uu___7,
                             (FStarC_Compiler_List.op_At sz_decls decls)))))
and (encode_deeply_embedded_quantifier :
  FStarC_Syntax_Syntax.term ->
    FStarC_SMTEncoding_Env.env_t ->
      (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.decls_t))
  =
  fun t ->
    fun env ->
      let env1 =
        {
          FStarC_SMTEncoding_Env.bvar_bindings =
            (env.FStarC_SMTEncoding_Env.bvar_bindings);
          FStarC_SMTEncoding_Env.fvar_bindings =
            (env.FStarC_SMTEncoding_Env.fvar_bindings);
          FStarC_SMTEncoding_Env.depth = (env.FStarC_SMTEncoding_Env.depth);
          FStarC_SMTEncoding_Env.tcenv = (env.FStarC_SMTEncoding_Env.tcenv);
          FStarC_SMTEncoding_Env.warn = (env.FStarC_SMTEncoding_Env.warn);
          FStarC_SMTEncoding_Env.nolabels =
            (env.FStarC_SMTEncoding_Env.nolabels);
          FStarC_SMTEncoding_Env.use_zfuel_name =
            (env.FStarC_SMTEncoding_Env.use_zfuel_name);
          FStarC_SMTEncoding_Env.encode_non_total_function_typ =
            (env.FStarC_SMTEncoding_Env.encode_non_total_function_typ);
          FStarC_SMTEncoding_Env.current_module_name =
            (env.FStarC_SMTEncoding_Env.current_module_name);
          FStarC_SMTEncoding_Env.encoding_quantifier = true;
          FStarC_SMTEncoding_Env.global_cache =
            (env.FStarC_SMTEncoding_Env.global_cache)
        } in
      let uu___ = encode_term t env1 in
      match uu___ with
      | (tm, decls) ->
          let vars = FStarC_SMTEncoding_Term.free_variables tm in
          let valid_tm = FStarC_SMTEncoding_Term.mk_Valid tm in
          let key =
            FStarC_SMTEncoding_Term.mkForall t.FStarC_Syntax_Syntax.pos
              ([], vars, valid_tm) in
          let tkey_hash = FStarC_SMTEncoding_Term.hash_of_term key in
          (match tm.FStarC_SMTEncoding_Term.tm with
           | FStarC_SMTEncoding_Term.App
               (uu___1,
                {
                  FStarC_SMTEncoding_Term.tm = FStarC_SMTEncoding_Term.FreeV
                    uu___2;
                  FStarC_SMTEncoding_Term.freevars = uu___3;
                  FStarC_SMTEncoding_Term.rng = uu___4;_}::{
                                                             FStarC_SMTEncoding_Term.tm
                                                               =
                                                               FStarC_SMTEncoding_Term.FreeV
                                                               uu___5;
                                                             FStarC_SMTEncoding_Term.freevars
                                                               = uu___6;
                                                             FStarC_SMTEncoding_Term.rng
                                                               = uu___7;_}::[])
               ->
               (FStarC_Errors.log_issue
                  (FStarC_Syntax_Syntax.has_range_syntax ()) t
                  FStarC_Errors_Codes.Warning_QuantifierWithoutPattern ()
                  (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                  (Obj.magic
                     "Not encoding deeply embedded, unguarded quantifier to SMT");
                (tm, decls))
           | uu___1 ->
               let uu___2 = encode_formula t env1 in
               (match uu___2 with
                | (phi, decls') ->
                    let interp =
                      match vars with
                      | [] ->
                          let uu___3 =
                            let uu___4 = FStarC_SMTEncoding_Term.mk_Valid tm in
                            (uu___4, phi) in
                          FStarC_SMTEncoding_Util.mkIff uu___3
                      | uu___3 ->
                          let uu___4 =
                            let uu___5 =
                              let uu___6 =
                                let uu___7 =
                                  FStarC_SMTEncoding_Term.mk_Valid tm in
                                (uu___7, phi) in
                              FStarC_SMTEncoding_Util.mkIff uu___6 in
                            ([[valid_tm]], vars, uu___5) in
                          FStarC_SMTEncoding_Term.mkForall
                            t.FStarC_Syntax_Syntax.pos uu___4 in
                    let ax =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 =
                            FStarC_Compiler_Util.digest_of_string tkey_hash in
                          Prims.strcat "l_quant_interp_" uu___5 in
                        (interp,
                          (FStar_Pervasives_Native.Some
                             "Interpretation of deeply embedded quantifier"),
                          uu___4) in
                      FStarC_SMTEncoding_Util.mkAssume uu___3 in
                    let uu___3 =
                      let uu___4 =
                        let uu___5 =
                          FStarC_SMTEncoding_Term.mk_decls "" tkey_hash 
                            [ax] (FStarC_Compiler_List.op_At decls decls') in
                        FStarC_Compiler_List.op_At decls' uu___5 in
                      FStarC_Compiler_List.op_At decls uu___4 in
                    (tm, uu___3)))
and (encode_term :
  FStarC_Syntax_Syntax.typ ->
    FStarC_SMTEncoding_Env.env_t ->
      (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.decls_t))
  =
  fun t ->
    fun env ->
      FStarC_Defensive.def_check_scoped FStarC_TypeChecker_Env.hasBinders_env
        FStarC_Class_Binders.hasNames_term FStarC_Syntax_Print.pretty_term
        t.FStarC_Syntax_Syntax.pos "encode_term"
        env.FStarC_SMTEncoding_Env.tcenv t;
      (let t1 = FStarC_Syntax_Subst.compress t in
       let t0 = t1 in
       (let uu___2 = FStarC_Compiler_Effect.op_Bang dbg_SMTEncoding in
        if uu___2
        then
          let uu___3 =
            FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term t1 in
          let uu___4 =
            FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t1 in
          FStarC_Compiler_Util.print2 "(%s)   %s\n" uu___3 uu___4
        else ());
       (match t1.FStarC_Syntax_Syntax.n with
        | FStarC_Syntax_Syntax.Tm_delayed uu___2 ->
            let uu___3 =
              let uu___4 =
                FStarC_Compiler_Range_Ops.string_of_range
                  t1.FStarC_Syntax_Syntax.pos in
              let uu___5 =
                FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term
                  t1 in
              let uu___6 =
                FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t1 in
              FStarC_Compiler_Util.format3 "(%s) Impossible: %s\n%s\n" uu___4
                uu___5 uu___6 in
            failwith uu___3
        | FStarC_Syntax_Syntax.Tm_unknown ->
            let uu___2 =
              let uu___3 =
                FStarC_Compiler_Range_Ops.string_of_range
                  t1.FStarC_Syntax_Syntax.pos in
              let uu___4 =
                FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term
                  t1 in
              let uu___5 =
                FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t1 in
              FStarC_Compiler_Util.format3 "(%s) Impossible: %s\n%s\n" uu___3
                uu___4 uu___5 in
            failwith uu___2
        | FStarC_Syntax_Syntax.Tm_lazy i ->
            let e = FStarC_Syntax_Util.unfold_lazy i in
            ((let uu___3 = FStarC_Compiler_Effect.op_Bang dbg_SMTEncoding in
              if uu___3
              then
                let uu___4 =
                  FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t1 in
                let uu___5 =
                  FStarC_Class_Show.show FStarC_Syntax_Print.showable_term e in
                FStarC_Compiler_Util.print2 ">> Unfolded (%s) ~> (%s)\n"
                  uu___4 uu___5
              else ());
             encode_term e env)
        | FStarC_Syntax_Syntax.Tm_bvar x ->
            let uu___2 =
              let uu___3 =
                FStarC_Class_Show.show FStarC_Syntax_Print.showable_bv x in
              FStarC_Compiler_Util.format1
                "Impossible: locally nameless; got %s" uu___3 in
            failwith uu___2
        | FStarC_Syntax_Syntax.Tm_ascribed
            { FStarC_Syntax_Syntax.tm = t2;
              FStarC_Syntax_Syntax.asc = (k, uu___2, uu___3);
              FStarC_Syntax_Syntax.eff_opt = uu___4;_}
            ->
            let uu___5 =
              match k with
              | FStar_Pervasives.Inl t3 -> FStarC_Syntax_Util.is_unit t3
              | uu___6 -> false in
            if uu___5
            then (FStarC_SMTEncoding_Term.mk_Term_unit, [])
            else encode_term t2 env
        | FStarC_Syntax_Syntax.Tm_quoted (qt, uu___2) ->
            let tv =
              let uu___3 =
                let uu___4 = FStarC_Reflection_V2_Builtins.inspect_ln qt in
                FStarC_Syntax_Embeddings_Base.embed
                  FStarC_Reflection_V2_Embeddings.e_term_view uu___4 in
              uu___3 t1.FStarC_Syntax_Syntax.pos FStar_Pervasives_Native.None
                FStarC_Syntax_Embeddings_Base.id_norm_cb in
            ((let uu___4 = FStarC_Compiler_Effect.op_Bang dbg_SMTEncoding in
              if uu___4
              then
                let uu___5 =
                  FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t0 in
                let uu___6 =
                  FStarC_Class_Show.show FStarC_Syntax_Print.showable_term tv in
                FStarC_Compiler_Util.print2 ">> Inspected (%s) ~> (%s)\n"
                  uu___5 uu___6
              else ());
             (let t2 =
                let uu___4 =
                  let uu___5 = FStarC_Syntax_Syntax.as_arg tv in [uu___5] in
                FStarC_Syntax_Util.mk_app
                  (FStarC_Reflection_V2_Constants.refl_constant_term
                     FStarC_Reflection_V2_Constants.fstar_refl_pack_ln)
                  uu___4 in
              encode_term t2 env))
        | FStarC_Syntax_Syntax.Tm_meta
            { FStarC_Syntax_Syntax.tm2 = t2;
              FStarC_Syntax_Syntax.meta = FStarC_Syntax_Syntax.Meta_pattern
                uu___2;_}
            ->
            encode_term t2
              {
                FStarC_SMTEncoding_Env.bvar_bindings =
                  (env.FStarC_SMTEncoding_Env.bvar_bindings);
                FStarC_SMTEncoding_Env.fvar_bindings =
                  (env.FStarC_SMTEncoding_Env.fvar_bindings);
                FStarC_SMTEncoding_Env.depth =
                  (env.FStarC_SMTEncoding_Env.depth);
                FStarC_SMTEncoding_Env.tcenv =
                  (env.FStarC_SMTEncoding_Env.tcenv);
                FStarC_SMTEncoding_Env.warn =
                  (env.FStarC_SMTEncoding_Env.warn);
                FStarC_SMTEncoding_Env.nolabels =
                  (env.FStarC_SMTEncoding_Env.nolabels);
                FStarC_SMTEncoding_Env.use_zfuel_name =
                  (env.FStarC_SMTEncoding_Env.use_zfuel_name);
                FStarC_SMTEncoding_Env.encode_non_total_function_typ =
                  (env.FStarC_SMTEncoding_Env.encode_non_total_function_typ);
                FStarC_SMTEncoding_Env.current_module_name =
                  (env.FStarC_SMTEncoding_Env.current_module_name);
                FStarC_SMTEncoding_Env.encoding_quantifier = false;
                FStarC_SMTEncoding_Env.global_cache =
                  (env.FStarC_SMTEncoding_Env.global_cache)
              }
        | FStarC_Syntax_Syntax.Tm_meta
            { FStarC_Syntax_Syntax.tm2 = t2;
              FStarC_Syntax_Syntax.meta = uu___2;_}
            -> encode_term t2 env
        | FStarC_Syntax_Syntax.Tm_name x ->
            let t2 = FStarC_SMTEncoding_Env.lookup_term_var env x in (t2, [])
        | FStarC_Syntax_Syntax.Tm_fvar v ->
            let encode_freev uu___2 =
              let fvb =
                FStarC_SMTEncoding_Env.lookup_free_var_name env
                  v.FStarC_Syntax_Syntax.fv_name in
              let tok =
                FStarC_SMTEncoding_Env.lookup_free_var env
                  v.FStarC_Syntax_Syntax.fv_name in
              let tkey_hash = FStarC_SMTEncoding_Term.hash_of_term tok in
              let uu___3 =
                if fvb.FStarC_SMTEncoding_Env.smt_arity > Prims.int_zero
                then
                  match tok.FStarC_SMTEncoding_Term.tm with
                  | FStarC_SMTEncoding_Term.FreeV uu___4 ->
                      let sym_name =
                        let uu___5 =
                          FStarC_Compiler_Util.digest_of_string tkey_hash in
                        Prims.strcat "@kick_partial_app_" uu___5 in
                      let uu___5 =
                        let uu___6 =
                          let uu___7 =
                            let uu___8 =
                              FStarC_SMTEncoding_Term.kick_partial_app tok in
                            (uu___8,
                              (FStar_Pervasives_Native.Some
                                 "kick_partial_app"), sym_name) in
                          FStarC_SMTEncoding_Util.mkAssume uu___7 in
                        [uu___6] in
                      (uu___5, sym_name)
                  | FStarC_SMTEncoding_Term.App (uu___4, []) ->
                      let sym_name =
                        let uu___5 =
                          FStarC_Compiler_Util.digest_of_string tkey_hash in
                        Prims.strcat "@kick_partial_app_" uu___5 in
                      let uu___5 =
                        let uu___6 =
                          let uu___7 =
                            let uu___8 =
                              FStarC_SMTEncoding_Term.kick_partial_app tok in
                            (uu___8,
                              (FStar_Pervasives_Native.Some
                                 "kick_partial_app"), sym_name) in
                          FStarC_SMTEncoding_Util.mkAssume uu___7 in
                        [uu___6] in
                      (uu___5, sym_name)
                  | uu___4 -> ([], "")
                else ([], "") in
              match uu___3 with
              | (aux_decls, sym_name) ->
                  let uu___4 =
                    if aux_decls = []
                    then FStarC_SMTEncoding_Term.mk_decls_trivial []
                    else
                      FStarC_SMTEncoding_Term.mk_decls sym_name tkey_hash
                        aux_decls [] in
                  (tok, uu___4) in
            let uu___2 = head_redex env t1 in
            if uu___2
            then
              let uu___3 = maybe_whnf env t1 in
              (match uu___3 with
               | FStar_Pervasives_Native.None -> encode_freev ()
               | FStar_Pervasives_Native.Some t2 -> encode_term t2 env)
            else encode_freev ()
        | FStarC_Syntax_Syntax.Tm_type uu___2 ->
            (FStarC_SMTEncoding_Term.mk_Term_type, [])
        | FStarC_Syntax_Syntax.Tm_uinst (t2, uu___2) -> encode_term t2 env
        | FStarC_Syntax_Syntax.Tm_constant c -> encode_const c env
        | FStarC_Syntax_Syntax.Tm_arrow
            { FStarC_Syntax_Syntax.bs1 = binders;
              FStarC_Syntax_Syntax.comp = c;_}
            ->
            let module_name = env.FStarC_SMTEncoding_Env.current_module_name in
            let uu___2 = FStarC_Syntax_Subst.open_comp binders c in
            (match uu___2 with
             | (binders1, res) ->
                 let uu___3 =
                   (env.FStarC_SMTEncoding_Env.encode_non_total_function_typ
                      && (FStarC_Syntax_Util.is_pure_or_ghost_comp res))
                     || (FStarC_Syntax_Util.is_tot_or_gtot_comp res) in
                 if uu___3
                 then
                   let uu___4 =
                     encode_binders FStar_Pervasives_Native.None binders1 env in
                   (match uu___4 with
                    | (vars, guards_l, env', decls, uu___5) ->
                        let fsym =
                          let uu___6 =
                            let uu___7 =
                              FStarC_SMTEncoding_Env.varops.FStarC_SMTEncoding_Env.fresh
                                module_name "f" in
                            (uu___7, FStarC_SMTEncoding_Term.Term_sort) in
                          FStarC_SMTEncoding_Term.mk_fv uu___6 in
                        let f = FStarC_SMTEncoding_Util.mkFreeV fsym in
                        let app = mk_Apply f vars in
                        let tcenv_bs =
                          let uu___6 = env'.FStarC_SMTEncoding_Env.tcenv in
                          {
                            FStarC_TypeChecker_Env.solver =
                              (uu___6.FStarC_TypeChecker_Env.solver);
                            FStarC_TypeChecker_Env.range =
                              (uu___6.FStarC_TypeChecker_Env.range);
                            FStarC_TypeChecker_Env.curmodule =
                              (uu___6.FStarC_TypeChecker_Env.curmodule);
                            FStarC_TypeChecker_Env.gamma =
                              (uu___6.FStarC_TypeChecker_Env.gamma);
                            FStarC_TypeChecker_Env.gamma_sig =
                              (uu___6.FStarC_TypeChecker_Env.gamma_sig);
                            FStarC_TypeChecker_Env.gamma_cache =
                              (uu___6.FStarC_TypeChecker_Env.gamma_cache);
                            FStarC_TypeChecker_Env.modules =
                              (uu___6.FStarC_TypeChecker_Env.modules);
                            FStarC_TypeChecker_Env.expected_typ =
                              (uu___6.FStarC_TypeChecker_Env.expected_typ);
                            FStarC_TypeChecker_Env.sigtab =
                              (uu___6.FStarC_TypeChecker_Env.sigtab);
                            FStarC_TypeChecker_Env.attrtab =
                              (uu___6.FStarC_TypeChecker_Env.attrtab);
                            FStarC_TypeChecker_Env.instantiate_imp =
                              (uu___6.FStarC_TypeChecker_Env.instantiate_imp);
                            FStarC_TypeChecker_Env.effects =
                              (uu___6.FStarC_TypeChecker_Env.effects);
                            FStarC_TypeChecker_Env.generalize =
                              (uu___6.FStarC_TypeChecker_Env.generalize);
                            FStarC_TypeChecker_Env.letrecs =
                              (uu___6.FStarC_TypeChecker_Env.letrecs);
                            FStarC_TypeChecker_Env.top_level =
                              (uu___6.FStarC_TypeChecker_Env.top_level);
                            FStarC_TypeChecker_Env.check_uvars =
                              (uu___6.FStarC_TypeChecker_Env.check_uvars);
                            FStarC_TypeChecker_Env.use_eq_strict =
                              (uu___6.FStarC_TypeChecker_Env.use_eq_strict);
                            FStarC_TypeChecker_Env.is_iface =
                              (uu___6.FStarC_TypeChecker_Env.is_iface);
                            FStarC_TypeChecker_Env.admit = true;
                            FStarC_TypeChecker_Env.lax_universes =
                              (uu___6.FStarC_TypeChecker_Env.lax_universes);
                            FStarC_TypeChecker_Env.phase1 =
                              (uu___6.FStarC_TypeChecker_Env.phase1);
                            FStarC_TypeChecker_Env.failhard =
                              (uu___6.FStarC_TypeChecker_Env.failhard);
                            FStarC_TypeChecker_Env.flychecking =
                              (uu___6.FStarC_TypeChecker_Env.flychecking);
                            FStarC_TypeChecker_Env.uvar_subtyping =
                              (uu___6.FStarC_TypeChecker_Env.uvar_subtyping);
                            FStarC_TypeChecker_Env.intactics =
                              (uu___6.FStarC_TypeChecker_Env.intactics);
                            FStarC_TypeChecker_Env.nocoerce =
                              (uu___6.FStarC_TypeChecker_Env.nocoerce);
                            FStarC_TypeChecker_Env.tc_term =
                              (uu___6.FStarC_TypeChecker_Env.tc_term);
                            FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
                              (uu___6.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                            FStarC_TypeChecker_Env.universe_of =
                              (uu___6.FStarC_TypeChecker_Env.universe_of);
                            FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                              =
                              (uu___6.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                            FStarC_TypeChecker_Env.teq_nosmt_force =
                              (uu___6.FStarC_TypeChecker_Env.teq_nosmt_force);
                            FStarC_TypeChecker_Env.subtype_nosmt_force =
                              (uu___6.FStarC_TypeChecker_Env.subtype_nosmt_force);
                            FStarC_TypeChecker_Env.qtbl_name_and_index =
                              (uu___6.FStarC_TypeChecker_Env.qtbl_name_and_index);
                            FStarC_TypeChecker_Env.normalized_eff_names =
                              (uu___6.FStarC_TypeChecker_Env.normalized_eff_names);
                            FStarC_TypeChecker_Env.fv_delta_depths =
                              (uu___6.FStarC_TypeChecker_Env.fv_delta_depths);
                            FStarC_TypeChecker_Env.proof_ns =
                              (uu___6.FStarC_TypeChecker_Env.proof_ns);
                            FStarC_TypeChecker_Env.synth_hook =
                              (uu___6.FStarC_TypeChecker_Env.synth_hook);
                            FStarC_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___6.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                            FStarC_TypeChecker_Env.splice =
                              (uu___6.FStarC_TypeChecker_Env.splice);
                            FStarC_TypeChecker_Env.mpreprocess =
                              (uu___6.FStarC_TypeChecker_Env.mpreprocess);
                            FStarC_TypeChecker_Env.postprocess =
                              (uu___6.FStarC_TypeChecker_Env.postprocess);
                            FStarC_TypeChecker_Env.identifier_info =
                              (uu___6.FStarC_TypeChecker_Env.identifier_info);
                            FStarC_TypeChecker_Env.tc_hooks =
                              (uu___6.FStarC_TypeChecker_Env.tc_hooks);
                            FStarC_TypeChecker_Env.dsenv =
                              (uu___6.FStarC_TypeChecker_Env.dsenv);
                            FStarC_TypeChecker_Env.nbe =
                              (uu___6.FStarC_TypeChecker_Env.nbe);
                            FStarC_TypeChecker_Env.strict_args_tab =
                              (uu___6.FStarC_TypeChecker_Env.strict_args_tab);
                            FStarC_TypeChecker_Env.erasable_types_tab =
                              (uu___6.FStarC_TypeChecker_Env.erasable_types_tab);
                            FStarC_TypeChecker_Env.enable_defer_to_tac =
                              (uu___6.FStarC_TypeChecker_Env.enable_defer_to_tac);
                            FStarC_TypeChecker_Env.unif_allow_ref_guards =
                              (uu___6.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                            FStarC_TypeChecker_Env.erase_erasable_args =
                              (uu___6.FStarC_TypeChecker_Env.erase_erasable_args);
                            FStarC_TypeChecker_Env.core_check =
                              (uu___6.FStarC_TypeChecker_Env.core_check);
                            FStarC_TypeChecker_Env.missing_decl =
                              (uu___6.FStarC_TypeChecker_Env.missing_decl)
                          } in
                        let uu___6 =
                          FStarC_TypeChecker_Util.pure_or_ghost_pre_and_post
                            tcenv_bs res in
                        (match uu___6 with
                         | (pre_opt, res_t) ->
                             let uu___7 =
                               encode_term_pred FStar_Pervasives_Native.None
                                 res_t env' app in
                             (match uu___7 with
                              | (res_pred, decls') ->
                                  let uu___8 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None ->
                                        let uu___9 =
                                          FStarC_SMTEncoding_Util.mk_and_l
                                            guards_l in
                                        (uu___9, [])
                                    | FStar_Pervasives_Native.Some pre ->
                                        let uu___9 = encode_formula pre env' in
                                        (match uu___9 with
                                         | (guard, decls0) ->
                                             let uu___10 =
                                               FStarC_SMTEncoding_Util.mk_and_l
                                                 (guard :: guards_l) in
                                             (uu___10, decls0)) in
                                  (match uu___8 with
                                   | (guards, guard_decls) ->
                                       let is_pure =
                                         let uu___9 =
                                           FStarC_TypeChecker_Normalize.maybe_ghost_to_pure
                                             env.FStarC_SMTEncoding_Env.tcenv
                                             res in
                                         FStarC_Syntax_Util.is_pure_comp
                                           uu___9 in
                                       let t_interp =
                                         let uu___9 =
                                           let uu___10 =
                                             FStarC_SMTEncoding_Util.mkImp
                                               (guards, res_pred) in
                                           ([[app]], vars, uu___10) in
                                         FStarC_SMTEncoding_Term.mkForall
                                           t1.FStarC_Syntax_Syntax.pos uu___9 in
                                       let t_interp1 =
                                         let tot_fun_axioms =
                                           isTotFun_axioms
                                             t1.FStarC_Syntax_Syntax.pos f
                                             vars guards_l is_pure in
                                         FStarC_SMTEncoding_Util.mkAnd
                                           (t_interp, tot_fun_axioms) in
                                       let cvars =
                                         let uu___9 =
                                           FStarC_SMTEncoding_Term.free_variables
                                             t_interp1 in
                                         FStarC_Compiler_List.filter
                                           (fun x ->
                                              let uu___10 =
                                                FStarC_SMTEncoding_Term.fv_name
                                                  x in
                                              let uu___11 =
                                                FStarC_SMTEncoding_Term.fv_name
                                                  fsym in
                                              uu___10 <> uu___11) uu___9 in
                                       let tkey =
                                         FStarC_SMTEncoding_Term.mkForall
                                           t1.FStarC_Syntax_Syntax.pos
                                           ([], (fsym :: cvars), t_interp1) in
                                       let prefix =
                                         if is_pure
                                         then "Tm_arrow_"
                                         else "Tm_ghost_arrow_" in
                                       let tkey_hash =
                                         let uu___9 =
                                           FStarC_SMTEncoding_Term.hash_of_term
                                             tkey in
                                         Prims.strcat prefix uu___9 in
                                       let tsym =
                                         let uu___9 =
                                           FStarC_Compiler_Util.digest_of_string
                                             tkey_hash in
                                         Prims.strcat prefix uu___9 in
                                       let cvar_sorts =
                                         FStarC_Compiler_List.map
                                           FStarC_SMTEncoding_Term.fv_sort
                                           cvars in
                                       let caption =
                                         let uu___9 =
                                           FStarC_Options.log_queries () in
                                         if uu___9
                                         then
                                           let uu___10 =
                                             let uu___11 =
                                               FStarC_TypeChecker_Normalize.term_to_string
                                                 env.FStarC_SMTEncoding_Env.tcenv
                                                 t0 in
                                             FStarC_Compiler_Util.replace_char
                                               uu___11 10 32 in
                                           FStar_Pervasives_Native.Some
                                             uu___10
                                         else FStar_Pervasives_Native.None in
                                       let tdecl =
                                         FStarC_SMTEncoding_Term.DeclFun
                                           (tsym, cvar_sorts,
                                             FStarC_SMTEncoding_Term.Term_sort,
                                             caption) in
                                       let t2 =
                                         let uu___9 =
                                           let uu___10 =
                                             FStarC_Compiler_List.map
                                               FStarC_SMTEncoding_Util.mkFreeV
                                               cvars in
                                           (tsym, uu___10) in
                                         FStarC_SMTEncoding_Util.mkApp uu___9 in
                                       let t_has_kind =
                                         FStarC_SMTEncoding_Term.mk_HasType
                                           t2
                                           FStarC_SMTEncoding_Term.mk_Term_type in
                                       let k_assumption =
                                         let a_name =
                                           Prims.strcat "kinding_" tsym in
                                         let uu___9 =
                                           let uu___10 =
                                             FStarC_SMTEncoding_Term.mkForall
                                               t0.FStarC_Syntax_Syntax.pos
                                               ([[t_has_kind]], cvars,
                                                 t_has_kind) in
                                           (uu___10,
                                             (FStar_Pervasives_Native.Some
                                                a_name), a_name) in
                                         FStarC_SMTEncoding_Util.mkAssume
                                           uu___9 in
                                       let f_has_t =
                                         FStarC_SMTEncoding_Term.mk_HasType f
                                           t2 in
                                       let f_has_t_z =
                                         FStarC_SMTEncoding_Term.mk_HasTypeZ
                                           f t2 in
                                       let pre_typing =
                                         let a_name =
                                           Prims.strcat "pre_typing_" tsym in
                                         let uu___9 =
                                           let uu___10 =
                                             let uu___11 =
                                               let uu___12 =
                                                 let uu___13 =
                                                   let uu___14 =
                                                     let uu___15 =
                                                       FStarC_SMTEncoding_Term.mk_PreType
                                                         f in
                                                     FStarC_SMTEncoding_Term.mk_tester
                                                       "Tm_arrow" uu___15 in
                                                   (f_has_t, uu___14) in
                                                 FStarC_SMTEncoding_Util.mkImp
                                                   uu___13 in
                                               ([[f_has_t]], (fsym :: cvars),
                                                 uu___12) in
                                             let uu___12 =
                                               mkForall_fuel module_name
                                                 t0.FStarC_Syntax_Syntax.pos in
                                             uu___12 uu___11 in
                                           (uu___10,
                                             (FStar_Pervasives_Native.Some
                                                "pre-typing for functions"),
                                             (Prims.strcat module_name
                                                (Prims.strcat "_" a_name))) in
                                         FStarC_SMTEncoding_Util.mkAssume
                                           uu___9 in
                                       let t_interp2 =
                                         let a_name =
                                           Prims.strcat "interpretation_"
                                             tsym in
                                         let uu___9 =
                                           let uu___10 =
                                             let uu___11 =
                                               let uu___12 =
                                                 FStarC_SMTEncoding_Util.mkIff
                                                   (f_has_t_z, t_interp1) in
                                               ([[f_has_t_z]], (fsym ::
                                                 cvars), uu___12) in
                                             FStarC_SMTEncoding_Term.mkForall
                                               t0.FStarC_Syntax_Syntax.pos
                                               uu___11 in
                                           (uu___10,
                                             (FStar_Pervasives_Native.Some
                                                a_name),
                                             (Prims.strcat module_name
                                                (Prims.strcat "_" a_name))) in
                                         FStarC_SMTEncoding_Util.mkAssume
                                           uu___9 in
                                       let t_decls =
                                         [tdecl;
                                         k_assumption;
                                         pre_typing;
                                         t_interp2] in
                                       let uu___9 =
                                         let uu___10 =
                                           let uu___11 =
                                             let uu___12 =
                                               FStarC_SMTEncoding_Term.mk_decls
                                                 tsym tkey_hash t_decls
                                                 (FStarC_Compiler_List.op_At
                                                    decls
                                                    (FStarC_Compiler_List.op_At
                                                       decls' guard_decls)) in
                                             FStarC_Compiler_List.op_At
                                               guard_decls uu___12 in
                                           FStarC_Compiler_List.op_At decls'
                                             uu___11 in
                                         FStarC_Compiler_List.op_At decls
                                           uu___10 in
                                       (t2, uu___9)))))
                 else
                   (let tkey_hash =
                      let uu___5 =
                        encode_binders FStar_Pervasives_Native.None binders1
                          env in
                      match uu___5 with
                      | (vars, guards_l, env_bs, uu___6, uu___7) ->
                          let c1 =
                            let uu___8 =
                              let uu___9 =
                                FStarC_TypeChecker_Env.push_binders
                                  env.FStarC_SMTEncoding_Env.tcenv binders1 in
                              FStarC_TypeChecker_Env.unfold_effect_abbrev
                                uu___9 res in
                            FStarC_Syntax_Syntax.mk_Comp uu___8 in
                          let uu___8 =
                            encode_term (FStarC_Syntax_Util.comp_result c1)
                              env_bs in
                          (match uu___8 with
                           | (ct, uu___9) ->
                               let uu___10 =
                                 let uu___11 =
                                   FStarC_Syntax_Util.comp_effect_args c1 in
                                 encode_args uu___11 env_bs in
                               (match uu___10 with
                                | (effect_args, uu___11) ->
                                    let tkey =
                                      let uu___12 =
                                        let uu___13 =
                                          FStarC_SMTEncoding_Util.mk_and_l
                                            (FStarC_Compiler_List.op_At
                                               guards_l
                                               (FStarC_Compiler_List.op_At
                                                  [ct] effect_args)) in
                                        ([], vars, uu___13) in
                                      FStarC_SMTEncoding_Term.mkForall
                                        t1.FStarC_Syntax_Syntax.pos uu___12 in
                                    let tkey_hash1 =
                                      let uu___12 =
                                        let uu___13 =
                                          FStarC_SMTEncoding_Term.hash_of_term
                                            tkey in
                                        let uu___14 =
                                          let uu___15 =
                                            FStarC_Ident.string_of_lid
                                              (FStarC_Syntax_Util.comp_effect_name
                                                 c1) in
                                          Prims.strcat "@Effect=" uu___15 in
                                        Prims.strcat uu___13 uu___14 in
                                      Prims.strcat "Non_total_Tm_arrow"
                                        uu___12 in
                                    FStarC_Compiler_Util.digest_of_string
                                      tkey_hash1)) in
                    let tsym = Prims.strcat "Non_total_Tm_arrow_" tkey_hash in
                    let env0 = env in
                    let uu___5 =
                      let fvs =
                        let uu___6 = FStarC_Syntax_Free.names t0 in
                        FStarC_Class_Setlike.elems ()
                          (Obj.magic
                             (FStarC_Compiler_FlatSet.setlike_flat_set
                                FStarC_Syntax_Syntax.ord_bv))
                          (Obj.magic uu___6) in
                      let getfreeV t2 =
                        match t2.FStarC_SMTEncoding_Term.tm with
                        | FStarC_SMTEncoding_Term.FreeV fv -> fv
                        | uu___6 ->
                            failwith
                              "Impossible: getfreeV: gen_term_var should always returns a FreeV" in
                      let uu___6 =
                        FStarC_Compiler_List.fold_left
                          (fun uu___7 ->
                             fun bv ->
                               match uu___7 with
                               | (env1, decls, vars, tms, guards) ->
                                   let uu___8 =
                                     FStarC_TypeChecker_Env.lookup_bv
                                       env1.FStarC_SMTEncoding_Env.tcenv bv in
                                   (match uu___8 with
                                    | (sort, uu___9) ->
                                        let uu___10 =
                                          FStarC_SMTEncoding_Env.gen_term_var
                                            env1 bv in
                                        (match uu___10 with
                                         | (sym, smt_tm, env2) ->
                                             let fv = getfreeV smt_tm in
                                             let uu___11 =
                                               let uu___12 = norm env2 sort in
                                               encode_term_pred
                                                 FStar_Pervasives_Native.None
                                                 uu___12 env2 smt_tm in
                                             (match uu___11 with
                                              | (guard, decls') ->
                                                  (env2,
                                                    (FStarC_Compiler_List.op_At
                                                       decls' decls), (fv ::
                                                    vars), (smt_tm :: tms),
                                                    (guard :: guards))))))
                          (env, [], [], [], []) fvs in
                      (fvs, uu___6) in
                    match uu___5 with
                    | (fstar_fvs,
                       (env1, fv_decls, fv_vars, fv_tms, fv_guards)) ->
                        let fv_decls1 = FStarC_Compiler_List.rev fv_decls in
                        let fv_vars1 = FStarC_Compiler_List.rev fv_vars in
                        let fv_tms1 = FStarC_Compiler_List.rev fv_tms in
                        let fv_guards1 = FStarC_Compiler_List.rev fv_guards in
                        let arg_sorts =
                          FStarC_Compiler_List.map
                            (fun uu___6 -> FStarC_SMTEncoding_Term.Term_sort)
                            fv_tms1 in
                        let tdecl =
                          FStarC_SMTEncoding_Term.DeclFun
                            (tsym, arg_sorts,
                              FStarC_SMTEncoding_Term.Term_sort,
                              FStar_Pervasives_Native.None) in
                        let tapp =
                          FStarC_SMTEncoding_Util.mkApp (tsym, fv_tms1) in
                        let t_kinding =
                          let a_name =
                            Prims.strcat "non_total_function_typing_" tsym in
                          let axiom =
                            let uu___6 =
                              let uu___7 =
                                let uu___8 =
                                  let uu___9 =
                                    FStarC_SMTEncoding_Term.mk_HasType tapp
                                      FStarC_SMTEncoding_Term.mk_Term_type in
                                  [uu___9] in
                                [uu___8] in
                              let uu___8 =
                                let uu___9 =
                                  let uu___10 =
                                    FStarC_SMTEncoding_Util.mk_and_l
                                      fv_guards1 in
                                  let uu___11 =
                                    FStarC_SMTEncoding_Term.mk_HasType tapp
                                      FStarC_SMTEncoding_Term.mk_Term_type in
                                  (uu___10, uu___11) in
                                FStarC_SMTEncoding_Util.mkImp uu___9 in
                              (uu___7, fv_vars1, uu___8) in
                            FStarC_SMTEncoding_Term.mkForall
                              t0.FStarC_Syntax_Syntax.pos uu___6 in
                          let svars =
                            FStarC_SMTEncoding_Term.free_variables axiom in
                          let axiom1 =
                            FStarC_SMTEncoding_Term.mkForall
                              t0.FStarC_Syntax_Syntax.pos ([], svars, axiom) in
                          FStarC_SMTEncoding_Util.mkAssume
                            (axiom1,
                              (FStar_Pervasives_Native.Some
                                 "Typing for non-total arrows"), a_name) in
                        let tapp_concrete =
                          let uu___6 =
                            let uu___7 =
                              FStarC_Compiler_List.map
                                (FStarC_SMTEncoding_Env.lookup_term_var env0)
                                fstar_fvs in
                            (tsym, uu___7) in
                          FStarC_SMTEncoding_Util.mkApp uu___6 in
                        let uu___6 =
                          let uu___7 =
                            FStarC_SMTEncoding_Term.mk_decls tsym tkey_hash
                              [tdecl; t_kinding] [] in
                          FStarC_Compiler_List.op_At fv_decls1 uu___7 in
                        (tapp_concrete, uu___6)))
        | FStarC_Syntax_Syntax.Tm_refine uu___2 ->
            let uu___3 =
              let steps =
                [FStarC_TypeChecker_Env.Weak;
                FStarC_TypeChecker_Env.HNF;
                FStarC_TypeChecker_Env.EraseUniverses] in
              let uu___4 =
                normalize_refinement steps env.FStarC_SMTEncoding_Env.tcenv
                  t0 in
              match uu___4 with
              | {
                  FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_refine
                    { FStarC_Syntax_Syntax.b = x;
                      FStarC_Syntax_Syntax.phi = f;_};
                  FStarC_Syntax_Syntax.pos = uu___5;
                  FStarC_Syntax_Syntax.vars = uu___6;
                  FStarC_Syntax_Syntax.hash_code = uu___7;_} ->
                  let uu___8 =
                    let uu___9 =
                      let uu___10 = FStarC_Syntax_Syntax.mk_binder x in
                      [uu___10] in
                    FStarC_Syntax_Subst.open_term uu___9 f in
                  (match uu___8 with
                   | (b, f1) ->
                       let uu___9 =
                         let uu___10 = FStarC_Compiler_List.hd b in
                         uu___10.FStarC_Syntax_Syntax.binder_bv in
                       (uu___9, f1))
              | uu___5 -> failwith "impossible" in
            (match uu___3 with
             | (x, f) ->
                 let uu___4 = encode_term x.FStarC_Syntax_Syntax.sort env in
                 (match uu___4 with
                  | (base_t, decls) ->
                      let uu___5 = FStarC_SMTEncoding_Env.gen_term_var env x in
                      (match uu___5 with
                       | (x1, xtm, env') ->
                           let uu___6 = encode_formula f env' in
                           (match uu___6 with
                            | (refinement, decls') ->
                                let uu___7 =
                                  FStarC_SMTEncoding_Env.fresh_fvar
                                    env.FStarC_SMTEncoding_Env.current_module_name
                                    "f" FStarC_SMTEncoding_Term.Fuel_sort in
                                (match uu___7 with
                                 | (fsym, fterm) ->
                                     let tm_has_type_with_fuel =
                                       FStarC_SMTEncoding_Term.mk_HasTypeWithFuel
                                         (FStar_Pervasives_Native.Some fterm)
                                         xtm base_t in
                                     let encoding =
                                       FStarC_SMTEncoding_Util.mkAnd
                                         (tm_has_type_with_fuel, refinement) in
                                     let cvars =
                                       let uu___8 =
                                         let uu___9 =
                                           FStarC_SMTEncoding_Term.free_variables
                                             refinement in
                                         let uu___10 =
                                           FStarC_SMTEncoding_Term.free_variables
                                             tm_has_type_with_fuel in
                                         FStarC_Compiler_List.op_At uu___9
                                           uu___10 in
                                       FStarC_Compiler_Util.remove_dups
                                         FStarC_SMTEncoding_Term.fv_eq uu___8 in
                                     let cvars1 =
                                       FStarC_Compiler_List.filter
                                         (fun y ->
                                            (let uu___8 =
                                               FStarC_SMTEncoding_Term.fv_name
                                                 y in
                                             uu___8 <> x1) &&
                                              (let uu___8 =
                                                 FStarC_SMTEncoding_Term.fv_name
                                                   y in
                                               uu___8 <> fsym)) cvars in
                                     let xfv =
                                       FStarC_SMTEncoding_Term.mk_fv
                                         (x1,
                                           FStarC_SMTEncoding_Term.Term_sort) in
                                     let ffv =
                                       FStarC_SMTEncoding_Term.mk_fv
                                         (fsym,
                                           FStarC_SMTEncoding_Term.Fuel_sort) in
                                     let tkey =
                                       FStarC_SMTEncoding_Term.mkForall
                                         t0.FStarC_Syntax_Syntax.pos
                                         ([], (ffv :: xfv :: cvars1),
                                           encoding) in
                                     let tkey_hash =
                                       FStarC_SMTEncoding_Term.hash_of_term
                                         tkey in
                                     ((let uu___9 =
                                         FStarC_Compiler_Effect.op_Bang
                                           dbg_SMTEncoding in
                                       if uu___9
                                       then
                                         let uu___10 =
                                           FStarC_Class_Show.show
                                             FStarC_Syntax_Print.showable_term
                                             f in
                                         let uu___11 =
                                           FStarC_Compiler_Util.digest_of_string
                                             tkey_hash in
                                         FStarC_Compiler_Util.print3
                                           "Encoding Tm_refine %s with tkey_hash %s and digest %s\n"
                                           uu___10 tkey_hash uu___11
                                       else ());
                                      (let tsym =
                                         let uu___9 =
                                           FStarC_Compiler_Util.digest_of_string
                                             tkey_hash in
                                         Prims.strcat "Tm_refine_" uu___9 in
                                       let cvar_sorts =
                                         FStarC_Compiler_List.map
                                           FStarC_SMTEncoding_Term.fv_sort
                                           cvars1 in
                                       let tdecl =
                                         FStarC_SMTEncoding_Term.DeclFun
                                           (tsym, cvar_sorts,
                                             FStarC_SMTEncoding_Term.Term_sort,
                                             FStar_Pervasives_Native.None) in
                                       let t2 =
                                         let uu___9 =
                                           let uu___10 =
                                             FStarC_Compiler_List.map
                                               FStarC_SMTEncoding_Util.mkFreeV
                                               cvars1 in
                                           (tsym, uu___10) in
                                         FStarC_SMTEncoding_Util.mkApp uu___9 in
                                       let x_has_base_t =
                                         FStarC_SMTEncoding_Term.mk_HasType
                                           xtm base_t in
                                       let x_has_t =
                                         FStarC_SMTEncoding_Term.mk_HasTypeWithFuel
                                           (FStar_Pervasives_Native.Some
                                              fterm) xtm t2 in
                                       let t_has_kind =
                                         FStarC_SMTEncoding_Term.mk_HasType
                                           t2
                                           FStarC_SMTEncoding_Term.mk_Term_type in
                                       let t_haseq_base =
                                         FStarC_SMTEncoding_Term.mk_haseq
                                           base_t in
                                       let t_haseq_ref =
                                         FStarC_SMTEncoding_Term.mk_haseq t2 in
                                       let t_haseq =
                                         let uu___9 =
                                           let uu___10 =
                                             let uu___11 =
                                               let uu___12 =
                                                 FStarC_SMTEncoding_Util.mkIff
                                                   (t_haseq_ref,
                                                     t_haseq_base) in
                                               ([[t_haseq_ref]], cvars1,
                                                 uu___12) in
                                             FStarC_SMTEncoding_Term.mkForall
                                               t0.FStarC_Syntax_Syntax.pos
                                               uu___11 in
                                           (uu___10,
                                             (FStar_Pervasives_Native.Some
                                                (Prims.strcat "haseq for "
                                                   tsym)),
                                             (Prims.strcat "haseq" tsym)) in
                                         FStarC_SMTEncoding_Util.mkAssume
                                           uu___9 in
                                       let t_kinding =
                                         let uu___9 =
                                           let uu___10 =
                                             FStarC_SMTEncoding_Term.mkForall
                                               t0.FStarC_Syntax_Syntax.pos
                                               ([[t_has_kind]], cvars1,
                                                 t_has_kind) in
                                           (uu___10,
                                             (FStar_Pervasives_Native.Some
                                                "refinement kinding"),
                                             (Prims.strcat
                                                "refinement_kinding_" tsym)) in
                                         FStarC_SMTEncoding_Util.mkAssume
                                           uu___9 in
                                       let t_interp =
                                         let uu___9 =
                                           let uu___10 =
                                             let uu___11 =
                                               let uu___12 =
                                                 FStarC_SMTEncoding_Util.mkIff
                                                   (x_has_t, encoding) in
                                               ([[x_has_t]], (ffv :: xfv ::
                                                 cvars1), uu___12) in
                                             FStarC_SMTEncoding_Term.mkForall
                                               t0.FStarC_Syntax_Syntax.pos
                                               uu___11 in
                                           (uu___10,
                                             (FStar_Pervasives_Native.Some
                                                "refinement_interpretation"),
                                             (Prims.strcat
                                                "refinement_interpretation_"
                                                tsym)) in
                                         FStarC_SMTEncoding_Util.mkAssume
                                           uu___9 in
                                       let t_decls =
                                         [tdecl;
                                         t_kinding;
                                         t_interp;
                                         t_haseq] in
                                       let uu___9 =
                                         let uu___10 =
                                           let uu___11 =
                                             FStarC_SMTEncoding_Term.mk_decls
                                               tsym tkey_hash t_decls
                                               (FStarC_Compiler_List.op_At
                                                  decls decls') in
                                           FStarC_Compiler_List.op_At decls'
                                             uu___11 in
                                         FStarC_Compiler_List.op_At decls
                                           uu___10 in
                                       (t2, uu___9))))))))
        | FStarC_Syntax_Syntax.Tm_uvar (uv, uu___2) ->
            let ttm =
              let uu___3 =
                FStarC_Syntax_Unionfind.uvar_id
                  uv.FStarC_Syntax_Syntax.ctx_uvar_head in
              FStarC_SMTEncoding_Util.mk_Term_uvar uu___3 in
            let uu___3 =
              let uu___4 = FStarC_Syntax_Util.ctx_uvar_typ uv in
              encode_term_pred FStar_Pervasives_Native.None uu___4 env ttm in
            (match uu___3 with
             | (t_has_k, decls) ->
                 let d =
                   let uu___4 =
                     let uu___5 =
                       let uu___6 =
                         let uu___7 =
                           let uu___8 =
                             FStarC_Syntax_Unionfind.uvar_id
                               uv.FStarC_Syntax_Syntax.ctx_uvar_head in
                           FStarC_Compiler_Util.string_of_int uu___8 in
                         FStarC_Compiler_Util.format1 "uvar_typing_%s" uu___7 in
                       FStarC_SMTEncoding_Env.varops.FStarC_SMTEncoding_Env.mk_unique
                         uu___6 in
                     (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                       uu___5) in
                   FStarC_SMTEncoding_Util.mkAssume uu___4 in
                 let uu___4 =
                   let uu___5 = FStarC_SMTEncoding_Term.mk_decls_trivial [d] in
                   FStarC_Compiler_List.op_At decls uu___5 in
                 (ttm, uu___4))
        | FStarC_Syntax_Syntax.Tm_app uu___2 ->
            let uu___3 = FStarC_Syntax_Util.head_and_args t0 in
            (match uu___3 with
             | (head, args_e) ->
                 let uu___4 =
                   let uu___5 = head_redex env head in
                   if uu___5
                   then
                     let uu___6 = maybe_whnf env t0 in
                     match uu___6 with
                     | FStar_Pervasives_Native.None -> (head, args_e)
                     | FStar_Pervasives_Native.Some t2 ->
                         FStarC_Syntax_Util.head_and_args t2
                   else (head, args_e) in
                 (match uu___4 with
                  | (head1, args_e1) ->
                      let uu___5 =
                        let uu___6 =
                          let uu___7 = FStarC_Syntax_Subst.compress head1 in
                          uu___7.FStarC_Syntax_Syntax.n in
                        (uu___6, args_e1) in
                      if is_arithmetic_primitive head1 args_e1
                      then encode_arith_term env head1 args_e1
                      else
                        if is_BitVector_primitive head1 args_e1
                        then encode_BitVector_term env head1 args_e1
                        else
                          (match uu___5 with
                           | (FStarC_Syntax_Syntax.Tm_fvar fv,
                              (arg, uu___6)::[]) when
                               ((FStarC_Syntax_Syntax.fv_eq_lid fv
                                   FStarC_Parser_Const.squash_lid)
                                  ||
                                  (FStarC_Syntax_Syntax.fv_eq_lid fv
                                     FStarC_Parser_Const.auto_squash_lid))
                                 &&
                                 (let uu___7 =
                                    FStarC_Syntax_Formula.destruct_typ_as_formula
                                      arg in
                                  FStarC_Compiler_Option.isSome uu___7)
                               ->
                               let dummy =
                                 FStarC_Syntax_Syntax.new_bv
                                   FStar_Pervasives_Native.None
                                   FStarC_Syntax_Syntax.t_unit in
                               let t2 = FStarC_Syntax_Util.refine dummy arg in
                               encode_term t2 env
                           | (FStarC_Syntax_Syntax.Tm_uinst
                              ({
                                 FStarC_Syntax_Syntax.n =
                                   FStarC_Syntax_Syntax.Tm_fvar fv;
                                 FStarC_Syntax_Syntax.pos = uu___6;
                                 FStarC_Syntax_Syntax.vars = uu___7;
                                 FStarC_Syntax_Syntax.hash_code = uu___8;_},
                               uu___9),
                              (arg, uu___10)::[]) when
                               ((FStarC_Syntax_Syntax.fv_eq_lid fv
                                   FStarC_Parser_Const.squash_lid)
                                  ||
                                  (FStarC_Syntax_Syntax.fv_eq_lid fv
                                     FStarC_Parser_Const.auto_squash_lid))
                                 &&
                                 (let uu___11 =
                                    FStarC_Syntax_Formula.destruct_typ_as_formula
                                      arg in
                                  FStarC_Compiler_Option.isSome uu___11)
                               ->
                               let dummy =
                                 FStarC_Syntax_Syntax.new_bv
                                   FStar_Pervasives_Native.None
                                   FStarC_Syntax_Syntax.t_unit in
                               let t2 = FStarC_Syntax_Util.refine dummy arg in
                               encode_term t2 env
                           | (FStarC_Syntax_Syntax.Tm_fvar fv, uu___6) when
                               (Prims.op_Negation
                                  env.FStarC_SMTEncoding_Env.encoding_quantifier)
                                 &&
                                 ((FStarC_Syntax_Syntax.fv_eq_lid fv
                                     FStarC_Parser_Const.forall_lid)
                                    ||
                                    (FStarC_Syntax_Syntax.fv_eq_lid fv
                                       FStarC_Parser_Const.exists_lid))
                               -> encode_deeply_embedded_quantifier t0 env
                           | (FStarC_Syntax_Syntax.Tm_uinst
                              ({
                                 FStarC_Syntax_Syntax.n =
                                   FStarC_Syntax_Syntax.Tm_fvar fv;
                                 FStarC_Syntax_Syntax.pos = uu___6;
                                 FStarC_Syntax_Syntax.vars = uu___7;
                                 FStarC_Syntax_Syntax.hash_code = uu___8;_},
                               uu___9),
                              uu___10) when
                               (Prims.op_Negation
                                  env.FStarC_SMTEncoding_Env.encoding_quantifier)
                                 &&
                                 ((FStarC_Syntax_Syntax.fv_eq_lid fv
                                     FStarC_Parser_Const.forall_lid)
                                    ||
                                    (FStarC_Syntax_Syntax.fv_eq_lid fv
                                       FStarC_Parser_Const.exists_lid))
                               -> encode_deeply_embedded_quantifier t0 env
                           | (FStarC_Syntax_Syntax.Tm_constant
                              (FStarC_Const.Const_range_of),
                              (arg, uu___6)::[]) ->
                               encode_const
                                 (FStarC_Const.Const_range
                                    (arg.FStarC_Syntax_Syntax.pos)) env
                           | (FStarC_Syntax_Syntax.Tm_constant
                              (FStarC_Const.Const_set_range_of),
                              (arg, uu___6)::(rng, uu___7)::[]) ->
                               encode_term arg env
                           | (FStarC_Syntax_Syntax.Tm_constant
                              (FStarC_Const.Const_reify lopt), uu___6) ->
                               let fallback uu___7 =
                                 let f =
                                   FStarC_SMTEncoding_Env.varops.FStarC_SMTEncoding_Env.fresh
                                     env.FStarC_SMTEncoding_Env.current_module_name
                                     "Tm_reify" in
                                 let decl =
                                   FStarC_SMTEncoding_Term.DeclFun
                                     (f, [],
                                       FStarC_SMTEncoding_Term.Term_sort,
                                       (FStar_Pervasives_Native.Some
                                          "Imprecise reify")) in
                                 let uu___8 =
                                   let uu___9 =
                                     FStarC_SMTEncoding_Term.mk_fv
                                       (f, FStarC_SMTEncoding_Term.Term_sort) in
                                   FStarC_SMTEncoding_Util.mkFreeV uu___9 in
                                 let uu___9 =
                                   FStarC_SMTEncoding_Term.mk_decls_trivial
                                     [decl] in
                                 (uu___8, uu___9) in
                               (match lopt with
                                | FStar_Pervasives_Native.None -> fallback ()
                                | FStar_Pervasives_Native.Some l when
                                    let uu___7 =
                                      FStarC_TypeChecker_Env.norm_eff_name
                                        env.FStarC_SMTEncoding_Env.tcenv l in
                                    FStarC_TypeChecker_Env.is_layered_effect
                                      env.FStarC_SMTEncoding_Env.tcenv uu___7
                                    -> fallback ()
                                | uu___7 ->
                                    let e0 =
                                      let uu___8 =
                                        let uu___9 =
                                          let uu___10 =
                                            FStarC_Compiler_List.hd args_e1 in
                                          FStar_Pervasives_Native.fst uu___10 in
                                        FStarC_Syntax_Util.mk_reify uu___9
                                          lopt in
                                      FStarC_TypeChecker_Util.norm_reify
                                        env.FStarC_SMTEncoding_Env.tcenv []
                                        uu___8 in
                                    ((let uu___9 =
                                        FStarC_Compiler_Effect.op_Bang
                                          dbg_SMTEncodingReify in
                                      if uu___9
                                      then
                                        let uu___10 =
                                          FStarC_Class_Show.show
                                            FStarC_Syntax_Print.showable_term
                                            e0 in
                                        FStarC_Compiler_Util.print1
                                          "Result of normalization %s\n"
                                          uu___10
                                      else ());
                                     (let e =
                                        let uu___9 =
                                          FStarC_TypeChecker_Util.remove_reify
                                            e0 in
                                        let uu___10 =
                                          FStarC_Compiler_List.tl args_e1 in
                                        FStarC_Syntax_Syntax.mk_Tm_app uu___9
                                          uu___10 t0.FStarC_Syntax_Syntax.pos in
                                      encode_term e env)))
                           | (FStarC_Syntax_Syntax.Tm_constant
                              (FStarC_Const.Const_reflect uu___6),
                              (arg, uu___7)::[]) -> encode_term arg env
                           | (FStarC_Syntax_Syntax.Tm_fvar fv,
                              uu___6::(phi, uu___7)::[]) when
                               FStarC_Syntax_Syntax.fv_eq_lid fv
                                 FStarC_Parser_Const.by_tactic_lid
                               -> encode_term phi env
                           | (FStarC_Syntax_Syntax.Tm_uinst
                              ({
                                 FStarC_Syntax_Syntax.n =
                                   FStarC_Syntax_Syntax.Tm_fvar fv;
                                 FStarC_Syntax_Syntax.pos = uu___6;
                                 FStarC_Syntax_Syntax.vars = uu___7;
                                 FStarC_Syntax_Syntax.hash_code = uu___8;_},
                               uu___9),
                              uu___10::(phi, uu___11)::[]) when
                               FStarC_Syntax_Syntax.fv_eq_lid fv
                                 FStarC_Parser_Const.by_tactic_lid
                               -> encode_term phi env
                           | (FStarC_Syntax_Syntax.Tm_fvar fv,
                              uu___6::uu___7::(phi, uu___8)::[]) when
                               FStarC_Syntax_Syntax.fv_eq_lid fv
                                 FStarC_Parser_Const.rewrite_by_tactic_lid
                               -> encode_term phi env
                           | (FStarC_Syntax_Syntax.Tm_uinst
                              ({
                                 FStarC_Syntax_Syntax.n =
                                   FStarC_Syntax_Syntax.Tm_fvar fv;
                                 FStarC_Syntax_Syntax.pos = uu___6;
                                 FStarC_Syntax_Syntax.vars = uu___7;
                                 FStarC_Syntax_Syntax.hash_code = uu___8;_},
                               uu___9),
                              uu___10::uu___11::(phi, uu___12)::[]) when
                               FStarC_Syntax_Syntax.fv_eq_lid fv
                                 FStarC_Parser_Const.rewrite_by_tactic_lid
                               -> encode_term phi env
                           | uu___6 ->
                               let uu___7 = encode_args args_e1 env in
                               (match uu___7 with
                                | (args, decls) ->
                                    let encode_partial_app ht_opt =
                                      let uu___8 = encode_term head1 env in
                                      match uu___8 with
                                      | (smt_head, decls') ->
                                          let app_tm =
                                            mk_Apply_args smt_head args in
                                          (app_tm,
                                            (FStarC_Compiler_List.op_At decls
                                               decls')) in
                                    let encode_full_app fv =
                                      let uu___8 =
                                        FStarC_SMTEncoding_Env.lookup_free_var_sym
                                          env fv in
                                      match uu___8 with
                                      | (fname, fuel_args, arity) ->
                                          let tm =
                                            maybe_curry_app
                                              t0.FStarC_Syntax_Syntax.pos
                                              fname arity
                                              (FStarC_Compiler_List.op_At
                                                 fuel_args args) in
                                          (tm, decls) in
                                    let head2 =
                                      FStarC_Syntax_Subst.compress head1 in
                                    let head_type =
                                      match head2.FStarC_Syntax_Syntax.n with
                                      | FStarC_Syntax_Syntax.Tm_uinst
                                          ({
                                             FStarC_Syntax_Syntax.n =
                                               FStarC_Syntax_Syntax.Tm_name x;
                                             FStarC_Syntax_Syntax.pos =
                                               uu___8;
                                             FStarC_Syntax_Syntax.vars =
                                               uu___9;
                                             FStarC_Syntax_Syntax.hash_code =
                                               uu___10;_},
                                           uu___11)
                                          ->
                                          FStar_Pervasives_Native.Some
                                            (x.FStarC_Syntax_Syntax.sort)
                                      | FStarC_Syntax_Syntax.Tm_name x ->
                                          FStar_Pervasives_Native.Some
                                            (x.FStarC_Syntax_Syntax.sort)
                                      | FStarC_Syntax_Syntax.Tm_uinst
                                          ({
                                             FStarC_Syntax_Syntax.n =
                                               FStarC_Syntax_Syntax.Tm_fvar
                                               fv;
                                             FStarC_Syntax_Syntax.pos =
                                               uu___8;
                                             FStarC_Syntax_Syntax.vars =
                                               uu___9;
                                             FStarC_Syntax_Syntax.hash_code =
                                               uu___10;_},
                                           uu___11)
                                          ->
                                          let uu___12 =
                                            let uu___13 =
                                              let uu___14 =
                                                FStarC_TypeChecker_Env.lookup_lid
                                                  env.FStarC_SMTEncoding_Env.tcenv
                                                  (fv.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v in
                                              FStar_Pervasives_Native.fst
                                                uu___14 in
                                            FStar_Pervasives_Native.snd
                                              uu___13 in
                                          FStar_Pervasives_Native.Some
                                            uu___12
                                      | FStarC_Syntax_Syntax.Tm_fvar fv ->
                                          let uu___8 =
                                            let uu___9 =
                                              let uu___10 =
                                                FStarC_TypeChecker_Env.lookup_lid
                                                  env.FStarC_SMTEncoding_Env.tcenv
                                                  (fv.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v in
                                              FStar_Pervasives_Native.fst
                                                uu___10 in
                                            FStar_Pervasives_Native.snd
                                              uu___9 in
                                          FStar_Pervasives_Native.Some uu___8
                                      | FStarC_Syntax_Syntax.Tm_ascribed
                                          { FStarC_Syntax_Syntax.tm = uu___8;
                                            FStarC_Syntax_Syntax.asc =
                                              (FStar_Pervasives.Inl t2,
                                               uu___9, uu___10);
                                            FStarC_Syntax_Syntax.eff_opt =
                                              uu___11;_}
                                          -> FStar_Pervasives_Native.Some t2
                                      | FStarC_Syntax_Syntax.Tm_ascribed
                                          { FStarC_Syntax_Syntax.tm = uu___8;
                                            FStarC_Syntax_Syntax.asc =
                                              (FStar_Pervasives.Inr c,
                                               uu___9, uu___10);
                                            FStarC_Syntax_Syntax.eff_opt =
                                              uu___11;_}
                                          ->
                                          FStar_Pervasives_Native.Some
                                            (FStarC_Syntax_Util.comp_result c)
                                      | uu___8 ->
                                          FStar_Pervasives_Native.None in
                                    (match head_type with
                                     | FStar_Pervasives_Native.None ->
                                         encode_partial_app
                                           FStar_Pervasives_Native.None
                                     | FStar_Pervasives_Native.Some
                                         head_type1 ->
                                         let uu___8 =
                                           let head_type2 =
                                             let uu___9 =
                                               normalize_refinement
                                                 [FStarC_TypeChecker_Env.Weak;
                                                 FStarC_TypeChecker_Env.HNF;
                                                 FStarC_TypeChecker_Env.EraseUniverses]
                                                 env.FStarC_SMTEncoding_Env.tcenv
                                                 head_type1 in
                                             FStarC_Syntax_Util.unrefine
                                               uu___9 in
                                           let uu___9 =
                                             curried_arrow_formals_comp
                                               head_type2 in
                                           match uu___9 with
                                           | (formals, c) ->
                                               if
                                                 (FStarC_Compiler_List.length
                                                    formals)
                                                   <
                                                   (FStarC_Compiler_List.length
                                                      args)
                                               then
                                                 let head_type3 =
                                                   let uu___10 =
                                                     normalize_refinement
                                                       [FStarC_TypeChecker_Env.Weak;
                                                       FStarC_TypeChecker_Env.HNF;
                                                       FStarC_TypeChecker_Env.EraseUniverses;
                                                       FStarC_TypeChecker_Env.UnfoldUntil
                                                         FStarC_Syntax_Syntax.delta_constant]
                                                       env.FStarC_SMTEncoding_Env.tcenv
                                                       head_type2 in
                                                   FStarC_Syntax_Util.unrefine
                                                     uu___10 in
                                                 let uu___10 =
                                                   curried_arrow_formals_comp
                                                     head_type3 in
                                                 (match uu___10 with
                                                  | (formals1, c1) ->
                                                      (head_type3, formals1,
                                                        c1))
                                               else (head_type2, formals, c) in
                                         (match uu___8 with
                                          | (head_type2, formals, c) ->
                                              ((let uu___10 =
                                                  FStarC_Compiler_Effect.op_Bang
                                                    dbg_PartialApp in
                                                if uu___10
                                                then
                                                  let uu___11 =
                                                    FStarC_Class_Show.show
                                                      FStarC_Syntax_Print.showable_term
                                                      head_type2 in
                                                  let uu___12 =
                                                    FStarC_Class_Show.show
                                                      (FStarC_Class_Show.show_list
                                                         FStarC_Syntax_Print.showable_binder)
                                                      formals in
                                                  let uu___13 =
                                                    FStarC_Class_Show.show
                                                      (FStarC_Class_Show.show_list
                                                         (FStarC_Class_Show.show_tuple2
                                                            FStarC_Syntax_Print.showable_term
                                                            FStarC_Syntax_Print.showable_aqual))
                                                      args_e1 in
                                                  FStarC_Compiler_Util.print3
                                                    "Encoding partial application, head_type = %s, formals = %s, args = %s\n"
                                                    uu___11 uu___12 uu___13
                                                else ());
                                               (match head2.FStarC_Syntax_Syntax.n
                                                with
                                                | FStarC_Syntax_Syntax.Tm_uinst
                                                    ({
                                                       FStarC_Syntax_Syntax.n
                                                         =
                                                         FStarC_Syntax_Syntax.Tm_fvar
                                                         fv;
                                                       FStarC_Syntax_Syntax.pos
                                                         = uu___10;
                                                       FStarC_Syntax_Syntax.vars
                                                         = uu___11;
                                                       FStarC_Syntax_Syntax.hash_code
                                                         = uu___12;_},
                                                     uu___13)
                                                    when
                                                    (FStarC_Compiler_List.length
                                                       formals)
                                                      =
                                                      (FStarC_Compiler_List.length
                                                         args)
                                                    ->
                                                    encode_full_app
                                                      fv.FStarC_Syntax_Syntax.fv_name
                                                | FStarC_Syntax_Syntax.Tm_fvar
                                                    fv when
                                                    (FStarC_Compiler_List.length
                                                       formals)
                                                      =
                                                      (FStarC_Compiler_List.length
                                                         args)
                                                    ->
                                                    encode_full_app
                                                      fv.FStarC_Syntax_Syntax.fv_name
                                                | uu___10 ->
                                                    if
                                                      (FStarC_Compiler_List.length
                                                         formals)
                                                        >
                                                        (FStarC_Compiler_List.length
                                                           args)
                                                    then
                                                      encode_partial_app
                                                        (FStar_Pervasives_Native.Some
                                                           (head_type2,
                                                             formals, c))
                                                    else
                                                      encode_partial_app
                                                        FStar_Pervasives_Native.None))))))))
        | FStarC_Syntax_Syntax.Tm_abs
            { FStarC_Syntax_Syntax.bs = bs; FStarC_Syntax_Syntax.body = body;
              FStarC_Syntax_Syntax.rc_opt = lopt;_}
            ->
            let uu___2 = FStarC_Syntax_Subst.open_term' bs body in
            (match uu___2 with
             | (bs1, body1, opening) ->
                 let fallback uu___3 =
                   let uu___4 =
                     let fvs =
                       let uu___5 = FStarC_Syntax_Free.names t0 in
                       FStarC_Class_Setlike.elems ()
                         (Obj.magic
                            (FStarC_Compiler_FlatSet.setlike_flat_set
                               FStarC_Syntax_Syntax.ord_bv))
                         (Obj.magic uu___5) in
                     let tms =
                       FStarC_Compiler_List.map
                         (FStarC_SMTEncoding_Env.lookup_term_var env) fvs in
                     let uu___5 =
                       FStarC_Compiler_List.map
                         (fun uu___6 -> FStarC_SMTEncoding_Term.Term_sort)
                         fvs in
                     (uu___5, tms) in
                   match uu___4 with
                   | (arg_sorts, arg_terms) ->
                       let f =
                         FStarC_SMTEncoding_Env.varops.FStarC_SMTEncoding_Env.fresh
                           env.FStarC_SMTEncoding_Env.current_module_name
                           "Tm_abs" in
                       let decl =
                         FStarC_SMTEncoding_Term.DeclFun
                           (f, arg_sorts, FStarC_SMTEncoding_Term.Term_sort,
                             (FStar_Pervasives_Native.Some
                                "Imprecise function encoding")) in
                       let fv =
                         let uu___5 =
                           FStarC_SMTEncoding_Term.mk_fv
                             (f, FStarC_SMTEncoding_Term.Term_sort) in
                         FStarC_SMTEncoding_Util.mkFreeV uu___5 in
                       let fapp =
                         FStarC_SMTEncoding_Util.mkApp (f, arg_terms) in
                       let uu___5 =
                         FStarC_SMTEncoding_Term.mk_decls_trivial [decl] in
                       (fapp, uu___5) in
                 let is_impure rc =
                   let uu___3 =
                     FStarC_TypeChecker_Util.is_pure_or_ghost_effect
                       env.FStarC_SMTEncoding_Env.tcenv
                       rc.FStarC_Syntax_Syntax.residual_effect in
                   Prims.op_Negation uu___3 in
                 let codomain_eff rc =
                   let res_typ =
                     match rc.FStarC_Syntax_Syntax.residual_typ with
                     | FStar_Pervasives_Native.None ->
                         let uu___3 =
                           let uu___4 =
                             FStarC_TypeChecker_Env.get_range
                               env.FStarC_SMTEncoding_Env.tcenv in
                           FStarC_TypeChecker_Util.new_implicit_var
                             "SMTEncoding codomain" uu___4
                             env.FStarC_SMTEncoding_Env.tcenv
                             FStarC_Syntax_Util.ktype0 false in
                         (match uu___3 with | (t2, uu___4, uu___5) -> t2)
                     | FStar_Pervasives_Native.Some t2 -> t2 in
                   let uu___3 =
                     FStarC_Ident.lid_equals
                       rc.FStarC_Syntax_Syntax.residual_effect
                       FStarC_Parser_Const.effect_Tot_lid in
                   if uu___3
                   then
                     let uu___4 = FStarC_Syntax_Syntax.mk_Total res_typ in
                     FStar_Pervasives_Native.Some uu___4
                   else
                     (let uu___5 =
                        FStarC_Ident.lid_equals
                          rc.FStarC_Syntax_Syntax.residual_effect
                          FStarC_Parser_Const.effect_GTot_lid in
                      if uu___5
                      then
                        let uu___6 = FStarC_Syntax_Syntax.mk_GTotal res_typ in
                        FStar_Pervasives_Native.Some uu___6
                      else FStar_Pervasives_Native.None) in
                 (match lopt with
                  | FStar_Pervasives_Native.None ->
                      ((let uu___4 =
                          let uu___5 =
                            let uu___6 =
                              FStarC_Errors_Msg.text
                                "Losing precision when encoding a function literal:" in
                            let uu___7 =
                              FStarC_Class_PP.pp
                                FStarC_Syntax_Print.pretty_term t0 in
                            FStarC_Pprint.prefix (Prims.of_int (2))
                              Prims.int_one uu___6 uu___7 in
                          let uu___6 =
                            let uu___7 =
                              FStarC_Errors_Msg.text
                                "Unannotated abstraction in the compiler?" in
                            [uu___7] in
                          uu___5 :: uu___6 in
                        FStarC_Errors.log_issue
                          (FStarC_Syntax_Syntax.has_range_syntax ()) t0
                          FStarC_Errors_Codes.Warning_FunctionLiteralPrecisionLoss
                          ()
                          (Obj.magic
                             FStarC_Errors_Msg.is_error_message_list_doc)
                          (Obj.magic uu___4));
                       fallback ())
                  | FStar_Pervasives_Native.Some rc ->
                      let uu___3 =
                        (is_impure rc) &&
                          (let uu___4 =
                             FStarC_SMTEncoding_Util.is_smt_reifiable_rc
                               env.FStarC_SMTEncoding_Env.tcenv rc in
                           Prims.op_Negation uu___4) in
                      if uu___3
                      then fallback ()
                      else
                        (let uu___5 =
                           encode_binders FStar_Pervasives_Native.None bs1
                             env in
                         match uu___5 with
                         | (vars, guards, envbody, decls, uu___6) ->
                             let body2 =
                               let uu___7 =
                                 FStarC_SMTEncoding_Util.is_smt_reifiable_rc
                                   env.FStarC_SMTEncoding_Env.tcenv rc in
                               if uu___7
                               then
                                 let uu___8 =
                                   FStarC_Syntax_Util.mk_reify body1
                                     (FStar_Pervasives_Native.Some
                                        (rc.FStarC_Syntax_Syntax.residual_effect)) in
                                 FStarC_TypeChecker_Util.norm_reify
                                   env.FStarC_SMTEncoding_Env.tcenv [] uu___8
                               else body1 in
                             let uu___7 = encode_term body2 envbody in
                             (match uu___7 with
                              | (body3, decls') ->
                                  let is_pure =
                                    FStarC_Syntax_Util.is_pure_effect
                                      rc.FStarC_Syntax_Syntax.residual_effect in
                                  let uu___8 =
                                    let uu___9 = codomain_eff rc in
                                    match uu___9 with
                                    | FStar_Pervasives_Native.None ->
                                        (FStar_Pervasives_Native.None, [])
                                    | FStar_Pervasives_Native.Some c ->
                                        let tfun =
                                          FStarC_Syntax_Util.arrow bs1 c in
                                        let uu___10 = encode_term tfun env in
                                        (match uu___10 with
                                         | (t2, decls1) ->
                                             ((FStar_Pervasives_Native.Some
                                                 t2), decls1)) in
                                  (match uu___8 with
                                   | (arrow_t_opt, decls'') ->
                                       let key_body =
                                         let uu___9 =
                                           let uu___10 =
                                             let uu___11 =
                                               let uu___12 =
                                                 FStarC_SMTEncoding_Util.mk_and_l
                                                   guards in
                                               (uu___12, body3) in
                                             FStarC_SMTEncoding_Util.mkImp
                                               uu___11 in
                                           ([], vars, uu___10) in
                                         FStarC_SMTEncoding_Term.mkForall
                                           t0.FStarC_Syntax_Syntax.pos uu___9 in
                                       let cvars =
                                         FStarC_SMTEncoding_Term.free_variables
                                           key_body in
                                       let uu___9 =
                                         match arrow_t_opt with
                                         | FStar_Pervasives_Native.None ->
                                             (cvars, key_body)
                                         | FStar_Pervasives_Native.Some t2 ->
                                             let uu___10 =
                                               let uu___11 =
                                                 let uu___12 =
                                                   FStarC_SMTEncoding_Term.free_variables
                                                     t2 in
                                                 FStarC_Compiler_List.op_At
                                                   uu___12 cvars in
                                               FStarC_Compiler_Util.remove_dups
                                                 FStarC_SMTEncoding_Term.fv_eq
                                                 uu___11 in
                                             let uu___11 =
                                               FStarC_SMTEncoding_Util.mkAnd
                                                 (key_body, t2) in
                                             (uu___10, uu___11) in
                                       (match uu___9 with
                                        | (cvars1, key_body1) ->
                                            let tkey =
                                              FStarC_SMTEncoding_Term.mkForall
                                                t0.FStarC_Syntax_Syntax.pos
                                                ([], cvars1, key_body1) in
                                            let tkey_hash =
                                              FStarC_SMTEncoding_Term.hash_of_term
                                                tkey in
                                            ((let uu___11 =
                                                FStarC_Compiler_Effect.op_Bang
                                                  dbg_PartialApp in
                                              if uu___11
                                              then
                                                let uu___12 =
                                                  let uu___13 =
                                                    FStarC_Compiler_List.map
                                                      FStarC_SMTEncoding_Term.fv_name
                                                      vars in
                                                  FStarC_Compiler_String.concat
                                                    ", " uu___13 in
                                                let uu___13 =
                                                  FStarC_SMTEncoding_Term.print_smt_term
                                                    body3 in
                                                FStarC_Compiler_Util.print2
                                                  "Checking eta expansion of\n\tvars={%s}\n\tbody=%s\n"
                                                  uu___12 uu___13
                                              else ());
                                             (let cvar_sorts =
                                                FStarC_Compiler_List.map
                                                  FStarC_SMTEncoding_Term.fv_sort
                                                  cvars1 in
                                              let fsym =
                                                let uu___11 =
                                                  FStarC_Compiler_Util.digest_of_string
                                                    tkey_hash in
                                                Prims.strcat "Tm_abs_"
                                                  uu___11 in
                                              let fdecl =
                                                FStarC_SMTEncoding_Term.DeclFun
                                                  (fsym, cvar_sorts,
                                                    FStarC_SMTEncoding_Term.Term_sort,
                                                    FStar_Pervasives_Native.None) in
                                              let f =
                                                let uu___11 =
                                                  let uu___12 =
                                                    FStarC_Compiler_List.map
                                                      FStarC_SMTEncoding_Util.mkFreeV
                                                      cvars1 in
                                                  (fsym, uu___12) in
                                                FStarC_SMTEncoding_Util.mkApp
                                                  uu___11 in
                                              let app = mk_Apply f vars in
                                              let typing_f =
                                                match arrow_t_opt with
                                                | FStar_Pervasives_Native.None
                                                    ->
                                                    let tot_fun_ax =
                                                      let ax =
                                                        let uu___11 =
                                                          FStarC_Compiler_List.map
                                                            (fun uu___12 ->
                                                               FStarC_SMTEncoding_Util.mkTrue)
                                                            vars in
                                                        isTotFun_axioms
                                                          t0.FStarC_Syntax_Syntax.pos
                                                          f vars uu___11
                                                          is_pure in
                                                      match cvars1 with
                                                      | [] -> ax
                                                      | uu___11 ->
                                                          FStarC_SMTEncoding_Term.mkForall
                                                            t0.FStarC_Syntax_Syntax.pos
                                                            ([[f]], cvars1,
                                                              ax) in
                                                    let a_name =
                                                      Prims.strcat "tot_fun_"
                                                        fsym in
                                                    let uu___11 =
                                                      FStarC_SMTEncoding_Util.mkAssume
                                                        (tot_fun_ax,
                                                          (FStar_Pervasives_Native.Some
                                                             a_name), a_name) in
                                                    [uu___11]
                                                | FStar_Pervasives_Native.Some
                                                    t2 ->
                                                    let f_has_t =
                                                      FStarC_SMTEncoding_Term.mk_HasTypeWithFuel
                                                        FStar_Pervasives_Native.None
                                                        f t2 in
                                                    let a_name =
                                                      Prims.strcat "typing_"
                                                        fsym in
                                                    let uu___11 =
                                                      let uu___12 =
                                                        let uu___13 =
                                                          FStarC_SMTEncoding_Term.mkForall
                                                            t0.FStarC_Syntax_Syntax.pos
                                                            ([[f]], cvars1,
                                                              f_has_t) in
                                                        (uu___13,
                                                          (FStar_Pervasives_Native.Some
                                                             a_name), a_name) in
                                                      FStarC_SMTEncoding_Util.mkAssume
                                                        uu___12 in
                                                    [uu___11] in
                                              let interp_f =
                                                let a_name =
                                                  Prims.strcat
                                                    "interpretation_" fsym in
                                                let uu___11 =
                                                  let uu___12 =
                                                    let uu___13 =
                                                      let uu___14 =
                                                        FStarC_SMTEncoding_Util.mkEq
                                                          (app, body3) in
                                                      ([[app]],
                                                        (FStarC_Compiler_List.op_At
                                                           vars cvars1),
                                                        uu___14) in
                                                    FStarC_SMTEncoding_Term.mkForall
                                                      t0.FStarC_Syntax_Syntax.pos
                                                      uu___13 in
                                                  (uu___12,
                                                    (FStar_Pervasives_Native.Some
                                                       a_name), a_name) in
                                                FStarC_SMTEncoding_Util.mkAssume
                                                  uu___11 in
                                              let f_decls =
                                                FStarC_Compiler_List.op_At
                                                  (fdecl :: typing_f)
                                                  [interp_f] in
                                              let uu___11 =
                                                let uu___12 =
                                                  let uu___13 =
                                                    let uu___14 =
                                                      FStarC_SMTEncoding_Term.mk_decls
                                                        fsym tkey_hash
                                                        f_decls
                                                        (FStarC_Compiler_List.op_At
                                                           decls
                                                           (FStarC_Compiler_List.op_At
                                                              decls' decls'')) in
                                                    FStarC_Compiler_List.op_At
                                                      decls'' uu___14 in
                                                  FStarC_Compiler_List.op_At
                                                    decls' uu___13 in
                                                FStarC_Compiler_List.op_At
                                                  decls uu___12 in
                                              (f, uu___11)))))))))
        | FStarC_Syntax_Syntax.Tm_let
            {
              FStarC_Syntax_Syntax.lbs =
                (uu___2,
                 { FStarC_Syntax_Syntax.lbname = FStar_Pervasives.Inr uu___3;
                   FStarC_Syntax_Syntax.lbunivs = uu___4;
                   FStarC_Syntax_Syntax.lbtyp = uu___5;
                   FStarC_Syntax_Syntax.lbeff = uu___6;
                   FStarC_Syntax_Syntax.lbdef = uu___7;
                   FStarC_Syntax_Syntax.lbattrs = uu___8;
                   FStarC_Syntax_Syntax.lbpos = uu___9;_}::uu___10);
              FStarC_Syntax_Syntax.body1 = uu___11;_}
            -> failwith "Impossible: already handled by encoding of Sig_let"
        | FStarC_Syntax_Syntax.Tm_let
            {
              FStarC_Syntax_Syntax.lbs =
                (false,
                 { FStarC_Syntax_Syntax.lbname = FStar_Pervasives.Inl x;
                   FStarC_Syntax_Syntax.lbunivs = uu___2;
                   FStarC_Syntax_Syntax.lbtyp = t11;
                   FStarC_Syntax_Syntax.lbeff = uu___3;
                   FStarC_Syntax_Syntax.lbdef = e1;
                   FStarC_Syntax_Syntax.lbattrs = uu___4;
                   FStarC_Syntax_Syntax.lbpos = uu___5;_}::[]);
              FStarC_Syntax_Syntax.body1 = e2;_}
            -> encode_let x t11 e1 e2 env encode_term
        | FStarC_Syntax_Syntax.Tm_let
            { FStarC_Syntax_Syntax.lbs = (false, uu___2::uu___3);
              FStarC_Syntax_Syntax.body1 = uu___4;_}
            ->
            failwith "Impossible: non-recursive let with multiple bindings"
        | FStarC_Syntax_Syntax.Tm_let
            { FStarC_Syntax_Syntax.lbs = (uu___2, lbs);
              FStarC_Syntax_Syntax.body1 = uu___3;_}
            ->
            let names =
              FStarC_Compiler_List.map
                (fun lb ->
                   let uu___4 = lb in
                   match uu___4 with
                   | { FStarC_Syntax_Syntax.lbname = lbname;
                       FStarC_Syntax_Syntax.lbunivs = uu___5;
                       FStarC_Syntax_Syntax.lbtyp = uu___6;
                       FStarC_Syntax_Syntax.lbeff = uu___7;
                       FStarC_Syntax_Syntax.lbdef = uu___8;
                       FStarC_Syntax_Syntax.lbattrs = uu___9;
                       FStarC_Syntax_Syntax.lbpos = uu___10;_} ->
                       let x = FStarC_Compiler_Util.left lbname in
                       let uu___11 =
                         FStarC_Ident.string_of_id
                           x.FStarC_Syntax_Syntax.ppname in
                       let uu___12 = FStarC_Syntax_Syntax.range_of_bv x in
                       (uu___11, uu___12)) lbs in
            FStarC_Compiler_Effect.raise
              (FStarC_SMTEncoding_Env.Inner_let_rec names)
        | FStarC_Syntax_Syntax.Tm_match
            { FStarC_Syntax_Syntax.scrutinee = e;
              FStarC_Syntax_Syntax.ret_opt = uu___2;
              FStarC_Syntax_Syntax.brs = pats;
              FStarC_Syntax_Syntax.rc_opt1 = uu___3;_}
            ->
            encode_match e pats FStarC_SMTEncoding_Term.mk_Term_unit env
              encode_term))
and (encode_let :
  FStarC_Syntax_Syntax.bv ->
    FStarC_Syntax_Syntax.typ ->
      FStarC_Syntax_Syntax.term ->
        FStarC_Syntax_Syntax.term ->
          FStarC_SMTEncoding_Env.env_t ->
            (FStarC_Syntax_Syntax.term ->
               FStarC_SMTEncoding_Env.env_t ->
                 (FStarC_SMTEncoding_Term.term *
                   FStarC_SMTEncoding_Term.decls_t))
              ->
              (FStarC_SMTEncoding_Term.term *
                FStarC_SMTEncoding_Term.decls_t))
  =
  fun x ->
    fun t1 ->
      fun e1 ->
        fun e2 ->
          fun env ->
            fun encode_body ->
              let uu___ =
                let uu___1 =
                  FStarC_Syntax_Util.ascribe e1
                    ((FStar_Pervasives.Inl t1), FStar_Pervasives_Native.None,
                      false) in
                encode_term uu___1 env in
              match uu___ with
              | (ee1, decls1) ->
                  let uu___1 =
                    let uu___2 =
                      let uu___3 = FStarC_Syntax_Syntax.mk_binder x in
                      [uu___3] in
                    FStarC_Syntax_Subst.open_term uu___2 e2 in
                  (match uu___1 with
                   | (xs, e21) ->
                       let x1 =
                         let uu___2 = FStarC_Compiler_List.hd xs in
                         uu___2.FStarC_Syntax_Syntax.binder_bv in
                       let env' =
                         FStarC_SMTEncoding_Env.push_term_var env x1 ee1 in
                       let uu___2 = encode_body e21 env' in
                       (match uu___2 with
                        | (ee2, decls2) ->
                            (ee2, (FStarC_Compiler_List.op_At decls1 decls2))))
and (encode_match :
  FStarC_Syntax_Syntax.term ->
    FStarC_Syntax_Syntax.branch Prims.list ->
      FStarC_SMTEncoding_Term.term ->
        FStarC_SMTEncoding_Env.env_t ->
          (FStarC_Syntax_Syntax.term ->
             FStarC_SMTEncoding_Env.env_t ->
               (FStarC_SMTEncoding_Term.term *
                 FStarC_SMTEncoding_Term.decls_t))
            ->
            (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.decls_t))
  =
  fun e ->
    fun pats ->
      fun default_case ->
        fun env ->
          fun encode_br ->
            let uu___ =
              let uu___1 =
                let uu___2 =
                  FStarC_Syntax_Syntax.mk FStarC_Syntax_Syntax.Tm_unknown
                    FStarC_Compiler_Range_Type.dummyRange in
                FStarC_Syntax_Syntax.null_bv uu___2 in
              FStarC_SMTEncoding_Env.gen_term_var env uu___1 in
            match uu___ with
            | (scrsym, scr', env1) ->
                let uu___1 = encode_term e env1 in
                (match uu___1 with
                 | (scr, decls) ->
                     let uu___2 =
                       let encode_branch b uu___3 =
                         match uu___3 with
                         | (else_case, decls1) ->
                             let uu___4 = FStarC_Syntax_Subst.open_branch b in
                             (match uu___4 with
                              | (p, w, br) ->
                                  let uu___5 = encode_pat env1 p in
                                  (match uu___5 with
                                   | (env0, pattern1) ->
                                       let guard = pattern1.guard scr' in
                                       let projections =
                                         pattern1.projections scr' in
                                       let env2 =
                                         FStarC_Compiler_List.fold_left
                                           (fun env3 ->
                                              fun uu___6 ->
                                                match uu___6 with
                                                | (x, t) ->
                                                    FStarC_SMTEncoding_Env.push_term_var
                                                      env3 x t) env1
                                           projections in
                                       let uu___6 =
                                         match w with
                                         | FStar_Pervasives_Native.None ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu___7 = encode_term w1 env2 in
                                             (match uu___7 with
                                              | (w2, decls2) ->
                                                  let uu___8 =
                                                    let uu___9 =
                                                      let uu___10 =
                                                        let uu___11 =
                                                          let uu___12 =
                                                            FStarC_SMTEncoding_Term.boxBool
                                                              FStarC_SMTEncoding_Util.mkTrue in
                                                          (w2, uu___12) in
                                                        FStarC_SMTEncoding_Util.mkEq
                                                          uu___11 in
                                                      (guard, uu___10) in
                                                    FStarC_SMTEncoding_Util.mkAnd
                                                      uu___9 in
                                                  (uu___8, decls2)) in
                                       (match uu___6 with
                                        | (guard1, decls2) ->
                                            let uu___7 = encode_br br env2 in
                                            (match uu___7 with
                                             | (br1, decls3) ->
                                                 let uu___8 =
                                                   FStarC_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu___8,
                                                   (FStarC_Compiler_List.op_At
                                                      decls1
                                                      (FStarC_Compiler_List.op_At
                                                         decls2 decls3))))))) in
                       FStarC_Compiler_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu___2 with
                      | (match_tm, decls1) ->
                          let uu___3 =
                            let uu___4 =
                              let uu___5 =
                                let uu___6 =
                                  let uu___7 =
                                    FStarC_SMTEncoding_Term.mk_fv
                                      (scrsym,
                                        FStarC_SMTEncoding_Term.Term_sort) in
                                  (uu___7, scr) in
                                [uu___6] in
                              (uu___5, match_tm) in
                            FStarC_SMTEncoding_Term.mkLet' uu___4
                              FStarC_Compiler_Range_Type.dummyRange in
                          (uu___3, decls1)))
and (encode_pat :
  FStarC_SMTEncoding_Env.env_t ->
    FStarC_Syntax_Syntax.pat -> (FStarC_SMTEncoding_Env.env_t * pattern))
  =
  fun env ->
    fun pat ->
      (let uu___1 = FStarC_Compiler_Debug.medium () in
       if uu___1
       then
         let uu___2 =
           FStarC_Class_Show.show FStarC_Syntax_Print.showable_pat pat in
         FStarC_Compiler_Util.print1 "Encoding pattern %s\n" uu___2
       else ());
      (let uu___1 = FStarC_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu___1 with
       | (vars, pat_term) ->
           let uu___2 =
             FStarC_Compiler_List.fold_left
               (fun uu___3 ->
                  fun v ->
                    match uu___3 with
                    | (env1, vars1) ->
                        let uu___4 =
                          FStarC_SMTEncoding_Env.gen_term_var env1 v in
                        (match uu___4 with
                         | (xx, uu___5, env2) ->
                             let uu___6 =
                               let uu___7 =
                                 let uu___8 =
                                   FStarC_SMTEncoding_Term.mk_fv
                                     (xx, FStarC_SMTEncoding_Term.Term_sort) in
                                 (v, uu___8) in
                               uu___7 :: vars1 in
                             (env2, uu___6))) (env, []) vars in
           (match uu___2 with
            | (env1, vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStarC_Syntax_Syntax.v with
                  | FStarC_Syntax_Syntax.Pat_var uu___3 ->
                      FStarC_SMTEncoding_Util.mkTrue
                  | FStarC_Syntax_Syntax.Pat_dot_term uu___3 ->
                      FStarC_SMTEncoding_Util.mkTrue
                  | FStarC_Syntax_Syntax.Pat_constant c ->
                      let uu___3 = encode_const c env1 in
                      (match uu___3 with
                       | (tm, decls) ->
                           ((match decls with
                             | uu___5::uu___6 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu___5 -> ());
                            FStarC_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStarC_Syntax_Syntax.Pat_cons (f, uu___3, args) ->
                      let is_f =
                        let tc_name =
                          FStarC_TypeChecker_Env.typ_of_datacon
                            env1.FStarC_SMTEncoding_Env.tcenv
                            (f.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v in
                        let uu___4 =
                          FStarC_TypeChecker_Env.datacons_of_typ
                            env1.FStarC_SMTEncoding_Env.tcenv tc_name in
                        match uu___4 with
                        | (uu___5, uu___6::[]) ->
                            FStarC_SMTEncoding_Util.mkTrue
                        | uu___5 ->
                            FStarC_SMTEncoding_Env.mk_data_tester env1
                              (f.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStarC_Compiler_List.mapi
                          (fun i ->
                             fun uu___4 ->
                               match uu___4 with
                               | (arg, uu___5) ->
                                   let proj =
                                     FStarC_SMTEncoding_Env.primitive_projector_by_pos
                                       env1.FStarC_SMTEncoding_Env.tcenv
                                       (f.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v
                                       i in
                                   let uu___6 =
                                     FStarC_SMTEncoding_Util.mkApp
                                       (proj, [scrutinee]) in
                                   mk_guard arg uu___6) args in
                      FStarC_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStarC_Syntax_Syntax.v with
                  | FStarC_Syntax_Syntax.Pat_dot_term uu___3 -> []
                  | FStarC_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStarC_Syntax_Syntax.Pat_constant uu___3 -> []
                  | FStarC_Syntax_Syntax.Pat_cons (f, uu___3, args) ->
                      let uu___4 =
                        FStarC_Compiler_List.mapi
                          (fun i ->
                             fun uu___5 ->
                               match uu___5 with
                               | (arg, uu___6) ->
                                   let proj =
                                     FStarC_SMTEncoding_Env.primitive_projector_by_pos
                                       env1.FStarC_SMTEncoding_Env.tcenv
                                       (f.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v
                                       i in
                                   let uu___7 =
                                     FStarC_SMTEncoding_Util.mkApp
                                       (proj, [scrutinee]) in
                                   mk_projections arg uu___7) args in
                      FStarC_Compiler_List.flatten uu___4 in
                let pat_term1 uu___3 = encode_term pat_term env1 in
                let pattern1 =
                  {
                    pat_vars = vars1;
                    pat_term = pat_term1;
                    guard = (mk_guard pat);
                    projections = (mk_projections pat)
                  } in
                (env1, pattern1)))
and (encode_args :
  FStarC_Syntax_Syntax.args ->
    FStarC_SMTEncoding_Env.env_t ->
      (FStarC_SMTEncoding_Term.term Prims.list *
        FStarC_SMTEncoding_Term.decls_t))
  =
  fun l ->
    fun env ->
      let uu___ =
        FStarC_Compiler_List.fold_left
          (fun uu___1 ->
             fun uu___2 ->
               match (uu___1, uu___2) with
               | ((tms, decls), (t, uu___3)) ->
                   let uu___4 = encode_term t env in
                   (match uu___4 with
                    | (t1, decls') ->
                        ((t1 :: tms),
                          (FStarC_Compiler_List.op_At decls decls'))))
          ([], []) l in
      match uu___ with
      | (l1, decls) -> ((FStarC_Compiler_List.rev l1), decls)
and (encode_smt_patterns :
  FStarC_Syntax_Syntax.arg Prims.list Prims.list ->
    FStarC_SMTEncoding_Env.env_t ->
      (FStarC_SMTEncoding_Term.term Prims.list Prims.list *
        FStarC_SMTEncoding_Term.decls_t))
  =
  fun pats_l ->
    fun env ->
      let env1 =
        {
          FStarC_SMTEncoding_Env.bvar_bindings =
            (env.FStarC_SMTEncoding_Env.bvar_bindings);
          FStarC_SMTEncoding_Env.fvar_bindings =
            (env.FStarC_SMTEncoding_Env.fvar_bindings);
          FStarC_SMTEncoding_Env.depth = (env.FStarC_SMTEncoding_Env.depth);
          FStarC_SMTEncoding_Env.tcenv = (env.FStarC_SMTEncoding_Env.tcenv);
          FStarC_SMTEncoding_Env.warn = (env.FStarC_SMTEncoding_Env.warn);
          FStarC_SMTEncoding_Env.nolabels =
            (env.FStarC_SMTEncoding_Env.nolabels);
          FStarC_SMTEncoding_Env.use_zfuel_name = true;
          FStarC_SMTEncoding_Env.encode_non_total_function_typ =
            (env.FStarC_SMTEncoding_Env.encode_non_total_function_typ);
          FStarC_SMTEncoding_Env.current_module_name =
            (env.FStarC_SMTEncoding_Env.current_module_name);
          FStarC_SMTEncoding_Env.encoding_quantifier =
            (env.FStarC_SMTEncoding_Env.encoding_quantifier);
          FStarC_SMTEncoding_Env.global_cache =
            (env.FStarC_SMTEncoding_Env.global_cache)
        } in
      let encode_smt_pattern t =
        let uu___ = FStarC_Syntax_Util.head_and_args t in
        match uu___ with
        | (head, args) ->
            let head1 = FStarC_Syntax_Util.un_uinst head in
            (match ((head1.FStarC_Syntax_Syntax.n), args) with
             | (FStarC_Syntax_Syntax.Tm_fvar fv,
                uu___1::(x, uu___2)::(t1, uu___3)::[]) when
                 FStarC_Syntax_Syntax.fv_eq_lid fv
                   FStarC_Parser_Const.has_type_lid
                 ->
                 let uu___4 = encode_term x env1 in
                 (match uu___4 with
                  | (x1, decls) ->
                      let uu___5 = encode_term t1 env1 in
                      (match uu___5 with
                       | (t2, decls') ->
                           let uu___6 =
                             FStarC_SMTEncoding_Term.mk_HasType x1 t2 in
                           (uu___6,
                             (FStarC_Compiler_List.op_At decls decls'))))
             | uu___1 -> encode_term t env1) in
      FStarC_Compiler_List.fold_right
        (fun pats ->
           fun uu___ ->
             match uu___ with
             | (pats_l1, decls) ->
                 let uu___1 =
                   FStarC_Compiler_List.fold_right
                     (fun uu___2 ->
                        fun uu___3 ->
                          match (uu___2, uu___3) with
                          | ((p, uu___4), (pats1, decls1)) ->
                              let uu___5 = encode_smt_pattern p in
                              (match uu___5 with
                               | (t, d) ->
                                   let uu___6 =
                                     FStarC_SMTEncoding_Term.check_pattern_ok
                                       t in
                                   (match uu___6 with
                                    | FStar_Pervasives_Native.None ->
                                        ((t :: pats1),
                                          (FStarC_Compiler_List.op_At d
                                             decls1))
                                    | FStar_Pervasives_Native.Some
                                        illegal_subterm ->
                                        ((let uu___8 =
                                            let uu___9 =
                                              FStarC_Class_Show.show
                                                FStarC_Syntax_Print.showable_term
                                                p in
                                            let uu___10 =
                                              FStarC_Class_Show.show
                                                FStarC_SMTEncoding_Term.showable_smt_term
                                                illegal_subterm in
                                            FStarC_Compiler_Util.format2
                                              "Pattern %s contains illegal sub-term (%s); dropping it"
                                              uu___9 uu___10 in
                                          FStarC_Errors.log_issue
                                            (FStarC_Syntax_Syntax.has_range_syntax
                                               ()) p
                                            FStarC_Errors_Codes.Warning_SMTPatternIllFormed
                                            ()
                                            (Obj.magic
                                               FStarC_Errors_Msg.is_error_message_string)
                                            (Obj.magic uu___8));
                                         (pats1,
                                           (FStarC_Compiler_List.op_At d
                                              decls1)))))) pats ([], decls) in
                 (match uu___1 with
                  | (pats1, decls1) -> ((pats1 :: pats_l1), decls1))) pats_l
        ([], [])
and (encode_formula :
  FStarC_Syntax_Syntax.typ ->
    FStarC_SMTEncoding_Env.env_t ->
      (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.decls_t))
  =
  fun phi ->
    fun env ->
      let debug phi1 =
        let uu___ = FStarC_Compiler_Effect.op_Bang dbg_SMTEncoding in
        if uu___
        then
          let uu___1 =
            FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term phi1 in
          let uu___2 =
            FStarC_Class_Show.show FStarC_Syntax_Print.showable_term phi1 in
          FStarC_Compiler_Util.print2 "Formula (%s)  %s\n" uu___1 uu___2
        else () in
      let enc f r l =
        let uu___ =
          FStarC_Compiler_Util.fold_map
            (fun decls ->
               fun x ->
                 let uu___1 = encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu___1 with
                 | (t, decls') ->
                     ((FStarC_Compiler_List.op_At decls decls'), t)) [] l in
        match uu___ with
        | (decls, args) ->
            let uu___1 =
              let uu___2 = f args in
              {
                FStarC_SMTEncoding_Term.tm =
                  (uu___2.FStarC_SMTEncoding_Term.tm);
                FStarC_SMTEncoding_Term.freevars =
                  (uu___2.FStarC_SMTEncoding_Term.freevars);
                FStarC_SMTEncoding_Term.rng = r
              } in
            (uu___1, decls) in
      let const_op f r uu___ = let uu___1 = f r in (uu___1, []) in
      let un_op f l = let uu___ = FStarC_Compiler_List.hd l in f uu___ in
      let bin_op f uu___ =
        match uu___ with
        | t1::t2::[] -> f (t1, t2)
        | uu___1 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu___ =
          FStarC_Compiler_Util.fold_map
            (fun decls ->
               fun uu___1 ->
                 match uu___1 with
                 | (t, uu___2) ->
                     let uu___3 = encode_formula t env in
                     (match uu___3 with
                      | (phi1, decls') ->
                          ((FStarC_Compiler_List.op_At decls decls'), phi1)))
            [] l in
        match uu___ with
        | (decls, phis) ->
            let uu___1 =
              let uu___2 = f phis in
              {
                FStarC_SMTEncoding_Term.tm =
                  (uu___2.FStarC_SMTEncoding_Term.tm);
                FStarC_SMTEncoding_Term.freevars =
                  (uu___2.FStarC_SMTEncoding_Term.freevars);
                FStarC_SMTEncoding_Term.rng = r
              } in
            (uu___1, decls) in
      let eq_op r args =
        let rf =
          FStarC_Compiler_List.filter
            (fun uu___ ->
               match uu___ with
               | (a, q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        { FStarC_Syntax_Syntax.aqual_implicit = true;
                          FStarC_Syntax_Syntax.aqual_attributes = uu___1;_}
                        -> false
                    | uu___1 -> true)) args in
        if (FStarC_Compiler_List.length rf) <> (Prims.of_int (2))
        then
          let uu___ =
            FStarC_Compiler_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStarC_Compiler_List.length rf)) in
          failwith uu___
        else
          (let uu___1 = enc (bin_op FStarC_SMTEncoding_Util.mkEq) in
           uu___1 r rf) in
      let mk_imp r uu___ =
        match uu___ with
        | (lhs, uu___1)::(rhs, uu___2)::[] ->
            let uu___3 = encode_formula rhs env in
            (match uu___3 with
             | (l1, decls1) ->
                 (match l1.FStarC_SMTEncoding_Term.tm with
                  | FStarC_SMTEncoding_Term.App
                      (FStarC_SMTEncoding_Term.TrueOp, uu___4) ->
                      (l1, decls1)
                  | uu___4 ->
                      let uu___5 = encode_formula lhs env in
                      (match uu___5 with
                       | (l2, decls2) ->
                           let uu___6 =
                             FStarC_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu___6,
                             (FStarC_Compiler_List.op_At decls1 decls2)))))
        | uu___1 -> failwith "impossible" in
      let mk_ite r uu___ =
        match uu___ with
        | (guard, uu___1)::(_then, uu___2)::(_else, uu___3)::[] ->
            let uu___4 = encode_formula guard env in
            (match uu___4 with
             | (g, decls1) ->
                 let uu___5 = encode_formula _then env in
                 (match uu___5 with
                  | (t, decls2) ->
                      let uu___6 = encode_formula _else env in
                      (match uu___6 with
                       | (e, decls3) ->
                           let res =
                             FStarC_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStarC_Compiler_List.op_At decls1
                                (FStarC_Compiler_List.op_At decls2 decls3))))))
        | uu___1 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu___ =
          FStarC_Compiler_List.map FStarC_SMTEncoding_Term.unboxInt l in
        f uu___ in
      let connectives =
        let uu___ =
          let uu___1 = enc_prop_c (bin_op FStarC_SMTEncoding_Util.mkAnd) in
          (FStarC_Parser_Const.and_lid, uu___1) in
        let uu___1 =
          let uu___2 =
            let uu___3 = enc_prop_c (bin_op FStarC_SMTEncoding_Util.mkOr) in
            (FStarC_Parser_Const.or_lid, uu___3) in
          let uu___3 =
            let uu___4 =
              let uu___5 =
                let uu___6 =
                  enc_prop_c (bin_op FStarC_SMTEncoding_Util.mkIff) in
                (FStarC_Parser_Const.iff_lid, uu___6) in
              let uu___6 =
                let uu___7 =
                  let uu___8 =
                    let uu___9 =
                      enc_prop_c (un_op FStarC_SMTEncoding_Util.mkNot) in
                    (FStarC_Parser_Const.not_lid, uu___9) in
                  [uu___8;
                  (FStarC_Parser_Const.eq2_lid, eq_op);
                  (FStarC_Parser_Const.c_eq2_lid, eq_op);
                  (FStarC_Parser_Const.true_lid,
                    (const_op FStarC_SMTEncoding_Term.mkTrue));
                  (FStarC_Parser_Const.false_lid,
                    (const_op FStarC_SMTEncoding_Term.mkFalse))] in
                (FStarC_Parser_Const.ite_lid, mk_ite) :: uu___7 in
              uu___5 :: uu___6 in
            (FStarC_Parser_Const.imp_lid, mk_imp) :: uu___4 in
          uu___2 :: uu___3 in
        uu___ :: uu___1 in
      let rec fallback phi1 =
        match phi1.FStarC_Syntax_Syntax.n with
        | FStarC_Syntax_Syntax.Tm_meta
            { FStarC_Syntax_Syntax.tm2 = phi';
              FStarC_Syntax_Syntax.meta = FStarC_Syntax_Syntax.Meta_labeled
                (msg, r, b);_}
            ->
            let uu___ = encode_formula phi' env in
            (match uu___ with
             | (phi2, decls) ->
                 let uu___1 =
                   FStarC_SMTEncoding_Term.mk
                     (FStarC_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu___1, decls))
        | FStarC_Syntax_Syntax.Tm_meta uu___ ->
            let uu___1 = FStarC_Syntax_Util.unmeta phi1 in
            encode_formula uu___1 env
        | FStarC_Syntax_Syntax.Tm_match
            { FStarC_Syntax_Syntax.scrutinee = e;
              FStarC_Syntax_Syntax.ret_opt = uu___;
              FStarC_Syntax_Syntax.brs = pats;
              FStarC_Syntax_Syntax.rc_opt1 = uu___1;_}
            ->
            let uu___2 =
              encode_match e pats FStarC_SMTEncoding_Term.mkUnreachable env
                encode_formula in
            (match uu___2 with | (t, decls) -> (t, decls))
        | FStarC_Syntax_Syntax.Tm_let
            {
              FStarC_Syntax_Syntax.lbs =
                (false,
                 { FStarC_Syntax_Syntax.lbname = FStar_Pervasives.Inl x;
                   FStarC_Syntax_Syntax.lbunivs = uu___;
                   FStarC_Syntax_Syntax.lbtyp = t1;
                   FStarC_Syntax_Syntax.lbeff = uu___1;
                   FStarC_Syntax_Syntax.lbdef = e1;
                   FStarC_Syntax_Syntax.lbattrs = uu___2;
                   FStarC_Syntax_Syntax.lbpos = uu___3;_}::[]);
              FStarC_Syntax_Syntax.body1 = e2;_}
            ->
            let uu___4 = encode_let x t1 e1 e2 env encode_formula in
            (match uu___4 with | (t, decls) -> (t, decls))
        | FStarC_Syntax_Syntax.Tm_app
            { FStarC_Syntax_Syntax.hd = head;
              FStarC_Syntax_Syntax.args = args;_}
            ->
            let head1 = FStarC_Syntax_Util.un_uinst head in
            (match ((head1.FStarC_Syntax_Syntax.n), args) with
             | (FStarC_Syntax_Syntax.Tm_fvar fv,
                uu___::(x, uu___1)::(t, uu___2)::[]) when
                 FStarC_Syntax_Syntax.fv_eq_lid fv
                   FStarC_Parser_Const.has_type_lid
                 ->
                 let uu___3 = encode_term x env in
                 (match uu___3 with
                  | (x1, decls) ->
                      let uu___4 = encode_term t env in
                      (match uu___4 with
                       | (t1, decls') ->
                           let uu___5 =
                             FStarC_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu___5,
                             (FStarC_Compiler_List.op_At decls decls'))))
             | (FStarC_Syntax_Syntax.Tm_fvar fv, uu___::(phi2, uu___1)::[])
                 when
                 FStarC_Syntax_Syntax.fv_eq_lid fv
                   FStarC_Parser_Const.by_tactic_lid
                 -> encode_formula phi2 env
             | (FStarC_Syntax_Syntax.Tm_uinst
                ({ FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_fvar fv;
                   FStarC_Syntax_Syntax.pos = uu___;
                   FStarC_Syntax_Syntax.vars = uu___1;
                   FStarC_Syntax_Syntax.hash_code = uu___2;_},
                 uu___3),
                uu___4::(phi2, uu___5)::[]) when
                 FStarC_Syntax_Syntax.fv_eq_lid fv
                   FStarC_Parser_Const.by_tactic_lid
                 -> encode_formula phi2 env
             | (FStarC_Syntax_Syntax.Tm_fvar fv,
                uu___::uu___1::(phi2, uu___2)::[]) when
                 FStarC_Syntax_Syntax.fv_eq_lid fv
                   FStarC_Parser_Const.rewrite_by_tactic_lid
                 -> encode_formula phi2 env
             | (FStarC_Syntax_Syntax.Tm_uinst
                ({ FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_fvar fv;
                   FStarC_Syntax_Syntax.pos = uu___;
                   FStarC_Syntax_Syntax.vars = uu___1;
                   FStarC_Syntax_Syntax.hash_code = uu___2;_},
                 uu___3),
                uu___4::uu___5::(phi2, uu___6)::[]) when
                 FStarC_Syntax_Syntax.fv_eq_lid fv
                   FStarC_Parser_Const.rewrite_by_tactic_lid
                 -> encode_formula phi2 env
             | (FStarC_Syntax_Syntax.Tm_fvar fv,
                (r, uu___)::(msg, uu___1)::(phi2, uu___2)::[]) when
                 FStarC_Syntax_Syntax.fv_eq_lid fv
                   FStarC_Parser_Const.labeled_lid
                 ->
                 let uu___3 =
                   let uu___4 =
                     FStarC_Syntax_Embeddings_Base.try_unembed
                       FStarC_Syntax_Embeddings.e_range r
                       FStarC_Syntax_Embeddings_Base.id_norm_cb in
                   let uu___5 =
                     FStarC_Syntax_Embeddings_Base.try_unembed
                       FStarC_Syntax_Embeddings.e_string msg
                       FStarC_Syntax_Embeddings_Base.id_norm_cb in
                   (uu___4, uu___5) in
                 (match uu___3 with
                  | (FStar_Pervasives_Native.Some r1,
                     FStar_Pervasives_Native.Some s) ->
                      let phi3 =
                        let uu___4 =
                          let uu___5 =
                            let uu___6 =
                              let uu___7 =
                                let uu___8 = FStarC_Errors_Msg.mkmsg s in
                                (uu___8, r1, false) in
                              FStarC_Syntax_Syntax.Meta_labeled uu___7 in
                            {
                              FStarC_Syntax_Syntax.tm2 = phi2;
                              FStarC_Syntax_Syntax.meta = uu___6
                            } in
                          FStarC_Syntax_Syntax.Tm_meta uu___5 in
                        FStarC_Syntax_Syntax.mk uu___4 r1 in
                      fallback phi3
                  | (FStar_Pervasives_Native.None,
                     FStar_Pervasives_Native.Some s) ->
                      let phi3 =
                        let uu___4 =
                          let uu___5 =
                            let uu___6 =
                              let uu___7 =
                                let uu___8 = FStarC_Errors_Msg.mkmsg s in
                                (uu___8, (phi2.FStarC_Syntax_Syntax.pos),
                                  false) in
                              FStarC_Syntax_Syntax.Meta_labeled uu___7 in
                            {
                              FStarC_Syntax_Syntax.tm2 = phi2;
                              FStarC_Syntax_Syntax.meta = uu___6
                            } in
                          FStarC_Syntax_Syntax.Tm_meta uu___5 in
                        FStarC_Syntax_Syntax.mk uu___4
                          phi2.FStarC_Syntax_Syntax.pos in
                      fallback phi3
                  | uu___4 -> fallback phi2)
             | (FStarC_Syntax_Syntax.Tm_fvar fv, (t, uu___)::[]) when
                 (FStarC_Syntax_Syntax.fv_eq_lid fv
                    FStarC_Parser_Const.squash_lid)
                   ||
                   (FStarC_Syntax_Syntax.fv_eq_lid fv
                      FStarC_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu___ ->
                 let encode_valid uu___1 =
                   let uu___2 = encode_term phi1 env in
                   match uu___2 with
                   | (tt, decls) ->
                       let tt1 =
                         let uu___3 =
                           let uu___4 =
                             FStarC_Compiler_Range_Type.use_range
                               tt.FStarC_SMTEncoding_Term.rng in
                           let uu___5 =
                             FStarC_Compiler_Range_Type.use_range
                               phi1.FStarC_Syntax_Syntax.pos in
                           FStarC_Compiler_Range_Ops.rng_included uu___4
                             uu___5 in
                         if uu___3
                         then tt
                         else
                           {
                             FStarC_SMTEncoding_Term.tm =
                               (tt.FStarC_SMTEncoding_Term.tm);
                             FStarC_SMTEncoding_Term.freevars =
                               (tt.FStarC_SMTEncoding_Term.freevars);
                             FStarC_SMTEncoding_Term.rng =
                               (phi1.FStarC_Syntax_Syntax.pos)
                           } in
                       let uu___3 = FStarC_SMTEncoding_Term.mk_Valid tt1 in
                       (uu___3, decls) in
                 let uu___1 = head_redex env head1 in
                 if uu___1
                 then
                   let uu___2 = maybe_whnf env head1 in
                   (match uu___2 with
                    | FStar_Pervasives_Native.None -> encode_valid ()
                    | FStar_Pervasives_Native.Some phi2 ->
                        encode_formula phi2 env)
                 else encode_valid ())
        | uu___ ->
            let uu___1 = encode_term phi1 env in
            (match uu___1 with
             | (tt, decls) ->
                 let tt1 =
                   let uu___2 =
                     let uu___3 =
                       FStarC_Compiler_Range_Type.use_range
                         tt.FStarC_SMTEncoding_Term.rng in
                     let uu___4 =
                       FStarC_Compiler_Range_Type.use_range
                         phi1.FStarC_Syntax_Syntax.pos in
                     FStarC_Compiler_Range_Ops.rng_included uu___3 uu___4 in
                   if uu___2
                   then tt
                   else
                     {
                       FStarC_SMTEncoding_Term.tm =
                         (tt.FStarC_SMTEncoding_Term.tm);
                       FStarC_SMTEncoding_Term.freevars =
                         (tt.FStarC_SMTEncoding_Term.freevars);
                       FStarC_SMTEncoding_Term.rng =
                         (phi1.FStarC_Syntax_Syntax.pos)
                     } in
                 let uu___2 = FStarC_SMTEncoding_Term.mk_Valid tt1 in
                 (uu___2, decls)) in
      let encode_q_body env1 bs ps body =
        let uu___ = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu___ with
        | (vars, guards, env2, decls, uu___1) ->
            let uu___2 = encode_smt_patterns ps env2 in
            (match uu___2 with
             | (pats, decls') ->
                 let uu___3 = encode_formula body env2 in
                 (match uu___3 with
                  | (body1, decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStarC_SMTEncoding_Term.tm =
                               FStarC_SMTEncoding_Term.App
                               (FStarC_SMTEncoding_Term.Var gf, p::[]);
                             FStarC_SMTEncoding_Term.freevars = uu___4;
                             FStarC_SMTEncoding_Term.rng = uu___5;_}::[])::[]
                            when
                            let uu___6 =
                              FStarC_Ident.string_of_lid
                                FStarC_Parser_Const.guard_free in
                            uu___6 = gf -> []
                        | uu___4 -> guards in
                      let uu___4 = FStarC_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu___4, body1,
                        (FStarC_Compiler_List.op_At decls
                           (FStarC_Compiler_List.op_At decls' decls''))))) in
      debug phi;
      (let phi1 = FStarC_Syntax_Util.unascribe phi in
       let uu___1 = FStarC_Syntax_Formula.destruct_typ_as_formula phi1 in
       match uu___1 with
       | FStar_Pervasives_Native.None -> fallback phi1
       | FStar_Pervasives_Native.Some (FStarC_Syntax_Formula.BaseConn
           (op, arms)) ->
           let uu___2 =
             FStarC_Compiler_List.tryFind
               (fun uu___3 ->
                  match uu___3 with
                  | (l, uu___4) -> FStarC_Ident.lid_equals op l) connectives in
           (match uu___2 with
            | FStar_Pervasives_Native.None -> fallback phi1
            | FStar_Pervasives_Native.Some (uu___3, f) ->
                f phi1.FStarC_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStarC_Syntax_Formula.QAll
           (vars, pats, body)) ->
           (FStarC_Compiler_List.iter (check_pattern_vars env vars) pats;
            (let uu___3 = encode_q_body env vars pats body in
             match uu___3 with
             | (vars1, pats1, guard, body1, decls) ->
                 let tm =
                   let uu___4 =
                     let uu___5 =
                       FStarC_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu___5) in
                   FStarC_SMTEncoding_Term.mkForall
                     phi1.FStarC_Syntax_Syntax.pos uu___4 in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStarC_Syntax_Formula.QEx
           (vars, pats, body)) ->
           (FStarC_Compiler_List.iter (check_pattern_vars env vars) pats;
            (let uu___3 = encode_q_body env vars pats body in
             match uu___3 with
             | (vars1, pats1, guard, body1, decls) ->
                 let uu___4 =
                   let uu___5 =
                     let uu___6 =
                       FStarC_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu___6) in
                   FStarC_SMTEncoding_Term.mkExists
                     phi1.FStarC_Syntax_Syntax.pos uu___5 in
                 (uu___4, decls))))
let (encode_function_type_as_formula :
  FStarC_Syntax_Syntax.typ ->
    FStarC_SMTEncoding_Env.env_t ->
      (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.decls_t))
  =
  fun t ->
    fun env ->
      let universe_of_binders binders =
        FStarC_Compiler_List.map (fun uu___ -> FStarC_Syntax_Syntax.U_zero)
          binders in
      let quant =
        FStarC_Syntax_Util.smt_lemma_as_forall t universe_of_binders in
      let env1 =
        {
          FStarC_SMTEncoding_Env.bvar_bindings =
            (env.FStarC_SMTEncoding_Env.bvar_bindings);
          FStarC_SMTEncoding_Env.fvar_bindings =
            (env.FStarC_SMTEncoding_Env.fvar_bindings);
          FStarC_SMTEncoding_Env.depth = (env.FStarC_SMTEncoding_Env.depth);
          FStarC_SMTEncoding_Env.tcenv = (env.FStarC_SMTEncoding_Env.tcenv);
          FStarC_SMTEncoding_Env.warn = (env.FStarC_SMTEncoding_Env.warn);
          FStarC_SMTEncoding_Env.nolabels =
            (env.FStarC_SMTEncoding_Env.nolabels);
          FStarC_SMTEncoding_Env.use_zfuel_name = true;
          FStarC_SMTEncoding_Env.encode_non_total_function_typ =
            (env.FStarC_SMTEncoding_Env.encode_non_total_function_typ);
          FStarC_SMTEncoding_Env.current_module_name =
            (env.FStarC_SMTEncoding_Env.current_module_name);
          FStarC_SMTEncoding_Env.encoding_quantifier =
            (env.FStarC_SMTEncoding_Env.encoding_quantifier);
          FStarC_SMTEncoding_Env.global_cache =
            (env.FStarC_SMTEncoding_Env.global_cache)
        } in
      encode_formula quant env1