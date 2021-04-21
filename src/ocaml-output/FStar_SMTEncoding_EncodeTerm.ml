open Prims
let mkForall_fuel' :
  'uuuuu .
    Prims.string ->
      FStar_Range.range ->
        'uuuuu ->
          (FStar_SMTEncoding_Term.pat Prims.list Prims.list *
            FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term) ->
            FStar_SMTEncoding_Term.term
  =
  fun mname ->
    fun r ->
      fun n ->
        fun uu___ ->
          match uu___ with
          | (pats, vars, body) ->
              let fallback uu___1 =
                FStar_SMTEncoding_Term.mkForall r (pats, vars, body) in
              let uu___1 = FStar_Options.unthrottle_inductives () in
              if uu___1
              then fallback ()
              else
                (let uu___3 =
                   FStar_SMTEncoding_Env.fresh_fvar mname "f"
                     FStar_SMTEncoding_Term.Fuel_sort in
                 match uu___3 with
                 | (fsym, fterm) ->
                     let add_fuel tms =
                       FStar_All.pipe_right tms
                         (FStar_List.map
                            (fun p ->
                               match p.FStar_SMTEncoding_Term.tm with
                               | FStar_SMTEncoding_Term.App
                                   (FStar_SMTEncoding_Term.Var "HasType",
                                    args)
                                   ->
                                   FStar_SMTEncoding_Util.mkApp
                                     ("HasTypeFuel", (fterm :: args))
                               | uu___4 -> p)) in
                     let pats1 = FStar_List.map add_fuel pats in
                     let body1 =
                       match body.FStar_SMTEncoding_Term.tm with
                       | FStar_SMTEncoding_Term.App
                           (FStar_SMTEncoding_Term.Imp, guard::body'::[]) ->
                           let guard1 =
                             match guard.FStar_SMTEncoding_Term.tm with
                             | FStar_SMTEncoding_Term.App
                                 (FStar_SMTEncoding_Term.And, guards) ->
                                 let uu___4 = add_fuel guards in
                                 FStar_SMTEncoding_Util.mk_and_l uu___4
                             | uu___4 ->
                                 let uu___5 = add_fuel [guard] in
                                 FStar_All.pipe_right uu___5 FStar_List.hd in
                           FStar_SMTEncoding_Util.mkImp (guard1, body')
                       | uu___4 -> body in
                     let vars1 =
                       let uu___4 =
                         FStar_SMTEncoding_Term.mk_fv
                           (fsym, FStar_SMTEncoding_Term.Fuel_sort) in
                       uu___4 :: vars in
                     FStar_SMTEncoding_Term.mkForall r (pats1, vars1, body1))
let (mkForall_fuel :
  Prims.string ->
    FStar_Range.range ->
      (FStar_SMTEncoding_Term.pat Prims.list Prims.list *
        FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term) ->
        FStar_SMTEncoding_Term.term)
  = fun mname -> fun r -> mkForall_fuel' mname r Prims.int_one
let (head_normal :
  FStar_SMTEncoding_Env.env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env ->
    fun t ->
      let t1 = FStar_Syntax_Util.unmeta t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow uu___ -> true
      | FStar_Syntax_Syntax.Tm_refine uu___ -> true
      | FStar_Syntax_Syntax.Tm_bvar uu___ -> true
      | FStar_Syntax_Syntax.Tm_uvar uu___ -> true
      | FStar_Syntax_Syntax.Tm_abs uu___ -> true
      | FStar_Syntax_Syntax.Tm_constant uu___ -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu___ =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu___ FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu___;
             FStar_Syntax_Syntax.vars = uu___1;_},
           uu___2)
          ->
          let uu___3 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu___3 FStar_Option.isNone
      | uu___ -> false
let (head_redex :
  FStar_SMTEncoding_Env.env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env ->
    fun t ->
      let uu___ =
        let uu___1 = FStar_Syntax_Util.un_uinst t in
        uu___1.FStar_Syntax_Syntax.n in
      match uu___ with
      | FStar_Syntax_Syntax.Tm_abs
          (uu___1, uu___2, FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___3 ->
                  match uu___3 with
                  | FStar_Syntax_Syntax.TOTAL -> true
                  | uu___4 -> false) rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu___1 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu___1 FStar_Option.isSome
      | uu___1 -> false
let (norm_with_steps :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
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
          uu___ "FStar.SMTEncoding.EncodeTerm.norm_with_steps"
let (normalize_refinement :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun steps ->
    fun env ->
      fun t ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStar_TypeChecker_Env.current_module env in
            FStar_Ident.string_of_lid uu___2 in
          FStar_Pervasives_Native.Some uu___1 in
        FStar_Profiling.profile
          (fun uu___1 ->
             FStar_TypeChecker_Normalize.normalize_refinement steps env t)
          uu___ "FStar.SMTEncoding.EncodeTerm.normalize_refinement"
let (whnf :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun t ->
      let uu___ = head_normal env t in
      if uu___
      then t
      else
        norm_with_steps
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Weak;
          FStar_TypeChecker_Env.HNF;
          FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses]
          env.FStar_SMTEncoding_Env.tcenv t
let (norm :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun t ->
      norm_with_steps
        [FStar_TypeChecker_Env.Beta;
        FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
        FStar_TypeChecker_Env.Eager_unfolding;
        FStar_TypeChecker_Env.EraseUniverses] env.FStar_SMTEncoding_Env.tcenv
        t
let (maybe_whnf :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t ->
      let t' = whnf env t in
      let uu___ = FStar_Syntax_Util.head_and_args t' in
      match uu___ with
      | (head', uu___1) ->
          let uu___2 = head_redex env head' in
          if uu___2
          then FStar_Pervasives_Native.None
          else FStar_Pervasives_Native.Some t'
let (trivial_post : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let uu___ = let uu___1 = FStar_Syntax_Syntax.null_binder t in [uu___1] in
    let uu___1 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
    FStar_Syntax_Util.abs uu___ uu___1 FStar_Pervasives_Native.None
let (mk_Apply :
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.fvs -> FStar_SMTEncoding_Term.term)
  =
  fun e ->
    fun vars ->
      FStar_All.pipe_right vars
        (FStar_List.fold_left
           (fun out ->
              fun var ->
                let uu___ = FStar_SMTEncoding_Term.fv_sort var in
                match uu___ with
                | FStar_SMTEncoding_Term.Fuel_sort ->
                    let uu___1 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu___1
                | s ->
                    let uu___1 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu___1) e)
let (mk_Apply_args :
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term)
  =
  fun e ->
    fun args ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let raise_arity_mismatch :
  'a . Prims.string -> Prims.int -> Prims.int -> FStar_Range.range -> 'a =
  fun head ->
    fun arity ->
      fun n_args ->
        fun rng ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_Util.string_of_int arity in
              let uu___3 = FStar_Util.string_of_int n_args in
              FStar_Util.format3
                "Head symbol %s expects at least %s arguments; got only %s"
                head uu___2 uu___3 in
            (FStar_Errors.Fatal_SMTEncodingArityMismatch, uu___1) in
          FStar_Errors.raise_error uu___ rng
let (isTotFun_axioms :
  FStar_Range.range ->
    FStar_SMTEncoding_Term.term ->
      FStar_SMTEncoding_Term.fvs ->
        FStar_SMTEncoding_Term.term Prims.list ->
          Prims.bool -> FStar_SMTEncoding_Term.term)
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
                  FStar_SMTEncoding_Term.mkForall pos (pat, vars1, body) in
            let rec is_tot_fun_axioms ctx ctx_guard head1 vars1 guards1 =
              match (vars1, guards1) with
              | ([], []) -> FStar_SMTEncoding_Util.mkTrue
              | (uu___::[], uu___1) ->
                  if is_pure
                  then
                    let uu___2 =
                      let uu___3 =
                        let uu___4 = FStar_SMTEncoding_Term.mk_IsTotFun head1 in
                        (ctx_guard, uu___4) in
                      FStar_SMTEncoding_Util.mkImp uu___3 in
                    maybe_mkForall [[head1]] ctx uu___2
                  else FStar_SMTEncoding_Util.mkTrue
              | (x::vars2, g_x::guards2) ->
                  let is_tot_fun_head =
                    let uu___ =
                      let uu___1 =
                        let uu___2 = FStar_SMTEncoding_Term.mk_IsTotFun head1 in
                        (ctx_guard, uu___2) in
                      FStar_SMTEncoding_Util.mkImp uu___1 in
                    maybe_mkForall [[head1]] ctx uu___ in
                  let app = mk_Apply head1 [x] in
                  let ctx1 = FStar_List.append ctx [x] in
                  let ctx_guard1 =
                    FStar_SMTEncoding_Util.mkAnd (ctx_guard, g_x) in
                  let rest =
                    is_tot_fun_axioms ctx1 ctx_guard1 app vars2 guards2 in
                  FStar_SMTEncoding_Util.mkAnd (is_tot_fun_head, rest)
              | uu___ -> failwith "impossible: isTotFun_axioms" in
            is_tot_fun_axioms [] FStar_SMTEncoding_Util.mkTrue head vars
              guards
let (maybe_curry_app :
  FStar_Range.range ->
    (FStar_SMTEncoding_Term.op, FStar_SMTEncoding_Term.term)
      FStar_Pervasives.either ->
      Prims.int ->
        FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term)
  =
  fun rng ->
    fun head ->
      fun arity ->
        fun args ->
          let n_args = FStar_List.length args in
          match head with
          | FStar_Pervasives.Inr head1 -> mk_Apply_args head1 args
          | FStar_Pervasives.Inl head1 ->
              if n_args = arity
              then FStar_SMTEncoding_Util.mkApp' (head1, args)
              else
                if n_args > arity
                then
                  (let uu___1 = FStar_Util.first_N arity args in
                   match uu___1 with
                   | (args1, rest) ->
                       let head2 =
                         FStar_SMTEncoding_Util.mkApp' (head1, args1) in
                       mk_Apply_args head2 rest)
                else
                  (let uu___2 = FStar_SMTEncoding_Term.op_to_string head1 in
                   raise_arity_mismatch uu___2 arity n_args rng)
let (maybe_curry_fvb :
  FStar_Range.range ->
    FStar_SMTEncoding_Env.fvar_binding ->
      FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term)
  =
  fun rng ->
    fun fvb ->
      fun args ->
        if fvb.FStar_SMTEncoding_Env.fvb_thunked
        then
          let uu___ = FStar_SMTEncoding_Env.force_thunk fvb in
          mk_Apply_args uu___ args
        else
          maybe_curry_app rng
            (FStar_Pervasives.Inl
               (FStar_SMTEncoding_Term.Var (fvb.FStar_SMTEncoding_Env.smt_id)))
            fvb.FStar_SMTEncoding_Env.smt_arity args
let (is_app : FStar_SMTEncoding_Term.op -> Prims.bool) =
  fun uu___ ->
    match uu___ with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu___1 -> false
let (is_an_eta_expansion :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fv Prims.list ->
      FStar_SMTEncoding_Term.term ->
        FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun env ->
    fun vars ->
      fun body ->
        let rec check_partial_applications t xs =
          match ((t.FStar_SMTEncoding_Term.tm), xs) with
          | (FStar_SMTEncoding_Term.App
             (app,
              f::{
                   FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV y;
                   FStar_SMTEncoding_Term.freevars = uu___;
                   FStar_SMTEncoding_Term.rng = uu___1;_}::[]),
             x::xs1) when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)
              -> check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var f, args),
             uu___) ->
              let uu___1 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a ->
                        fun v ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v
                          | uu___2 -> false) args (FStar_List.rev xs)) in
              if uu___1
              then
                let n = FStar_SMTEncoding_Env.tok_of_name env f in
                ((let uu___3 =
                    FStar_All.pipe_left
                      (FStar_TypeChecker_Env.debug
                         env.FStar_SMTEncoding_Env.tcenv)
                      (FStar_Options.Other "PartialApp") in
                  if uu___3
                  then
                    let uu___4 = FStar_SMTEncoding_Term.print_smt_term t in
                    let uu___5 =
                      match n with
                      | FStar_Pervasives_Native.None -> "None"
                      | FStar_Pervasives_Native.Some x ->
                          FStar_SMTEncoding_Term.print_smt_term x in
                    FStar_Util.print2
                      "is_eta_expansion %s  ... tok_of_name = %s\n" uu___4
                      uu___5
                  else ());
                 n)
              else FStar_Pervasives_Native.None
          | (uu___, []) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu___1 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv ->
                        let uu___2 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu___2)) in
              if uu___1
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu___ -> FStar_Pervasives_Native.None in
        check_partial_applications body (FStar_List.rev vars)
let check_pattern_vars :
  'uuuuu .
    FStar_SMTEncoding_Env.env_t ->
      FStar_Syntax_Syntax.binder Prims.list ->
        (FStar_Syntax_Syntax.term * 'uuuuu) Prims.list -> unit
  =
  fun env ->
    fun vars ->
      fun pats ->
        let pats1 =
          FStar_All.pipe_right pats
            (FStar_List.map
               (fun uu___ ->
                  match uu___ with
                  | (x, uu___1) ->
                      norm_with_steps
                        [FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.AllowUnboundUniverses;
                        FStar_TypeChecker_Env.EraseUniverses]
                        env.FStar_SMTEncoding_Env.tcenv x)) in
        match pats1 with
        | [] -> ()
        | hd::tl ->
            let pat_vars =
              let uu___ = FStar_Syntax_Free.names hd in
              FStar_List.fold_left
                (fun out ->
                   fun x ->
                     let uu___1 = FStar_Syntax_Free.names x in
                     FStar_Util.set_union out uu___1) uu___ tl in
            let uu___ =
              FStar_All.pipe_right vars
                (FStar_Util.find_opt
                   (fun uu___1 ->
                      match uu___1 with
                      | { FStar_Syntax_Syntax.binder_bv = b;
                          FStar_Syntax_Syntax.binder_qual = uu___2;
                          FStar_Syntax_Syntax.binder_attrs = uu___3;_} ->
                          let uu___4 = FStar_Util.set_mem b pat_vars in
                          Prims.op_Negation uu___4)) in
            (match uu___ with
             | FStar_Pervasives_Native.None -> ()
             | FStar_Pervasives_Native.Some
                 { FStar_Syntax_Syntax.binder_bv = x;
                   FStar_Syntax_Syntax.binder_qual = uu___1;
                   FStar_Syntax_Syntax.binder_attrs = uu___2;_}
                 ->
                 let pos =
                   FStar_List.fold_left
                     (fun out ->
                        fun t ->
                          FStar_Range.union_ranges out
                            t.FStar_Syntax_Syntax.pos)
                     hd.FStar_Syntax_Syntax.pos tl in
                 let uu___3 =
                   let uu___4 =
                     let uu___5 = FStar_Syntax_Print.bv_to_string x in
                     FStar_Util.format1
                       "SMT pattern misses at least one bound variable: %s"
                       uu___5 in
                   (FStar_Errors.Warning_SMTPatternIllFormed, uu___4) in
                 FStar_Errors.log_issue pos uu___3)
type label = (FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range)
type labels = label Prims.list
type pattern =
  {
  pat_vars: (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.fv) Prims.list ;
  pat_term:
    unit -> (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) ;
  guard: FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term ;
  projections:
    FStar_SMTEncoding_Term.term ->
      (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) Prims.list
    }
let (__proj__Mkpattern__item__pat_vars :
  pattern -> (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.fv) Prims.list)
  =
  fun projectee ->
    match projectee with
    | { pat_vars; pat_term; guard; projections;_} -> pat_vars
let (__proj__Mkpattern__item__pat_term :
  pattern ->
    unit -> (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun projectee ->
    match projectee with
    | { pat_vars; pat_term; guard; projections;_} -> pat_term
let (__proj__Mkpattern__item__guard :
  pattern -> FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term) =
  fun projectee ->
    match projectee with
    | { pat_vars; pat_term; guard; projections;_} -> guard
let (__proj__Mkpattern__item__projections :
  pattern ->
    FStar_SMTEncoding_Term.term ->
      (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) Prims.list)
  =
  fun projectee ->
    match projectee with
    | { pat_vars; pat_term; guard; projections;_} -> projections
let (as_function_typ :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun t0 ->
      let rec aux norm1 t =
        let t1 = FStar_Syntax_Subst.compress t in
        match t1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow uu___ -> t1
        | FStar_Syntax_Syntax.Tm_refine uu___ ->
            let uu___1 = FStar_Syntax_Util.unrefine t1 in aux true uu___1
        | uu___ ->
            if norm1
            then let uu___1 = whnf env t1 in aux false uu___1
            else
              (let uu___2 =
                 let uu___3 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu___4 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu___3 uu___4 in
               failwith uu___2) in
      aux true t0
let rec (curried_arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp))
  =
  fun k ->
    let k1 = FStar_Syntax_Subst.compress k in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
        FStar_Syntax_Subst.open_comp bs c
    | FStar_Syntax_Syntax.Tm_refine (bv, uu___) ->
        let uu___1 = curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort in
        (match uu___1 with
         | (args, res) ->
             (match args with
              | [] ->
                  let uu___2 = FStar_Syntax_Syntax.mk_Total k1 in
                  ([], uu___2)
              | uu___2 -> (args, res)))
    | uu___ -> let uu___1 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu___1)
let is_arithmetic_primitive :
  'uuuuu .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'uuuuu Prims.list -> Prims.bool
  =
  fun head ->
    fun args ->
      match ((head.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv, uu___::uu___1::[]) ->
          ((((((((((((FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.op_Addition)
                       ||
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.op_Subtraction))
                      ||
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.op_Multiply))
                     ||
                     (FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.op_Division))
                    ||
                    (FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.op_Modulus))
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.real_op_LT))
                  ||
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.real_op_LTE))
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.real_op_GT))
                ||
                (FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.real_op_GTE))
               ||
               (FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.real_op_Addition))
              ||
              (FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.real_op_Subtraction))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.real_op_Multiply))
            ||
            (FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.real_op_Division)
      | (FStar_Syntax_Syntax.Tm_fvar fv, uu___::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu___ -> false
let (isInteger : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun tm ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n, FStar_Pervasives_Native.None)) -> true
    | uu___ -> false
let (getInteger : FStar_Syntax_Syntax.term' -> Prims.int) =
  fun tm ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n, FStar_Pervasives_Native.None)) -> FStar_Util.int_of_string n
    | uu___ -> failwith "Expected an Integer term"
let is_BitVector_primitive :
  'uuuuu .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'uuuuu)
        Prims.list -> Prims.bool
  =
  fun head ->
    fun args ->
      match ((head.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv, (sz_arg, uu___)::uu___1::uu___2::[])
          ->
          (((((((((((FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.bv_and_lid)
                      ||
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.bv_xor_lid))
                     ||
                     (FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.bv_or_lid))
                    ||
                    (FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.bv_add_lid))
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.bv_sub_lid))
                  ||
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_shift_left_lid))
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_shift_right_lid))
                ||
                (FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.bv_udiv_lid))
               ||
               (FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.bv_mod_lid))
              ||
              (FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.bv_uext_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_mul_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | (FStar_Syntax_Syntax.Tm_fvar fv, (sz_arg, uu___)::uu___1::[]) ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu___ -> false
let rec (encode_const :
  FStar_Const.sconst ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun c ->
    fun env ->
      match c with
      | FStar_Const.Const_unit -> (FStar_SMTEncoding_Term.mk_Term_unit, [])
      | FStar_Const.Const_bool (true) ->
          let uu___ =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue in
          (uu___, [])
      | FStar_Const.Const_bool (false) ->
          let uu___ =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse in
          (uu___, [])
      | FStar_Const.Const_char c1 ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  let uu___4 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1) in
                  FStar_SMTEncoding_Term.boxInt uu___4 in
                [uu___3] in
              ("FStar.Char.__char_of_int", uu___2) in
            FStar_SMTEncoding_Util.mkApp uu___1 in
          (uu___, [])
      | FStar_Const.Const_int (i, FStar_Pervasives_Native.None) ->
          let uu___ =
            let uu___1 = FStar_SMTEncoding_Util.mkInteger i in
            FStar_SMTEncoding_Term.boxInt uu___1 in
          (uu___, [])
      | FStar_Const.Const_int (repr, FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.FStar_SMTEncoding_Env.tcenv).FStar_TypeChecker_Env.dsenv
              repr sw FStar_Range.dummyRange in
          encode_term syntax_term env
      | FStar_Const.Const_string (s, uu___) ->
          let uu___1 =
            let uu___2 = FStar_SMTEncoding_Util.mk_String_const s in
            FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu___2 in
          (uu___1, [])
      | FStar_Const.Const_range uu___ ->
          let uu___1 = FStar_SMTEncoding_Term.mk_Range_const () in
          (uu___1, [])
      | FStar_Const.Const_effect -> (FStar_SMTEncoding_Term.mk_Term_type, [])
      | FStar_Const.Const_real r ->
          let uu___ =
            let uu___1 = FStar_SMTEncoding_Util.mkReal r in
            FStar_SMTEncoding_Term.boxReal uu___1 in
          (uu___, [])
      | c1 ->
          let uu___ =
            let uu___1 = FStar_Syntax_Print.const_to_string c1 in
            FStar_Util.format1 "Unhandled constant: %s" uu___1 in
          failwith uu___
and (encode_binders :
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.binders ->
      FStar_SMTEncoding_Env.env_t ->
        (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term
          Prims.list * FStar_SMTEncoding_Env.env_t *
          FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list))
  =
  fun fuel_opt ->
    fun bs ->
      fun env ->
        (let uu___1 =
           FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
             FStar_Options.Medium in
         if uu___1
         then
           let uu___2 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu___2
         else ());
        (let uu___1 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu___2 ->
                   fun b ->
                     match uu___2 with
                     | (vars, guards, env1, decls, names) ->
                         let uu___3 =
                           let x = b.FStar_Syntax_Syntax.binder_bv in
                           let uu___4 =
                             FStar_SMTEncoding_Env.gen_term_var env1 x in
                           match uu___4 with
                           | (xxsym, xx, env') ->
                               let uu___5 =
                                 let uu___6 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu___6 env1 xx in
                               (match uu___5 with
                                | (guard_x_t, decls') ->
                                    let uu___6 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xxsym,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    (uu___6, guard_x_t, env', decls', x)) in
                         (match uu___3 with
                          | (v, g, env2, decls', n) ->
                              ((v :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n ::
                                names)))) ([], [], env, [], [])) in
         match uu___1 with
         | (vars, guards, env1, decls, names) ->
             ((FStar_List.rev vars), (FStar_List.rev guards), env1, decls,
               (FStar_List.rev names)))
and (encode_term_pred :
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.typ ->
      FStar_SMTEncoding_Env.env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun fuel_opt ->
    fun t ->
      fun env ->
        fun e ->
          let uu___ = encode_term t env in
          match uu___ with
          | (t1, decls) ->
              let uu___1 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu___1, decls)
and (encode_term_pred' :
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.typ ->
      FStar_SMTEncoding_Env.env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun fuel_opt ->
    fun t ->
      fun env ->
        fun e ->
          let uu___ = encode_term t env in
          match uu___ with
          | (t1, decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None ->
                   let uu___1 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu___1, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu___1 = FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu___1, decls))
and (encode_arith_term :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun env ->
    fun head ->
      fun args_e ->
        let uu___ = encode_args args_e env in
        match uu___ with
        | (arg_tms, decls) ->
            let head_fv =
              match head.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu___1 -> failwith "Impossible" in
            let unary unbox arg_tms1 =
              let uu___1 = FStar_List.hd arg_tms1 in unbox uu___1 in
            let binary unbox arg_tms1 =
              let uu___1 =
                let uu___2 = FStar_List.hd arg_tms1 in unbox uu___2 in
              let uu___2 =
                let uu___3 =
                  let uu___4 = FStar_List.tl arg_tms1 in FStar_List.hd uu___4 in
                unbox uu___3 in
              (uu___1, uu___2) in
            let mk_default uu___1 =
              let uu___2 =
                FStar_SMTEncoding_Env.lookup_free_var_sym env
                  head_fv.FStar_Syntax_Syntax.fv_name in
              match uu___2 with
              | (fname, fuel_args, arity) ->
                  let args = FStar_List.append fuel_args arg_tms in
                  maybe_curry_app head.FStar_Syntax_Syntax.pos fname arity
                    args in
            let mk_l box op mk_args ts =
              let uu___1 = FStar_Options.smtencoding_l_arith_native () in
              if uu___1
              then
                let uu___2 = let uu___3 = mk_args ts in op uu___3 in
                FStar_All.pipe_right uu___2 box
              else mk_default () in
            let mk_nl box unbox nm op ts =
              let uu___1 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu___1
              then
                let uu___2 = binary unbox ts in
                match uu___2 with
                | (t1, t2) ->
                    let uu___3 = FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu___3 box
              else
                (let uu___3 = FStar_Options.smtencoding_nl_arith_native () in
                 if uu___3
                 then
                   let uu___4 = let uu___5 = binary unbox ts in op uu___5 in
                   FStar_All.pipe_right uu___4 box
                 else mk_default ()) in
            let add box unbox =
              mk_l box FStar_SMTEncoding_Util.mkAdd (binary unbox) in
            let sub box unbox =
              mk_l box FStar_SMTEncoding_Util.mkSub (binary unbox) in
            let minus box unbox =
              mk_l box FStar_SMTEncoding_Util.mkMinus (unary unbox) in
            let mul box unbox nm =
              mk_nl box unbox nm FStar_SMTEncoding_Util.mkMul in
            let div box unbox nm =
              mk_nl box unbox nm FStar_SMTEncoding_Util.mkDiv in
            let modulus box unbox =
              mk_nl box unbox "_mod" FStar_SMTEncoding_Util.mkMod in
            let ops =
              [(FStar_Parser_Const.op_Addition,
                 (add FStar_SMTEncoding_Term.boxInt
                    FStar_SMTEncoding_Term.unboxInt));
              (FStar_Parser_Const.op_Subtraction,
                (sub FStar_SMTEncoding_Term.boxInt
                   FStar_SMTEncoding_Term.unboxInt));
              (FStar_Parser_Const.op_Multiply,
                (mul FStar_SMTEncoding_Term.boxInt
                   FStar_SMTEncoding_Term.unboxInt "_mul"));
              (FStar_Parser_Const.op_Division,
                (div FStar_SMTEncoding_Term.boxInt
                   FStar_SMTEncoding_Term.unboxInt "_div"));
              (FStar_Parser_Const.op_Modulus,
                (modulus FStar_SMTEncoding_Term.boxInt
                   FStar_SMTEncoding_Term.unboxInt));
              (FStar_Parser_Const.op_Minus,
                (minus FStar_SMTEncoding_Term.boxInt
                   FStar_SMTEncoding_Term.unboxInt));
              (FStar_Parser_Const.real_op_Addition,
                (add FStar_SMTEncoding_Term.boxReal
                   FStar_SMTEncoding_Term.unboxReal));
              (FStar_Parser_Const.real_op_Subtraction,
                (sub FStar_SMTEncoding_Term.boxReal
                   FStar_SMTEncoding_Term.unboxReal));
              (FStar_Parser_Const.real_op_Multiply,
                (mul FStar_SMTEncoding_Term.boxReal
                   FStar_SMTEncoding_Term.unboxReal "_rmul"));
              (FStar_Parser_Const.real_op_Division,
                (mk_nl FStar_SMTEncoding_Term.boxReal
                   FStar_SMTEncoding_Term.unboxReal "_rdiv"
                   FStar_SMTEncoding_Util.mkRealDiv));
              (FStar_Parser_Const.real_op_LT,
                (mk_l FStar_SMTEncoding_Term.boxBool
                   FStar_SMTEncoding_Util.mkLT
                   (binary FStar_SMTEncoding_Term.unboxReal)));
              (FStar_Parser_Const.real_op_LTE,
                (mk_l FStar_SMTEncoding_Term.boxBool
                   FStar_SMTEncoding_Util.mkLTE
                   (binary FStar_SMTEncoding_Term.unboxReal)));
              (FStar_Parser_Const.real_op_GT,
                (mk_l FStar_SMTEncoding_Term.boxBool
                   FStar_SMTEncoding_Util.mkGT
                   (binary FStar_SMTEncoding_Term.unboxReal)));
              (FStar_Parser_Const.real_op_GTE,
                (mk_l FStar_SMTEncoding_Term.boxBool
                   FStar_SMTEncoding_Util.mkGTE
                   (binary FStar_SMTEncoding_Term.unboxReal)))] in
            let uu___1 =
              let uu___2 =
                FStar_List.tryFind
                  (fun uu___3 ->
                     match uu___3 with
                     | (l, uu___4) -> FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                  ops in
              FStar_All.pipe_right uu___2 FStar_Util.must in
            (match uu___1 with
             | (uu___2, op) -> let uu___3 = op arg_tms in (uu___3, decls))
and (encode_BitVector_term :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        Prims.list ->
        (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_elt
          Prims.list))
  =
  fun env ->
    fun head ->
      fun args_e ->
        let uu___ = FStar_List.hd args_e in
        match uu___ with
        | (tm_sz, uu___1) ->
            let uu___2 = uu___ in
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz) in
            let sz_decls =
              let t_decls = FStar_SMTEncoding_Term.mkBvConstructor sz in
              FStar_SMTEncoding_Term.mk_decls "" sz_key t_decls [] in
            let uu___3 =
              match ((head.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar fv,
                 uu___4::(sz_arg, uu___5)::uu___6::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu___7 =
                    let uu___8 = FStar_List.tail args_e in
                    FStar_List.tail uu___8 in
                  let uu___8 =
                    let uu___9 = getInteger sz_arg.FStar_Syntax_Syntax.n in
                    FStar_Pervasives_Native.Some uu___9 in
                  (uu___7, uu___8)
              | (FStar_Syntax_Syntax.Tm_fvar fv,
                 uu___4::(sz_arg, uu___5)::uu___6::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu___7 =
                    let uu___8 = FStar_Syntax_Print.term_to_string sz_arg in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu___8 in
                  failwith uu___7
              | uu___4 ->
                  let uu___5 = FStar_List.tail args_e in
                  (uu___5, FStar_Pervasives_Native.None) in
            (match uu___3 with
             | (arg_tms, ext_sz) ->
                 let uu___4 = encode_args arg_tms env in
                 (match uu___4 with
                  | (arg_tms1, decls) ->
                      let head_fv =
                        match head.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu___5 -> failwith "Impossible" in
                      let unary arg_tms2 =
                        let uu___5 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu___5 in
                      let unary_arith arg_tms2 =
                        let uu___5 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxInt uu___5 in
                      let binary arg_tms2 =
                        let uu___5 =
                          let uu___6 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu___6 in
                        let uu___6 =
                          let uu___7 =
                            let uu___8 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu___8 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu___7 in
                        (uu___5, uu___6) in
                      let binary_arith arg_tms2 =
                        let uu___5 =
                          let uu___6 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu___6 in
                        let uu___6 =
                          let uu___7 =
                            let uu___8 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu___8 in
                          FStar_SMTEncoding_Term.unboxInt uu___7 in
                        (uu___5, uu___6) in
                      let mk_bv op mk_args resBox ts =
                        let uu___5 = let uu___6 = mk_args ts in op uu___6 in
                        FStar_All.pipe_right uu___5 resBox in
                      let bv_and =
                        mk_bv FStar_SMTEncoding_Util.mkBvAnd binary
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_xor =
                        mk_bv FStar_SMTEncoding_Util.mkBvXor binary
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_or =
                        mk_bv FStar_SMTEncoding_Util.mkBvOr binary
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_add =
                        mk_bv FStar_SMTEncoding_Util.mkBvAdd binary
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_sub =
                        mk_bv FStar_SMTEncoding_Util.mkBvSub binary
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_shl =
                        mk_bv (FStar_SMTEncoding_Util.mkBvShl sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_shr =
                        mk_bv (FStar_SMTEncoding_Util.mkBvShr sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_udiv =
                        mk_bv (FStar_SMTEncoding_Util.mkBvUdiv sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_mod =
                        mk_bv (FStar_SMTEncoding_Util.mkBvMod sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_mul =
                        mk_bv (FStar_SMTEncoding_Util.mkBvMul sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_ult =
                        mk_bv FStar_SMTEncoding_Util.mkBvUlt binary
                          FStar_SMTEncoding_Term.boxBool in
                      let bv_uext arg_tms2 =
                        let uu___5 =
                          let uu___6 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None ->
                                failwith "impossible" in
                          FStar_SMTEncoding_Util.mkBvUext uu___6 in
                        let uu___6 =
                          let uu___7 =
                            let uu___8 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None ->
                                  failwith "impossible" in
                            sz + uu___8 in
                          FStar_SMTEncoding_Term.boxBitVec uu___7 in
                        mk_bv uu___5 unary uu___6 arg_tms2 in
                      let to_int =
                        mk_bv FStar_SMTEncoding_Util.mkBvToNat unary
                          FStar_SMTEncoding_Term.boxInt in
                      let bv_to =
                        mk_bv (FStar_SMTEncoding_Util.mkNatToBv sz)
                          unary_arith (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let ops =
                        [(FStar_Parser_Const.bv_and_lid, bv_and);
                        (FStar_Parser_Const.bv_xor_lid, bv_xor);
                        (FStar_Parser_Const.bv_or_lid, bv_or);
                        (FStar_Parser_Const.bv_add_lid, bv_add);
                        (FStar_Parser_Const.bv_sub_lid, bv_sub);
                        (FStar_Parser_Const.bv_shift_left_lid, bv_shl);
                        (FStar_Parser_Const.bv_shift_right_lid, bv_shr);
                        (FStar_Parser_Const.bv_udiv_lid, bv_udiv);
                        (FStar_Parser_Const.bv_mod_lid, bv_mod);
                        (FStar_Parser_Const.bv_mul_lid, bv_mul);
                        (FStar_Parser_Const.bv_ult_lid, bv_ult);
                        (FStar_Parser_Const.bv_uext_lid, bv_uext);
                        (FStar_Parser_Const.bv_to_nat_lid, to_int);
                        (FStar_Parser_Const.nat_to_bv_lid, bv_to)] in
                      let uu___5 =
                        let uu___6 =
                          FStar_List.tryFind
                            (fun uu___7 ->
                               match uu___7 with
                               | (l, uu___8) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops in
                        FStar_All.pipe_right uu___6 FStar_Util.must in
                      (match uu___5 with
                       | (uu___6, op) ->
                           let uu___7 = op arg_tms1 in
                           (uu___7, (FStar_List.append sz_decls decls)))))
and (encode_deeply_embedded_quantifier :
  FStar_Syntax_Syntax.term ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t ->
    fun env ->
      let env1 =
        let uu___ = env in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth = (uu___.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv = (uu___.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn = (uu___.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name =
            (uu___.FStar_SMTEncoding_Env.use_zfuel_name);
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier = true;
          FStar_SMTEncoding_Env.global_cache =
            (uu___.FStar_SMTEncoding_Env.global_cache)
        } in
      let uu___ = encode_term t env1 in
      match uu___ with
      | (tm, decls) ->
          let vars = FStar_SMTEncoding_Term.free_variables tm in
          let valid_tm = FStar_SMTEncoding_Term.mk_Valid tm in
          let key =
            FStar_SMTEncoding_Term.mkForall t.FStar_Syntax_Syntax.pos
              ([], vars, valid_tm) in
          let tkey_hash = FStar_SMTEncoding_Term.hash_of_term key in
          (match tm.FStar_SMTEncoding_Term.tm with
           | FStar_SMTEncoding_Term.App
               (uu___1,
                {
                  FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV
                    uu___2;
                  FStar_SMTEncoding_Term.freevars = uu___3;
                  FStar_SMTEncoding_Term.rng = uu___4;_}::{
                                                            FStar_SMTEncoding_Term.tm
                                                              =
                                                              FStar_SMTEncoding_Term.FreeV
                                                              uu___5;
                                                            FStar_SMTEncoding_Term.freevars
                                                              = uu___6;
                                                            FStar_SMTEncoding_Term.rng
                                                              = uu___7;_}::[])
               ->
               (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                  (FStar_Errors.Warning_QuantifierWithoutPattern,
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
                            let uu___4 = FStar_SMTEncoding_Term.mk_Valid tm in
                            (uu___4, phi) in
                          FStar_SMTEncoding_Util.mkIff uu___3
                      | uu___3 ->
                          let uu___4 =
                            let uu___5 =
                              let uu___6 =
                                let uu___7 =
                                  FStar_SMTEncoding_Term.mk_Valid tm in
                                (uu___7, phi) in
                              FStar_SMTEncoding_Util.mkIff uu___6 in
                            ([[valid_tm]], vars, uu___5) in
                          FStar_SMTEncoding_Term.mkForall
                            t.FStar_Syntax_Syntax.pos uu___4 in
                    let ax =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 = FStar_Util.digest_of_string tkey_hash in
                          Prims.op_Hat "l_quant_interp_" uu___5 in
                        (interp,
                          (FStar_Pervasives_Native.Some
                             "Interpretation of deeply embedded quantifier"),
                          uu___4) in
                      FStar_SMTEncoding_Util.mkAssume uu___3 in
                    let uu___3 =
                      let uu___4 =
                        let uu___5 =
                          FStar_SMTEncoding_Term.mk_decls "" tkey_hash 
                            [ax] (FStar_List.append decls decls') in
                        FStar_List.append decls' uu___5 in
                      FStar_List.append decls uu___4 in
                    (tm, uu___3)))
and (encode_term :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t ->
    fun env ->
      let t1 = FStar_Syntax_Subst.compress t in
      let t0 = t1 in
      (let uu___1 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu___1
       then
         let uu___2 = FStar_Syntax_Print.tag_of_term t1 in
         let uu___3 = FStar_Syntax_Print.term_to_string t1 in
         FStar_Util.print2 "(%s)   %s\n" uu___2 uu___3
       else ());
      (match t1.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu___1 ->
           let uu___2 =
             let uu___3 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t1.FStar_Syntax_Syntax.pos in
             let uu___4 = FStar_Syntax_Print.tag_of_term t1 in
             let uu___5 = FStar_Syntax_Print.term_to_string t1 in
             FStar_Util.format3 "(%s) Impossible: %s\n%s\n" uu___3 uu___4
               uu___5 in
           failwith uu___2
       | FStar_Syntax_Syntax.Tm_unknown ->
           let uu___1 =
             let uu___2 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t1.FStar_Syntax_Syntax.pos in
             let uu___3 = FStar_Syntax_Print.tag_of_term t1 in
             let uu___4 = FStar_Syntax_Print.term_to_string t1 in
             FStar_Util.format3 "(%s) Impossible: %s\n%s\n" uu___2 uu___3
               uu___4 in
           failwith uu___1
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let e = FStar_Syntax_Util.unfold_lazy i in
           ((let uu___2 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding") in
             if uu___2
             then
               let uu___3 = FStar_Syntax_Print.term_to_string t1 in
               let uu___4 = FStar_Syntax_Print.term_to_string e in
               FStar_Util.print2 ">> Unfolded (%s) ~> (%s)\n" uu___3 uu___4
             else ());
            encode_term e env)
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu___1 =
             let uu___2 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s" uu___2 in
           failwith uu___1
       | FStar_Syntax_Syntax.Tm_ascribed (t2, (k, uu___1), uu___2) ->
           let uu___3 =
             match k with
             | FStar_Pervasives.Inl t3 -> FStar_Syntax_Util.is_unit t3
             | uu___4 -> false in
           if uu___3
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t2 env
       | FStar_Syntax_Syntax.Tm_quoted (qt, uu___1) ->
           let tv =
             let uu___2 =
               let uu___3 = FStar_Reflection_Basic.inspect_ln qt in
               FStar_Syntax_Embeddings.embed
                 FStar_Reflection_Embeddings.e_term_view uu___3 in
             uu___2 t1.FStar_Syntax_Syntax.pos FStar_Pervasives_Native.None
               FStar_Syntax_Embeddings.id_norm_cb in
           ((let uu___3 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding") in
             if uu___3
             then
               let uu___4 = FStar_Syntax_Print.term_to_string t0 in
               let uu___5 = FStar_Syntax_Print.term_to_string tv in
               FStar_Util.print2 ">> Inspected (%s) ~> (%s)\n" uu___4 uu___5
             else ());
            (let t2 =
               let uu___3 =
                 let uu___4 = FStar_Syntax_Syntax.as_arg tv in [uu___4] in
               FStar_Syntax_Util.mk_app
                 (FStar_Reflection_Data.refl_constant_term
                    FStar_Reflection_Data.fstar_refl_pack_ln) uu___3 in
             encode_term t2 env))
       | FStar_Syntax_Syntax.Tm_meta
           (t2, FStar_Syntax_Syntax.Meta_pattern uu___1) ->
           encode_term t2
             (let uu___2 = env in
              {
                FStar_SMTEncoding_Env.bvar_bindings =
                  (uu___2.FStar_SMTEncoding_Env.bvar_bindings);
                FStar_SMTEncoding_Env.fvar_bindings =
                  (uu___2.FStar_SMTEncoding_Env.fvar_bindings);
                FStar_SMTEncoding_Env.depth =
                  (uu___2.FStar_SMTEncoding_Env.depth);
                FStar_SMTEncoding_Env.tcenv =
                  (uu___2.FStar_SMTEncoding_Env.tcenv);
                FStar_SMTEncoding_Env.warn =
                  (uu___2.FStar_SMTEncoding_Env.warn);
                FStar_SMTEncoding_Env.nolabels =
                  (uu___2.FStar_SMTEncoding_Env.nolabels);
                FStar_SMTEncoding_Env.use_zfuel_name =
                  (uu___2.FStar_SMTEncoding_Env.use_zfuel_name);
                FStar_SMTEncoding_Env.encode_non_total_function_typ =
                  (uu___2.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                FStar_SMTEncoding_Env.current_module_name =
                  (uu___2.FStar_SMTEncoding_Env.current_module_name);
                FStar_SMTEncoding_Env.encoding_quantifier = false;
                FStar_SMTEncoding_Env.global_cache =
                  (uu___2.FStar_SMTEncoding_Env.global_cache)
              })
       | FStar_Syntax_Syntax.Tm_meta (t2, uu___1) -> encode_term t2 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t2 = FStar_SMTEncoding_Env.lookup_term_var env x in (t2, [])
       | FStar_Syntax_Syntax.Tm_fvar v ->
           let encode_freev uu___1 =
             let fvb =
               FStar_SMTEncoding_Env.lookup_free_var_name env
                 v.FStar_Syntax_Syntax.fv_name in
             let tok =
               FStar_SMTEncoding_Env.lookup_free_var env
                 v.FStar_Syntax_Syntax.fv_name in
             let tkey_hash = FStar_SMTEncoding_Term.hash_of_term tok in
             let uu___2 =
               if fvb.FStar_SMTEncoding_Env.smt_arity > Prims.int_zero
               then
                 match tok.FStar_SMTEncoding_Term.tm with
                 | FStar_SMTEncoding_Term.FreeV uu___3 ->
                     let sym_name =
                       let uu___4 = FStar_Util.digest_of_string tkey_hash in
                       Prims.op_Hat "@kick_partial_app_" uu___4 in
                     let uu___4 =
                       let uu___5 =
                         let uu___6 =
                           let uu___7 =
                             FStar_SMTEncoding_Term.kick_partial_app tok in
                           (uu___7,
                             (FStar_Pervasives_Native.Some "kick_partial_app"),
                             sym_name) in
                         FStar_SMTEncoding_Util.mkAssume uu___6 in
                       [uu___5] in
                     (uu___4, sym_name)
                 | FStar_SMTEncoding_Term.App (uu___3, []) ->
                     let sym_name =
                       let uu___4 = FStar_Util.digest_of_string tkey_hash in
                       Prims.op_Hat "@kick_partial_app_" uu___4 in
                     let uu___4 =
                       let uu___5 =
                         let uu___6 =
                           let uu___7 =
                             FStar_SMTEncoding_Term.kick_partial_app tok in
                           (uu___7,
                             (FStar_Pervasives_Native.Some "kick_partial_app"),
                             sym_name) in
                         FStar_SMTEncoding_Util.mkAssume uu___6 in
                       [uu___5] in
                     (uu___4, sym_name)
                 | uu___3 -> ([], "")
               else ([], "") in
             match uu___2 with
             | (aux_decls, sym_name) ->
                 let uu___3 =
                   if aux_decls = []
                   then
                     FStar_All.pipe_right []
                       FStar_SMTEncoding_Term.mk_decls_trivial
                   else
                     FStar_SMTEncoding_Term.mk_decls sym_name tkey_hash
                       aux_decls [] in
                 (tok, uu___3) in
           let uu___1 = head_redex env t1 in
           if uu___1
           then
             let uu___2 = maybe_whnf env t1 in
             (match uu___2 with
              | FStar_Pervasives_Native.None -> encode_freev ()
              | FStar_Pervasives_Native.Some t2 -> encode_term t2 env)
           else encode_freev ()
       | FStar_Syntax_Syntax.Tm_type uu___1 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t2, uu___1) -> encode_term t2 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders, c) ->
           let module_name = env.FStar_SMTEncoding_Env.current_module_name in
           let uu___1 = FStar_Syntax_Subst.open_comp binders c in
           (match uu___1 with
            | (binders1, res) ->
                let uu___2 =
                  (env.FStar_SMTEncoding_Env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu___2
                then
                  let uu___3 =
                    encode_binders FStar_Pervasives_Native.None binders1 env in
                  (match uu___3 with
                   | (vars, guards_l, env', decls, uu___4) ->
                       let fsym =
                         let uu___5 =
                           let uu___6 =
                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                               module_name "f" in
                           (uu___6, FStar_SMTEncoding_Term.Term_sort) in
                         FStar_SMTEncoding_Term.mk_fv uu___5 in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu___5 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___6 = env.FStar_SMTEncoding_Env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___6.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___6.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___6.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___6.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___6.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___6.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___6.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___6.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___6.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___6.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___6.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___6.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___6.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___6.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___6.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___6.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___6.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___6.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___6.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___6.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___6.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___6.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___6.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___6.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___6.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___6.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
                                (uu___6.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___6.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                =
                                (uu___6.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___6.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___6.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___6.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___6.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___6.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___6.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___6.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___6.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___6.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___6.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___6.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___6.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___6.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___6.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___6.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___6.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___6.FStar_TypeChecker_Env.enable_defer_to_tac);
                              FStar_TypeChecker_Env.unif_allow_ref_guards =
                                (uu___6.FStar_TypeChecker_Env.unif_allow_ref_guards)
                            }) res in
                       (match uu___5 with
                        | (pre_opt, res_t) ->
                            let uu___6 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app in
                            (match uu___6 with
                             | (res_pred, decls') ->
                                 let uu___7 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None ->
                                       let uu___8 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards_l in
                                       (uu___8, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu___8 = encode_formula pre env' in
                                       (match uu___8 with
                                        | (guard, decls0) ->
                                            let uu___9 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards_l) in
                                            (uu___9, decls0)) in
                                 (match uu___7 with
                                  | (guards, guard_decls) ->
                                      let is_pure =
                                        let uu___8 =
                                          FStar_All.pipe_right res
                                            (FStar_TypeChecker_Normalize.ghost_to_pure
                                               env.FStar_SMTEncoding_Env.tcenv) in
                                        FStar_All.pipe_right uu___8
                                          FStar_Syntax_Util.is_pure_comp in
                                      let t_interp =
                                        let uu___8 =
                                          let uu___9 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards, res_pred) in
                                          ([[app]], vars, uu___9) in
                                        FStar_SMTEncoding_Term.mkForall
                                          t1.FStar_Syntax_Syntax.pos uu___8 in
                                      let t_interp1 =
                                        let tot_fun_axioms =
                                          isTotFun_axioms
                                            t1.FStar_Syntax_Syntax.pos f vars
                                            guards_l is_pure in
                                        FStar_SMTEncoding_Util.mkAnd
                                          (t_interp, tot_fun_axioms) in
                                      let cvars =
                                        let uu___8 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp1 in
                                        FStar_All.pipe_right uu___8
                                          (FStar_List.filter
                                             (fun x ->
                                                let uu___9 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    x in
                                                let uu___10 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    fsym in
                                                uu___9 <> uu___10)) in
                                      let tkey =
                                        FStar_SMTEncoding_Term.mkForall
                                          t1.FStar_Syntax_Syntax.pos
                                          ([], (fsym :: cvars), t_interp1) in
                                      let prefix =
                                        if is_pure
                                        then "Tm_arrow_"
                                        else "Tm_ghost_arrow_" in
                                      let tkey_hash =
                                        let uu___8 =
                                          FStar_SMTEncoding_Term.hash_of_term
                                            tkey in
                                        Prims.op_Hat prefix uu___8 in
                                      let tsym =
                                        let uu___8 =
                                          FStar_Util.digest_of_string
                                            tkey_hash in
                                        Prims.op_Hat prefix uu___8 in
                                      let cvar_sorts =
                                        FStar_List.map
                                          FStar_SMTEncoding_Term.fv_sort
                                          cvars in
                                      let caption =
                                        let uu___8 =
                                          FStar_Options.log_queries () in
                                        if uu___8
                                        then
                                          let uu___9 =
                                            let uu___10 =
                                              FStar_TypeChecker_Normalize.term_to_string
                                                env.FStar_SMTEncoding_Env.tcenv
                                                t0 in
                                            FStar_Util.replace_char uu___10
                                              10 32 in
                                          FStar_Pervasives_Native.Some uu___9
                                        else FStar_Pervasives_Native.None in
                                      let tdecl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (tsym, cvar_sorts,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            caption) in
                                      let t2 =
                                        let uu___8 =
                                          let uu___9 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              cvars in
                                          (tsym, uu___9) in
                                        FStar_SMTEncoding_Util.mkApp uu___8 in
                                      let t_has_kind =
                                        FStar_SMTEncoding_Term.mk_HasType t2
                                          FStar_SMTEncoding_Term.mk_Term_type in
                                      let k_assumption =
                                        let a_name =
                                          Prims.op_Hat "kinding_" tsym in
                                        let uu___8 =
                                          let uu___9 =
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              ([[t_has_kind]], cvars,
                                                t_has_kind) in
                                          (uu___9,
                                            (FStar_Pervasives_Native.Some
                                               a_name), a_name) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu___8 in
                                      let f_has_t =
                                        FStar_SMTEncoding_Term.mk_HasType f
                                          t2 in
                                      let f_has_t_z =
                                        FStar_SMTEncoding_Term.mk_HasTypeZ f
                                          t2 in
                                      let pre_typing =
                                        let a_name =
                                          Prims.op_Hat "pre_typing_" tsym in
                                        let uu___8 =
                                          let uu___9 =
                                            let uu___10 =
                                              let uu___11 =
                                                let uu___12 =
                                                  let uu___13 =
                                                    let uu___14 =
                                                      FStar_SMTEncoding_Term.mk_PreType
                                                        f in
                                                    FStar_SMTEncoding_Term.mk_tester
                                                      "Tm_arrow" uu___14 in
                                                  (f_has_t, uu___13) in
                                                FStar_SMTEncoding_Util.mkImp
                                                  uu___12 in
                                              ([[f_has_t]], (fsym :: cvars),
                                                uu___11) in
                                            let uu___11 =
                                              mkForall_fuel module_name
                                                t0.FStar_Syntax_Syntax.pos in
                                            uu___11 uu___10 in
                                          (uu___9,
                                            (FStar_Pervasives_Native.Some
                                               "pre-typing for functions"),
                                            (Prims.op_Hat module_name
                                               (Prims.op_Hat "_" a_name))) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu___8 in
                                      let t_interp2 =
                                        let a_name =
                                          Prims.op_Hat "interpretation_" tsym in
                                        let uu___8 =
                                          let uu___9 =
                                            let uu___10 =
                                              let uu___11 =
                                                FStar_SMTEncoding_Util.mkIff
                                                  (f_has_t_z, t_interp1) in
                                              ([[f_has_t_z]], (fsym ::
                                                cvars), uu___11) in
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              uu___10 in
                                          (uu___9,
                                            (FStar_Pervasives_Native.Some
                                               a_name),
                                            (Prims.op_Hat module_name
                                               (Prims.op_Hat "_" a_name))) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu___8 in
                                      let t_decls =
                                        [tdecl;
                                        k_assumption;
                                        pre_typing;
                                        t_interp2] in
                                      let uu___8 =
                                        let uu___9 =
                                          let uu___10 =
                                            let uu___11 =
                                              FStar_SMTEncoding_Term.mk_decls
                                                tsym tkey_hash t_decls
                                                (FStar_List.append decls
                                                   (FStar_List.append decls'
                                                      guard_decls)) in
                                            FStar_List.append guard_decls
                                              uu___11 in
                                          FStar_List.append decls' uu___10 in
                                        FStar_List.append decls uu___9 in
                                      (t2, uu___8)))))
                else
                  (let tkey_hash =
                     let uu___4 =
                       encode_binders FStar_Pervasives_Native.None binders1
                         env in
                     match uu___4 with
                     | (vars, guards_l, env_bs, uu___5, uu___6) ->
                         let c1 =
                           let uu___7 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev
                               env.FStar_SMTEncoding_Env.tcenv res in
                           FStar_All.pipe_right uu___7
                             FStar_Syntax_Syntax.mk_Comp in
                         let uu___7 =
                           let uu___8 =
                             FStar_All.pipe_right c1
                               FStar_Syntax_Util.comp_result in
                           encode_term uu___8 env_bs in
                         (match uu___7 with
                          | (ct, uu___8) ->
                              let uu___9 =
                                let uu___10 =
                                  FStar_All.pipe_right c1
                                    FStar_Syntax_Util.comp_effect_args in
                                encode_args uu___10 env_bs in
                              (match uu___9 with
                               | (effect_args, uu___10) ->
                                   let tkey =
                                     let uu___11 =
                                       let uu___12 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           (FStar_List.append guards_l
                                              (FStar_List.append [ct]
                                                 effect_args)) in
                                       ([], vars, uu___12) in
                                     FStar_SMTEncoding_Term.mkForall
                                       t1.FStar_Syntax_Syntax.pos uu___11 in
                                   let tkey_hash1 =
                                     let uu___11 =
                                       let uu___12 =
                                         FStar_SMTEncoding_Term.hash_of_term
                                           tkey in
                                       let uu___13 =
                                         let uu___14 =
                                           let uu___15 =
                                             FStar_All.pipe_right c1
                                               FStar_Syntax_Util.comp_effect_name in
                                           FStar_All.pipe_right uu___15
                                             FStar_Ident.string_of_lid in
                                         Prims.op_Hat "@Effect=" uu___14 in
                                       Prims.op_Hat uu___12 uu___13 in
                                     Prims.op_Hat "Non_total_Tm_arrow"
                                       uu___11 in
                                   FStar_Util.digest_of_string tkey_hash1)) in
                   let tsym = Prims.op_Hat "Non_total_Tm_arrow_" tkey_hash in
                   let tdecl =
                     FStar_SMTEncoding_Term.DeclFun
                       (tsym, [], FStar_SMTEncoding_Term.Term_sort,
                         FStar_Pervasives_Native.None) in
                   let t2 = FStar_SMTEncoding_Util.mkApp (tsym, []) in
                   let t_kinding =
                     let a_name =
                       Prims.op_Hat "non_total_function_typing_" tsym in
                     let uu___4 =
                       let uu___5 =
                         FStar_SMTEncoding_Term.mk_HasType t2
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu___5,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"), a_name) in
                     FStar_SMTEncoding_Util.mkAssume uu___4 in
                   let fsym =
                     FStar_SMTEncoding_Term.mk_fv
                       ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t2 in
                   let t_interp =
                     let a_name = Prims.op_Hat "pre_typing_" tsym in
                     let uu___4 =
                       let uu___5 =
                         let uu___6 =
                           let uu___7 =
                             let uu___8 =
                               let uu___9 =
                                 let uu___10 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu___10 in
                               (f_has_t, uu___9) in
                             FStar_SMTEncoding_Util.mkImp uu___8 in
                           ([[f_has_t]], [fsym], uu___7) in
                         let uu___7 =
                           mkForall_fuel module_name
                             t0.FStar_Syntax_Syntax.pos in
                         uu___7 uu___6 in
                       (uu___5, (FStar_Pervasives_Native.Some a_name),
                         a_name) in
                     FStar_SMTEncoding_Util.mkAssume uu___4 in
                   let uu___4 =
                     FStar_SMTEncoding_Term.mk_decls tsym tkey_hash
                       [tdecl; t_kinding; t_interp] [] in
                   (t2, uu___4)))
       | FStar_Syntax_Syntax.Tm_refine uu___1 ->
           let uu___2 =
             let steps =
               [FStar_TypeChecker_Env.Weak;
               FStar_TypeChecker_Env.HNF;
               FStar_TypeChecker_Env.EraseUniverses] in
             let uu___3 =
               normalize_refinement steps env.FStar_SMTEncoding_Env.tcenv t0 in
             match uu___3 with
             | {
                 FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f);
                 FStar_Syntax_Syntax.pos = uu___4;
                 FStar_Syntax_Syntax.vars = uu___5;_} ->
                 let uu___6 =
                   let uu___7 =
                     let uu___8 = FStar_Syntax_Syntax.mk_binder x in [uu___8] in
                   FStar_Syntax_Subst.open_term uu___7 f in
                 (match uu___6 with
                  | (b, f1) ->
                      let uu___7 =
                        let uu___8 = FStar_List.hd b in
                        uu___8.FStar_Syntax_Syntax.binder_bv in
                      (uu___7, f1))
             | uu___4 -> failwith "impossible" in
           (match uu___2 with
            | (x, f) ->
                let uu___3 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu___3 with
                 | (base_t, decls) ->
                     let uu___4 = FStar_SMTEncoding_Env.gen_term_var env x in
                     (match uu___4 with
                      | (x1, xtm, env') ->
                          let uu___5 = encode_formula f env' in
                          (match uu___5 with
                           | (refinement, decls') ->
                               let uu___6 =
                                 FStar_SMTEncoding_Env.fresh_fvar
                                   env.FStar_SMTEncoding_Env.current_module_name
                                   "f" FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu___6 with
                                | (fsym, fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu___7 =
                                        let uu___8 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu___9 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu___8 uu___9 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq uu___7 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun y ->
                                              (let uu___7 =
                                                 FStar_SMTEncoding_Term.fv_name
                                                   y in
                                               uu___7 <> x1) &&
                                                (let uu___7 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     y in
                                                 uu___7 <> fsym))) in
                                    let xfv =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (x1,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let ffv =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (fsym,
                                          FStar_SMTEncoding_Term.Fuel_sort) in
                                    let tkey =
                                      FStar_SMTEncoding_Term.mkForall
                                        t0.FStar_Syntax_Syntax.pos
                                        ([], (ffv :: xfv :: cvars1),
                                          encoding) in
                                    let tkey_hash =
                                      FStar_SMTEncoding_Term.hash_of_term
                                        tkey in
                                    ((let uu___8 =
                                        FStar_TypeChecker_Env.debug
                                          env.FStar_SMTEncoding_Env.tcenv
                                          (FStar_Options.Other "SMTEncoding") in
                                      if uu___8
                                      then
                                        let uu___9 =
                                          FStar_Syntax_Print.term_to_string f in
                                        let uu___10 =
                                          FStar_Util.digest_of_string
                                            tkey_hash in
                                        FStar_Util.print3
                                          "Encoding Tm_refine %s with tkey_hash %s and digest %s\n"
                                          uu___9 tkey_hash uu___10
                                      else ());
                                     (let tsym =
                                        let uu___8 =
                                          FStar_Util.digest_of_string
                                            tkey_hash in
                                        Prims.op_Hat "Tm_refine_" uu___8 in
                                      let cvar_sorts =
                                        FStar_List.map
                                          FStar_SMTEncoding_Term.fv_sort
                                          cvars1 in
                                      let tdecl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (tsym, cvar_sorts,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            FStar_Pervasives_Native.None) in
                                      let t2 =
                                        let uu___8 =
                                          let uu___9 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              cvars1 in
                                          (tsym, uu___9) in
                                        FStar_SMTEncoding_Util.mkApp uu___8 in
                                      let x_has_base_t =
                                        FStar_SMTEncoding_Term.mk_HasType xtm
                                          base_t in
                                      let x_has_t =
                                        FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                          (FStar_Pervasives_Native.Some fterm)
                                          xtm t2 in
                                      let t_has_kind =
                                        FStar_SMTEncoding_Term.mk_HasType t2
                                          FStar_SMTEncoding_Term.mk_Term_type in
                                      let t_haseq_base =
                                        FStar_SMTEncoding_Term.mk_haseq
                                          base_t in
                                      let t_haseq_ref =
                                        FStar_SMTEncoding_Term.mk_haseq t2 in
                                      let t_haseq =
                                        let uu___8 =
                                          let uu___9 =
                                            let uu___10 =
                                              let uu___11 =
                                                FStar_SMTEncoding_Util.mkIff
                                                  (t_haseq_ref, t_haseq_base) in
                                              ([[t_haseq_ref]], cvars1,
                                                uu___11) in
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              uu___10 in
                                          (uu___9,
                                            (FStar_Pervasives_Native.Some
                                               (Prims.op_Hat "haseq for "
                                                  tsym)),
                                            (Prims.op_Hat "haseq" tsym)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu___8 in
                                      let t_kinding =
                                        let uu___8 =
                                          let uu___9 =
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              ([[t_has_kind]], cvars1,
                                                t_has_kind) in
                                          (uu___9,
                                            (FStar_Pervasives_Native.Some
                                               "refinement kinding"),
                                            (Prims.op_Hat
                                               "refinement_kinding_" tsym)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu___8 in
                                      let t_interp =
                                        let uu___8 =
                                          let uu___9 =
                                            let uu___10 =
                                              let uu___11 =
                                                FStar_SMTEncoding_Util.mkIff
                                                  (x_has_t, encoding) in
                                              ([[x_has_t]], (ffv :: xfv ::
                                                cvars1), uu___11) in
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              uu___10 in
                                          (uu___9,
                                            (FStar_Pervasives_Native.Some
                                               "refinement_interpretation"),
                                            (Prims.op_Hat
                                               "refinement_interpretation_"
                                               tsym)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu___8 in
                                      let t_decls =
                                        [tdecl; t_kinding; t_interp; t_haseq] in
                                      let uu___8 =
                                        let uu___9 =
                                          let uu___10 =
                                            FStar_SMTEncoding_Term.mk_decls
                                              tsym tkey_hash t_decls
                                              (FStar_List.append decls decls') in
                                          FStar_List.append decls' uu___10 in
                                        FStar_List.append decls uu___9 in
                                      (t2, uu___8))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv, uu___1) ->
           let ttm =
             let uu___2 =
               FStar_Syntax_Unionfind.uvar_id
                 uv.FStar_Syntax_Syntax.ctx_uvar_head in
             FStar_SMTEncoding_Util.mk_Term_uvar uu___2 in
           let uu___2 =
             encode_term_pred FStar_Pervasives_Native.None
               uv.FStar_Syntax_Syntax.ctx_uvar_typ env ttm in
           (match uu___2 with
            | (t_has_k, decls) ->
                let d =
                  let uu___3 =
                    let uu___4 =
                      let uu___5 =
                        let uu___6 =
                          let uu___7 =
                            FStar_Syntax_Unionfind.uvar_id
                              uv.FStar_Syntax_Syntax.ctx_uvar_head in
                          FStar_Util.string_of_int uu___7 in
                        FStar_Util.format1 "uvar_typing_%s" uu___6 in
                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                        uu___5 in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu___4) in
                  FStar_SMTEncoding_Util.mkAssume uu___3 in
                let uu___3 =
                  let uu___4 =
                    FStar_All.pipe_right [d]
                      FStar_SMTEncoding_Term.mk_decls_trivial in
                  FStar_List.append decls uu___4 in
                (ttm, uu___3))
       | FStar_Syntax_Syntax.Tm_app uu___1 ->
           let uu___2 = FStar_Syntax_Util.head_and_args t0 in
           (match uu___2 with
            | (head, args_e) ->
                let uu___3 =
                  let uu___4 = head_redex env head in
                  if uu___4
                  then
                    let uu___5 = maybe_whnf env t0 in
                    match uu___5 with
                    | FStar_Pervasives_Native.None -> (head, args_e)
                    | FStar_Pervasives_Native.Some t2 ->
                        FStar_Syntax_Util.head_and_args t2
                  else (head, args_e) in
                (match uu___3 with
                 | (head1, args_e1) ->
                     let uu___4 =
                       let uu___5 =
                         let uu___6 = FStar_Syntax_Subst.compress head1 in
                         uu___6.FStar_Syntax_Syntax.n in
                       (uu___5, args_e1) in
                     (match uu___4 with
                      | uu___5 when is_arithmetic_primitive head1 args_e1 ->
                          encode_arith_term env head1 args_e1
                      | uu___5 when is_BitVector_primitive head1 args_e1 ->
                          encode_BitVector_term env head1 args_e1
                      | (FStar_Syntax_Syntax.Tm_fvar fv, uu___5) when
                          (Prims.op_Negation
                             env.FStar_SMTEncoding_Env.encoding_quantifier)
                            &&
                            ((FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.forall_lid)
                               ||
                               (FStar_Syntax_Syntax.fv_eq_lid fv
                                  FStar_Parser_Const.exists_lid))
                          -> encode_deeply_embedded_quantifier t0 env
                      | (FStar_Syntax_Syntax.Tm_uinst
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_fvar fv;
                            FStar_Syntax_Syntax.pos = uu___5;
                            FStar_Syntax_Syntax.vars = uu___6;_},
                          uu___7),
                         uu___8) when
                          (Prims.op_Negation
                             env.FStar_SMTEncoding_Env.encoding_quantifier)
                            &&
                            ((FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.forall_lid)
                               ||
                               (FStar_Syntax_Syntax.fv_eq_lid fv
                                  FStar_Parser_Const.exists_lid))
                          -> encode_deeply_embedded_quantifier t0 env
                      | (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range_of), (arg, uu___5)::[]) ->
                          encode_const
                            (FStar_Const.Const_range
                               (arg.FStar_Syntax_Syntax.pos)) env
                      | (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_set_range_of),
                         (arg, uu___5)::(rng, uu___6)::[]) ->
                          encode_term arg env
                      | (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify), uu___5) ->
                          let e0 =
                            let uu___6 = FStar_List.hd args_e1 in
                            FStar_TypeChecker_Util.reify_body_with_arg
                              env.FStar_SMTEncoding_Env.tcenv [] head1 uu___6 in
                          ((let uu___7 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   env.FStar_SMTEncoding_Env.tcenv)
                                (FStar_Options.Other "SMTEncodingReify") in
                            if uu___7
                            then
                              let uu___8 =
                                FStar_Syntax_Print.term_to_string e0 in
                              FStar_Util.print1
                                "Result of normalization %s\n" uu___8
                            else ());
                           (let e =
                              let uu___7 =
                                FStar_TypeChecker_Util.remove_reify e0 in
                              let uu___8 = FStar_List.tl args_e1 in
                              FStar_Syntax_Syntax.mk_Tm_app uu___7 uu___8
                                t0.FStar_Syntax_Syntax.pos in
                            encode_term e env))
                      | (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu___5),
                         (arg, uu___6)::[]) -> encode_term arg env
                      | uu___5 ->
                          let uu___6 = encode_args args_e1 env in
                          (match uu___6 with
                           | (args, decls) ->
                               let encode_partial_app ht_opt =
                                 let uu___7 = encode_term head1 env in
                                 match uu___7 with
                                 | (smt_head, decls') ->
                                     let app_tm = mk_Apply_args smt_head args in
                                     (match ht_opt with
                                      | uu___8 when
                                          Prims.int_one = Prims.int_one ->
                                          (app_tm,
                                            (FStar_List.append decls decls'))
                                      | FStar_Pervasives_Native.Some
                                          (head_type, formals, c) ->
                                          ((let uu___9 =
                                              FStar_TypeChecker_Env.debug
                                                env.FStar_SMTEncoding_Env.tcenv
                                                (FStar_Options.Other
                                                   "PartialApp") in
                                            if uu___9
                                            then
                                              let uu___10 =
                                                FStar_Syntax_Print.term_to_string
                                                  head1 in
                                              let uu___11 =
                                                FStar_Syntax_Print.term_to_string
                                                  head_type in
                                              let uu___12 =
                                                FStar_Syntax_Print.binders_to_string
                                                  ", " formals in
                                              let uu___13 =
                                                FStar_Syntax_Print.comp_to_string
                                                  c in
                                              let uu___14 =
                                                FStar_Syntax_Print.args_to_string
                                                  args_e1 in
                                              FStar_Util.print5
                                                "Encoding partial application:\n\thead=%s\n\thead_type=%s\n\tformals=%s\n\tcomp=%s\n\tactual args=%s\n"
                                                uu___10 uu___11 uu___12
                                                uu___13 uu___14
                                            else ());
                                           (let uu___9 =
                                              FStar_Util.first_N
                                                (FStar_List.length args_e1)
                                                formals in
                                            match uu___9 with
                                            | (formals1, rest) ->
                                                let subst =
                                                  FStar_List.map2
                                                    (fun uu___10 ->
                                                       fun uu___11 ->
                                                         match (uu___10,
                                                                 uu___11)
                                                         with
                                                         | ({
                                                              FStar_Syntax_Syntax.binder_bv
                                                                = bv;
                                                              FStar_Syntax_Syntax.binder_qual
                                                                = uu___12;
                                                              FStar_Syntax_Syntax.binder_attrs
                                                                = uu___13;_},
                                                            (a, uu___14)) ->
                                                             FStar_Syntax_Syntax.NT
                                                               (bv, a))
                                                    formals1 args_e1 in
                                                let ty =
                                                  let uu___10 =
                                                    FStar_Syntax_Util.arrow
                                                      rest c in
                                                  FStar_All.pipe_right
                                                    uu___10
                                                    (FStar_Syntax_Subst.subst
                                                       subst) in
                                                ((let uu___11 =
                                                    FStar_TypeChecker_Env.debug
                                                      env.FStar_SMTEncoding_Env.tcenv
                                                      (FStar_Options.Other
                                                         "PartialApp") in
                                                  if uu___11
                                                  then
                                                    let uu___12 =
                                                      FStar_Syntax_Print.term_to_string
                                                        ty in
                                                    FStar_Util.print1
                                                      "Encoding partial application, after subst:\n\tty=%s\n"
                                                      uu___12
                                                  else ());
                                                 (let uu___11 =
                                                    let uu___12 =
                                                      FStar_List.fold_left2
                                                        (fun uu___13 ->
                                                           fun uu___14 ->
                                                             fun e ->
                                                               match 
                                                                 (uu___13,
                                                                   uu___14)
                                                               with
                                                               | ((t_hyps,
                                                                   decls1),
                                                                  {
                                                                    FStar_Syntax_Syntax.binder_bv
                                                                    = bv;
                                                                    FStar_Syntax_Syntax.binder_qual
                                                                    = uu___15;
                                                                    FStar_Syntax_Syntax.binder_attrs
                                                                    = uu___16;_})
                                                                   ->
                                                                   let t2 =
                                                                    FStar_Syntax_Subst.subst
                                                                    subst
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                   let uu___17
                                                                    =
                                                                    encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    t2 env e in
                                                                   (match uu___17
                                                                    with
                                                                    | 
                                                                    (t_hyp,
                                                                    decls'1)
                                                                    ->
                                                                    ((
                                                                    let uu___19
                                                                    =
                                                                    FStar_TypeChecker_Env.debug
                                                                    env.FStar_SMTEncoding_Env.tcenv
                                                                    (FStar_Options.Other
                                                                    "PartialApp") in
                                                                    if
                                                                    uu___19
                                                                    then
                                                                    let uu___20
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2 in
                                                                    let uu___21
                                                                    =
                                                                    FStar_SMTEncoding_Term.print_smt_term
                                                                    t_hyp in
                                                                    FStar_Util.print2
                                                                    "Encoded typing hypothesis for %s ... got %s\n"
                                                                    uu___20
                                                                    uu___21
                                                                    else ());
                                                                    ((t_hyp
                                                                    ::
                                                                    t_hyps),
                                                                    (FStar_List.append
                                                                    decls1
                                                                    decls'1)))))
                                                        ([], []) formals1
                                                        args in
                                                    match uu___12 with
                                                    | (t_hyps, decls1) ->
                                                        let uu___13 =
                                                          match smt_head.FStar_SMTEncoding_Term.tm
                                                          with
                                                          | FStar_SMTEncoding_Term.FreeV
                                                              uu___14 ->
                                                              encode_term_pred
                                                                FStar_Pervasives_Native.None
                                                                head_type env
                                                                smt_head
                                                          | uu___14 ->
                                                              (FStar_SMTEncoding_Util.mkTrue,
                                                                []) in
                                                        (match uu___13 with
                                                         | (t_head_hyp,
                                                            decls'1) ->
                                                             let hyp =
                                                               FStar_SMTEncoding_Term.mk_and_l
                                                                 (t_head_hyp
                                                                 :: t_hyps)
                                                                 FStar_Range.dummyRange in
                                                             let uu___14 =
                                                               encode_term_pred
                                                                 FStar_Pervasives_Native.None
                                                                 ty env
                                                                 app_tm in
                                                             (match uu___14
                                                              with
                                                              | (has_type_conclusion,
                                                                 decls'') ->
                                                                  let has_type
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (hyp,
                                                                    has_type_conclusion) in
                                                                  let cvars =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    has_type in
                                                                  let app_tm_vars
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    app_tm in
                                                                  let uu___15
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    FStar_SMTEncoding_Term.fvs_subset_of
                                                                    cvars
                                                                    app_tm_vars in
                                                                    if
                                                                    uu___16
                                                                    then
                                                                    ([app_tm],
                                                                    app_tm_vars)
                                                                    else
                                                                    (let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    has_type_conclusion in
                                                                    FStar_SMTEncoding_Term.fvs_subset_of
                                                                    cvars
                                                                    uu___19 in
                                                                    if
                                                                    uu___18
                                                                    then
                                                                    ([has_type_conclusion],
                                                                    cvars)
                                                                    else
                                                                    ((
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t0 in
                                                                    FStar_Util.format1
                                                                    "No SMT pattern for partial application %s"
                                                                    uu___23 in
                                                                    (FStar_Errors.Warning_SMTPatternIllFormed,
                                                                    uu___22) in
                                                                    FStar_Errors.log_issue
                                                                    t0.FStar_Syntax_Syntax.pos
                                                                    uu___21);
                                                                    ([],
                                                                    cvars))) in
                                                                  (match uu___15
                                                                   with
                                                                   | 
                                                                   (pattern1,
                                                                    vars) ->
                                                                    (vars,
                                                                    pattern1,
                                                                    has_type,
                                                                    (FStar_List.append
                                                                    decls1
                                                                    (FStar_List.append
                                                                    decls'1
                                                                    decls'')))))) in
                                                  match uu___11 with
                                                  | (vars, pattern1,
                                                     has_type, decls'') ->
                                                      ((let uu___13 =
                                                          FStar_TypeChecker_Env.debug
                                                            env.FStar_SMTEncoding_Env.tcenv
                                                            (FStar_Options.Other
                                                               "PartialApp") in
                                                        if uu___13
                                                        then
                                                          let uu___14 =
                                                            FStar_SMTEncoding_Term.print_smt_term
                                                              has_type in
                                                          FStar_Util.print1
                                                            "Encoding partial application, after SMT encoded predicate:\n\t=%s\n"
                                                            uu___14
                                                        else ());
                                                       (let tkey_hash =
                                                          FStar_SMTEncoding_Term.hash_of_term
                                                            app_tm in
                                                        let e_typing =
                                                          let uu___13 =
                                                            let uu___14 =
                                                              FStar_SMTEncoding_Term.mkForall
                                                                t0.FStar_Syntax_Syntax.pos
                                                                ([pattern1],
                                                                  vars,
                                                                  has_type) in
                                                            let uu___15 =
                                                              let uu___16 =
                                                                let uu___17 =
                                                                  FStar_SMTEncoding_Term.hash_of_term
                                                                    app_tm in
                                                                FStar_Util.digest_of_string
                                                                  uu___17 in
                                                              Prims.op_Hat
                                                                "partial_app_typing_"
                                                                uu___16 in
                                                            (uu___14,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Partial app typing"),
                                                              uu___15) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu___13 in
                                                        let uu___13 =
                                                          let uu___14 =
                                                            let uu___15 =
                                                              let uu___16 =
                                                                FStar_SMTEncoding_Term.mk_decls
                                                                  ""
                                                                  tkey_hash
                                                                  [e_typing]
                                                                  (FStar_List.append
                                                                    decls
                                                                    (FStar_List.append
                                                                    decls'
                                                                    decls'')) in
                                                              FStar_List.append
                                                                decls''
                                                                uu___16 in
                                                            FStar_List.append
                                                              decls' uu___15 in
                                                          FStar_List.append
                                                            decls uu___14 in
                                                        (app_tm, uu___13)))))))
                                      | FStar_Pervasives_Native.None ->
                                          failwith "impossible") in
                               let encode_full_app fv =
                                 let uu___7 =
                                   FStar_SMTEncoding_Env.lookup_free_var_sym
                                     env fv in
                                 match uu___7 with
                                 | (fname, fuel_args, arity) ->
                                     let tm =
                                       maybe_curry_app
                                         t0.FStar_Syntax_Syntax.pos fname
                                         arity
                                         (FStar_List.append fuel_args args) in
                                     (tm, decls) in
                               let head2 = FStar_Syntax_Subst.compress head1 in
                               let head_type =
                                 match head2.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_uinst
                                     ({
                                        FStar_Syntax_Syntax.n =
                                          FStar_Syntax_Syntax.Tm_name x;
                                        FStar_Syntax_Syntax.pos = uu___7;
                                        FStar_Syntax_Syntax.vars = uu___8;_},
                                      uu___9)
                                     ->
                                     FStar_Pervasives_Native.Some
                                       (x.FStar_Syntax_Syntax.sort)
                                 | FStar_Syntax_Syntax.Tm_name x ->
                                     FStar_Pervasives_Native.Some
                                       (x.FStar_Syntax_Syntax.sort)
                                 | FStar_Syntax_Syntax.Tm_uinst
                                     ({
                                        FStar_Syntax_Syntax.n =
                                          FStar_Syntax_Syntax.Tm_fvar fv;
                                        FStar_Syntax_Syntax.pos = uu___7;
                                        FStar_Syntax_Syntax.vars = uu___8;_},
                                      uu___9)
                                     ->
                                     let uu___10 =
                                       let uu___11 =
                                         let uu___12 =
                                           FStar_TypeChecker_Env.lookup_lid
                                             env.FStar_SMTEncoding_Env.tcenv
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                         FStar_All.pipe_right uu___12
                                           FStar_Pervasives_Native.fst in
                                       FStar_All.pipe_right uu___11
                                         FStar_Pervasives_Native.snd in
                                     FStar_Pervasives_Native.Some uu___10
                                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                                     let uu___7 =
                                       let uu___8 =
                                         let uu___9 =
                                           FStar_TypeChecker_Env.lookup_lid
                                             env.FStar_SMTEncoding_Env.tcenv
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                         FStar_All.pipe_right uu___9
                                           FStar_Pervasives_Native.fst in
                                       FStar_All.pipe_right uu___8
                                         FStar_Pervasives_Native.snd in
                                     FStar_Pervasives_Native.Some uu___7
                                 | FStar_Syntax_Syntax.Tm_ascribed
                                     (uu___7,
                                      (FStar_Pervasives.Inl t2, uu___8),
                                      uu___9)
                                     -> FStar_Pervasives_Native.Some t2
                                 | FStar_Syntax_Syntax.Tm_ascribed
                                     (uu___7,
                                      (FStar_Pervasives.Inr c, uu___8),
                                      uu___9)
                                     ->
                                     FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Util.comp_result c)
                                 | uu___7 -> FStar_Pervasives_Native.None in
                               (match head_type with
                                | FStar_Pervasives_Native.None ->
                                    encode_partial_app
                                      FStar_Pervasives_Native.None
                                | FStar_Pervasives_Native.Some head_type1 ->
                                    let uu___7 =
                                      let head_type2 =
                                        let uu___8 =
                                          normalize_refinement
                                            [FStar_TypeChecker_Env.Weak;
                                            FStar_TypeChecker_Env.HNF;
                                            FStar_TypeChecker_Env.EraseUniverses]
                                            env.FStar_SMTEncoding_Env.tcenv
                                            head_type1 in
                                        FStar_All.pipe_left
                                          FStar_Syntax_Util.unrefine uu___8 in
                                      let uu___8 =
                                        curried_arrow_formals_comp head_type2 in
                                      match uu___8 with
                                      | (formals, c) ->
                                          if
                                            (FStar_List.length formals) <
                                              (FStar_List.length args)
                                          then
                                            let head_type3 =
                                              let uu___9 =
                                                normalize_refinement
                                                  [FStar_TypeChecker_Env.Weak;
                                                  FStar_TypeChecker_Env.HNF;
                                                  FStar_TypeChecker_Env.EraseUniverses;
                                                  FStar_TypeChecker_Env.UnfoldUntil
                                                    FStar_Syntax_Syntax.delta_constant]
                                                  env.FStar_SMTEncoding_Env.tcenv
                                                  head_type2 in
                                              FStar_All.pipe_left
                                                FStar_Syntax_Util.unrefine
                                                uu___9 in
                                            let uu___9 =
                                              curried_arrow_formals_comp
                                                head_type3 in
                                            (match uu___9 with
                                             | (formals1, c1) ->
                                                 (head_type3, formals1, c1))
                                          else (head_type2, formals, c) in
                                    (match uu___7 with
                                     | (head_type2, formals, c) ->
                                         ((let uu___9 =
                                             FStar_TypeChecker_Env.debug
                                               env.FStar_SMTEncoding_Env.tcenv
                                               (FStar_Options.Other
                                                  "PartialApp") in
                                           if uu___9
                                           then
                                             let uu___10 =
                                               FStar_Syntax_Print.term_to_string
                                                 head_type2 in
                                             let uu___11 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " formals in
                                             let uu___12 =
                                               FStar_Syntax_Print.args_to_string
                                                 args_e1 in
                                             FStar_Util.print3
                                               "Encoding partial application, head_type = %s, formals = %s, args = %s\n"
                                               uu___10 uu___11 uu___12
                                           else ());
                                          (match head2.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_uinst
                                               ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_fvar
                                                    fv;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu___9;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu___10;_},
                                                uu___11)
                                               when
                                               (FStar_List.length formals) =
                                                 (FStar_List.length args)
                                               ->
                                               encode_full_app
                                                 fv.FStar_Syntax_Syntax.fv_name
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               when
                                               (FStar_List.length formals) =
                                                 (FStar_List.length args)
                                               ->
                                               encode_full_app
                                                 fv.FStar_Syntax_Syntax.fv_name
                                           | uu___9 ->
                                               if
                                                 (FStar_List.length formals)
                                                   > (FStar_List.length args)
                                               then
                                                 encode_partial_app
                                                   (FStar_Pervasives_Native.Some
                                                      (head_type2, formals,
                                                        c))
                                               else
                                                 encode_partial_app
                                                   FStar_Pervasives_Native.None))))))))
       | FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) ->
           let uu___1 = FStar_Syntax_Subst.open_term' bs body in
           (match uu___1 with
            | (bs1, body1, opening) ->
                let fallback uu___2 =
                  let f =
                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                      env.FStar_SMTEncoding_Env.current_module_name "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding")) in
                  let uu___3 =
                    let uu___4 =
                      FStar_SMTEncoding_Term.mk_fv
                        (f, FStar_SMTEncoding_Term.Term_sort) in
                    FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu___4 in
                  let uu___4 =
                    FStar_All.pipe_right [decl]
                      FStar_SMTEncoding_Term.mk_decls_trivial in
                  (uu___3, uu___4) in
                let is_impure rc =
                  let uu___2 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                      env.FStar_SMTEncoding_Env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect in
                  FStar_All.pipe_right uu___2 Prims.op_Negation in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None ->
                        let uu___2 =
                          let uu___3 =
                            FStar_TypeChecker_Env.get_range
                              env.FStar_SMTEncoding_Env.tcenv in
                          FStar_TypeChecker_Util.new_implicit_var
                            "SMTEncoding codomain" uu___3
                            env.FStar_SMTEncoding_Env.tcenv
                            FStar_Syntax_Util.ktype0 in
                        (match uu___2 with | (t2, uu___3, uu___4) -> t2)
                    | FStar_Pervasives_Native.Some t2 -> t2 in
                  let uu___2 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid in
                  if uu___2
                  then
                    let uu___3 = FStar_Syntax_Syntax.mk_Total res_typ in
                    FStar_Pervasives_Native.Some uu___3
                  else
                    (let uu___4 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid in
                     if uu___4
                     then
                       let uu___5 = FStar_Syntax_Syntax.mk_GTotal res_typ in
                       FStar_Pervasives_Native.Some uu___5
                     else FStar_Pervasives_Native.None) in
                (match lopt with
                 | FStar_Pervasives_Native.None ->
                     ((let uu___3 =
                         let uu___4 =
                           let uu___5 = FStar_Syntax_Print.term_to_string t0 in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu___5 in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu___4) in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu___3);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu___2 =
                       (is_impure rc) &&
                         (let uu___3 =
                            FStar_SMTEncoding_Util.is_smt_reifiable_rc
                              env.FStar_SMTEncoding_Env.tcenv rc in
                          Prims.op_Negation uu___3) in
                     if uu___2
                     then fallback ()
                     else
                       (let uu___4 =
                          encode_binders FStar_Pervasives_Native.None bs1 env in
                        match uu___4 with
                        | (vars, guards, envbody, decls, uu___5) ->
                            let body2 =
                              let uu___6 =
                                FStar_SMTEncoding_Util.is_smt_reifiable_rc
                                  env.FStar_SMTEncoding_Env.tcenv rc in
                              if uu___6
                              then
                                FStar_TypeChecker_Util.reify_body
                                  env.FStar_SMTEncoding_Env.tcenv [] body1
                              else body1 in
                            let uu___6 = encode_term body2 envbody in
                            (match uu___6 with
                             | (body3, decls') ->
                                 let is_pure =
                                   FStar_Syntax_Util.is_pure_effect
                                     rc.FStar_Syntax_Syntax.residual_effect in
                                 let uu___7 =
                                   let uu___8 = codomain_eff rc in
                                   match uu___8 with
                                   | FStar_Pervasives_Native.None ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c in
                                       let uu___9 = encode_term tfun env in
                                       (match uu___9 with
                                        | (t2, decls1) ->
                                            ((FStar_Pervasives_Native.Some t2),
                                              decls1)) in
                                 (match uu___7 with
                                  | (arrow_t_opt, decls'') ->
                                      let key_body =
                                        let uu___8 =
                                          let uu___9 =
                                            let uu___10 =
                                              let uu___11 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu___11, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu___10 in
                                          ([], vars, uu___9) in
                                        FStar_SMTEncoding_Term.mkForall
                                          t0.FStar_Syntax_Syntax.pos uu___8 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let uu___8 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None ->
                                            (cvars, key_body)
                                        | FStar_Pervasives_Native.Some t2 ->
                                            let uu___9 =
                                              let uu___10 =
                                                let uu___11 =
                                                  FStar_SMTEncoding_Term.free_variables
                                                    t2 in
                                                FStar_List.append uu___11
                                                  cvars in
                                              FStar_Util.remove_dups
                                                FStar_SMTEncoding_Term.fv_eq
                                                uu___10 in
                                            let uu___10 =
                                              FStar_SMTEncoding_Util.mkAnd
                                                (key_body, t2) in
                                            (uu___9, uu___10) in
                                      (match uu___8 with
                                       | (cvars1, key_body1) ->
                                           let tkey =
                                             FStar_SMTEncoding_Term.mkForall
                                               t0.FStar_Syntax_Syntax.pos
                                               ([], cvars1, key_body1) in
                                           let tkey_hash =
                                             FStar_SMTEncoding_Term.hash_of_term
                                               tkey in
                                           ((let uu___10 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env.FStar_SMTEncoding_Env.tcenv)
                                                 (FStar_Options.Other
                                                    "PartialApp") in
                                             if uu___10
                                             then
                                               let uu___11 =
                                                 let uu___12 =
                                                   FStar_List.map
                                                     FStar_SMTEncoding_Term.fv_name
                                                     vars in
                                                 FStar_All.pipe_right uu___12
                                                   (FStar_String.concat ", ") in
                                               let uu___12 =
                                                 FStar_SMTEncoding_Term.print_smt_term
                                                   body3 in
                                               FStar_Util.print2
                                                 "Checking eta expansion of\n\tvars={%s}\n\tbody=%s\n"
                                                 uu___11 uu___12
                                             else ());
                                            (let uu___10 =
                                               is_an_eta_expansion env vars
                                                 body3 in
                                             match uu___10 with
                                             | FStar_Pervasives_Native.Some
                                                 t2 ->
                                                 ((let uu___12 =
                                                     FStar_All.pipe_left
                                                       (FStar_TypeChecker_Env.debug
                                                          env.FStar_SMTEncoding_Env.tcenv)
                                                       (FStar_Options.Other
                                                          "PartialApp") in
                                                   if uu___12
                                                   then
                                                     let uu___13 =
                                                       FStar_SMTEncoding_Term.print_smt_term
                                                         t2 in
                                                     FStar_Util.print1
                                                       "Yes, is an eta expansion of\n\tcore=%s\n"
                                                       uu___13
                                                   else ());
                                                  (let decls1 =
                                                     FStar_List.append decls
                                                       (FStar_List.append
                                                          decls' decls'') in
                                                   (t2, decls1)))
                                             | FStar_Pervasives_Native.None
                                                 ->
                                                 let cvar_sorts =
                                                   FStar_List.map
                                                     FStar_SMTEncoding_Term.fv_sort
                                                     cvars1 in
                                                 let fsym =
                                                   let uu___11 =
                                                     FStar_Util.digest_of_string
                                                       tkey_hash in
                                                   Prims.op_Hat "Tm_abs_"
                                                     uu___11 in
                                                 let fdecl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (fsym, cvar_sorts,
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       FStar_Pervasives_Native.None) in
                                                 let f =
                                                   let uu___11 =
                                                     let uu___12 =
                                                       FStar_List.map
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                         cvars1 in
                                                     (fsym, uu___12) in
                                                   FStar_SMTEncoding_Util.mkApp
                                                     uu___11 in
                                                 let app = mk_Apply f vars in
                                                 let typing_f =
                                                   match arrow_t_opt with
                                                   | FStar_Pervasives_Native.None
                                                       ->
                                                       let tot_fun_ax =
                                                         let ax =
                                                           let uu___11 =
                                                             FStar_All.pipe_right
                                                               vars
                                                               (FStar_List.map
                                                                  (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_SMTEncoding_Util.mkTrue)) in
                                                           isTotFun_axioms
                                                             t0.FStar_Syntax_Syntax.pos
                                                             f vars uu___11
                                                             is_pure in
                                                         match cvars1 with
                                                         | [] -> ax
                                                         | uu___11 ->
                                                             FStar_SMTEncoding_Term.mkForall
                                                               t0.FStar_Syntax_Syntax.pos
                                                               ([[f]],
                                                                 cvars1, ax) in
                                                       let a_name =
                                                         Prims.op_Hat
                                                           "tot_fun_" fsym in
                                                       let uu___11 =
                                                         FStar_SMTEncoding_Util.mkAssume
                                                           (tot_fun_ax,
                                                             (FStar_Pervasives_Native.Some
                                                                a_name),
                                                             a_name) in
                                                       [uu___11]
                                                   | FStar_Pervasives_Native.Some
                                                       t2 ->
                                                       let f_has_t =
                                                         FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                           FStar_Pervasives_Native.None
                                                           f t2 in
                                                       let a_name =
                                                         Prims.op_Hat
                                                           "typing_" fsym in
                                                       let uu___11 =
                                                         let uu___12 =
                                                           let uu___13 =
                                                             FStar_SMTEncoding_Term.mkForall
                                                               t0.FStar_Syntax_Syntax.pos
                                                               ([[f]],
                                                                 cvars1,
                                                                 f_has_t) in
                                                           (uu___13,
                                                             (FStar_Pervasives_Native.Some
                                                                a_name),
                                                             a_name) in
                                                         FStar_SMTEncoding_Util.mkAssume
                                                           uu___12 in
                                                       [uu___11] in
                                                 let interp_f =
                                                   let a_name =
                                                     Prims.op_Hat
                                                       "interpretation_" fsym in
                                                   let uu___11 =
                                                     let uu___12 =
                                                       let uu___13 =
                                                         let uu___14 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app, body3) in
                                                         ([[app]],
                                                           (FStar_List.append
                                                              vars cvars1),
                                                           uu___14) in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         t0.FStar_Syntax_Syntax.pos
                                                         uu___13 in
                                                     (uu___12,
                                                       (FStar_Pervasives_Native.Some
                                                          a_name), a_name) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu___11 in
                                                 let f_decls =
                                                   FStar_List.append (fdecl
                                                     :: typing_f) [interp_f] in
                                                 let uu___11 =
                                                   let uu___12 =
                                                     let uu___13 =
                                                       let uu___14 =
                                                         FStar_SMTEncoding_Term.mk_decls
                                                           fsym tkey_hash
                                                           f_decls
                                                           (FStar_List.append
                                                              decls
                                                              (FStar_List.append
                                                                 decls'
                                                                 decls'')) in
                                                       FStar_List.append
                                                         decls'' uu___14 in
                                                     FStar_List.append decls'
                                                       uu___13 in
                                                   FStar_List.append decls
                                                     uu___12 in
                                                 (f, uu___11)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu___1,
             { FStar_Syntax_Syntax.lbname = FStar_Pervasives.Inr uu___2;
               FStar_Syntax_Syntax.lbunivs = uu___3;
               FStar_Syntax_Syntax.lbtyp = uu___4;
               FStar_Syntax_Syntax.lbeff = uu___5;
               FStar_Syntax_Syntax.lbdef = uu___6;
               FStar_Syntax_Syntax.lbattrs = uu___7;
               FStar_Syntax_Syntax.lbpos = uu___8;_}::uu___9),
            uu___10)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false,
             { FStar_Syntax_Syntax.lbname = FStar_Pervasives.Inl x;
               FStar_Syntax_Syntax.lbunivs = uu___1;
               FStar_Syntax_Syntax.lbtyp = t11;
               FStar_Syntax_Syntax.lbeff = uu___2;
               FStar_Syntax_Syntax.lbdef = e1;
               FStar_Syntax_Syntax.lbattrs = uu___3;
               FStar_Syntax_Syntax.lbpos = uu___4;_}::[]),
            e2)
           -> encode_let x t11 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let ((false, uu___1::uu___2), uu___3) ->
           failwith "Impossible: non-recursive let with multiple bindings"
       | FStar_Syntax_Syntax.Tm_let ((uu___1, lbs), uu___2) ->
           let names =
             FStar_All.pipe_right lbs
               (FStar_List.map
                  (fun lb ->
                     let uu___3 = lb in
                     match uu___3 with
                     | { FStar_Syntax_Syntax.lbname = lbname;
                         FStar_Syntax_Syntax.lbunivs = uu___4;
                         FStar_Syntax_Syntax.lbtyp = uu___5;
                         FStar_Syntax_Syntax.lbeff = uu___6;
                         FStar_Syntax_Syntax.lbdef = uu___7;
                         FStar_Syntax_Syntax.lbattrs = uu___8;
                         FStar_Syntax_Syntax.lbpos = uu___9;_} ->
                         let x = FStar_Util.left lbname in
                         let uu___10 =
                           FStar_Ident.string_of_id
                             x.FStar_Syntax_Syntax.ppname in
                         let uu___11 = FStar_Syntax_Syntax.range_of_bv x in
                         (uu___10, uu___11))) in
           FStar_Exn.raise (FStar_SMTEncoding_Env.Inner_let_rec names)
       | FStar_Syntax_Syntax.Tm_match (e, uu___1, pats) ->
           encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env
             encode_term)
and (encode_let :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          FStar_SMTEncoding_Env.env_t ->
            (FStar_Syntax_Syntax.term ->
               FStar_SMTEncoding_Env.env_t ->
                 (FStar_SMTEncoding_Term.term *
                   FStar_SMTEncoding_Term.decls_t))
              ->
              (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun x ->
    fun t1 ->
      fun e1 ->
        fun e2 ->
          fun env ->
            fun encode_body ->
              let uu___ =
                let uu___1 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Pervasives.Inl t1), FStar_Pervasives_Native.None) in
                encode_term uu___1 env in
              match uu___ with
              | (ee1, decls1) ->
                  let uu___1 =
                    let uu___2 =
                      let uu___3 = FStar_Syntax_Syntax.mk_binder x in
                      [uu___3] in
                    FStar_Syntax_Subst.open_term uu___2 e2 in
                  (match uu___1 with
                   | (xs, e21) ->
                       let x1 =
                         let uu___2 = FStar_List.hd xs in
                         uu___2.FStar_Syntax_Syntax.binder_bv in
                       let env' =
                         FStar_SMTEncoding_Env.push_term_var env x1 ee1 in
                       let uu___2 = encode_body e21 env' in
                       (match uu___2 with
                        | (ee2, decls2) ->
                            (ee2, (FStar_List.append decls1 decls2))))
and (encode_match :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.branch Prims.list ->
      FStar_SMTEncoding_Term.term ->
        FStar_SMTEncoding_Env.env_t ->
          (FStar_Syntax_Syntax.term ->
             FStar_SMTEncoding_Env.env_t ->
               (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
            -> (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun e ->
    fun pats ->
      fun default_case ->
        fun env ->
          fun encode_br ->
            let uu___ =
              let uu___1 =
                let uu___2 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu___2 in
              FStar_SMTEncoding_Env.gen_term_var env uu___1 in
            match uu___ with
            | (scrsym, scr', env1) ->
                let uu___1 = encode_term e env1 in
                (match uu___1 with
                 | (scr, decls) ->
                     let uu___2 =
                       let encode_branch b uu___3 =
                         match uu___3 with
                         | (else_case, decls1) ->
                             let uu___4 = FStar_Syntax_Subst.open_branch b in
                             (match uu___4 with
                              | (p, w, br) ->
                                  let uu___5 = encode_pat env1 p in
                                  (match uu___5 with
                                   | (env0, pattern1) ->
                                       let guard = pattern1.guard scr' in
                                       let projections =
                                         pattern1.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env3 ->
                                                 fun uu___6 ->
                                                   match uu___6 with
                                                   | (x, t) ->
                                                       FStar_SMTEncoding_Env.push_term_var
                                                         env3 x t) env1) in
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
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu___12) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu___11 in
                                                      (guard, uu___10) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu___9 in
                                                  (uu___8, decls2)) in
                                       (match uu___6 with
                                        | (guard1, decls2) ->
                                            let uu___7 = encode_br br env2 in
                                            (match uu___7 with
                                             | (br1, decls3) ->
                                                 let uu___8 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu___8,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu___2 with
                      | (match_tm, decls1) ->
                          let uu___3 =
                            let uu___4 =
                              let uu___5 =
                                let uu___6 =
                                  let uu___7 =
                                    FStar_SMTEncoding_Term.mk_fv
                                      (scrsym,
                                        FStar_SMTEncoding_Term.Term_sort) in
                                  (uu___7, scr) in
                                [uu___6] in
                              (uu___5, match_tm) in
                            FStar_SMTEncoding_Term.mkLet' uu___4
                              FStar_Range.dummyRange in
                          (uu___3, decls1)))
and (encode_pat :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.pat -> (FStar_SMTEncoding_Env.env_t * pattern))
  =
  fun env ->
    fun pat ->
      (let uu___1 =
         FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
           FStar_Options.Medium in
       if uu___1
       then
         let uu___2 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu___2
       else ());
      (let uu___1 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu___1 with
       | (vars, pat_term) ->
           let uu___2 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu___3 ->
                     fun v ->
                       match uu___3 with
                       | (env1, vars1) ->
                           let uu___4 =
                             FStar_SMTEncoding_Env.gen_term_var env1 v in
                           (match uu___4 with
                            | (xx, uu___5, env2) ->
                                let uu___6 =
                                  let uu___7 =
                                    let uu___8 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xx,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    (v, uu___8) in
                                  uu___7 :: vars1 in
                                (env2, uu___6))) (env, [])) in
           (match uu___2 with
            | (env1, vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu___3 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu___3 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu___3 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu___3 = encode_const c env1 in
                      (match uu___3 with
                       | (tm, decls) ->
                           ((match decls with
                             | uu___5::uu___6 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu___5 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f, args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon
                            env1.FStar_SMTEncoding_Env.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu___3 =
                          FStar_TypeChecker_Env.datacons_of_typ
                            env1.FStar_SMTEncoding_Env.tcenv tc_name in
                        match uu___3 with
                        | (uu___4, uu___5::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu___4 ->
                            FStar_SMTEncoding_Env.mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i ->
                                fun uu___3 ->
                                  match uu___3 with
                                  | (arg, uu___4) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu___5 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu___5)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x, uu___3) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu___3 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f, args) ->
                      let uu___3 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i ->
                                fun uu___4 ->
                                  match uu___4 with
                                  | (arg, uu___5) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu___6 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu___6)) in
                      FStar_All.pipe_right uu___3 FStar_List.flatten in
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
  FStar_Syntax_Syntax.args ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term Prims.list *
        FStar_SMTEncoding_Term.decls_t))
  =
  fun l ->
    fun env ->
      let uu___ =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu___1 ->
                fun uu___2 ->
                  match (uu___1, uu___2) with
                  | ((tms, decls), (t, uu___3)) ->
                      let uu___4 = encode_term t env in
                      (match uu___4 with
                       | (t1, decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu___ with | (l1, decls) -> ((FStar_List.rev l1), decls)
and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t ->
    fun env ->
      let universe_of_binders binders =
        FStar_List.map (fun uu___ -> FStar_Syntax_Syntax.U_zero) binders in
      let quant = FStar_Syntax_Util.smt_lemma_as_forall t universe_of_binders in
      let env1 =
        let uu___ = env in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth = (uu___.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv = (uu___.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn = (uu___.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___.FStar_SMTEncoding_Env.encoding_quantifier);
          FStar_SMTEncoding_Env.global_cache =
            (uu___.FStar_SMTEncoding_Env.global_cache)
        } in
      encode_formula quant env1
and (encode_smt_patterns :
  FStar_Syntax_Syntax.arg Prims.list Prims.list ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term Prims.list Prims.list *
        FStar_SMTEncoding_Term.decls_t))
  =
  fun pats_l ->
    fun env ->
      let env1 =
        let uu___ = env in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth = (uu___.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv = (uu___.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn = (uu___.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___.FStar_SMTEncoding_Env.encoding_quantifier);
          FStar_SMTEncoding_Env.global_cache =
            (uu___.FStar_SMTEncoding_Env.global_cache)
        } in
      let encode_smt_pattern t =
        let uu___ = FStar_Syntax_Util.head_and_args t in
        match uu___ with
        | (head, args) ->
            let head1 = FStar_Syntax_Util.un_uinst head in
            (match ((head1.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                uu___1::(x, uu___2)::(t1, uu___3)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu___4 = encode_term x env1 in
                 (match uu___4 with
                  | (x1, decls) ->
                      let uu___5 = encode_term t1 env1 in
                      (match uu___5 with
                       | (t2, decls') ->
                           let uu___6 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t2 in
                           (uu___6, (FStar_List.append decls decls'))))
             | uu___1 -> encode_term t env1) in
      FStar_List.fold_right
        (fun pats ->
           fun uu___ ->
             match uu___ with
             | (pats_l1, decls) ->
                 let uu___1 =
                   FStar_List.fold_right
                     (fun uu___2 ->
                        fun uu___3 ->
                          match (uu___2, uu___3) with
                          | ((p, uu___4), (pats1, decls1)) ->
                              let uu___5 = encode_smt_pattern p in
                              (match uu___5 with
                               | (t, d) ->
                                   let uu___6 =
                                     FStar_SMTEncoding_Term.check_pattern_ok
                                       t in
                                   (match uu___6 with
                                    | FStar_Pervasives_Native.None ->
                                        ((t :: pats1),
                                          (FStar_List.append d decls1))
                                    | FStar_Pervasives_Native.Some
                                        illegal_subterm ->
                                        ((let uu___8 =
                                            let uu___9 =
                                              let uu___10 =
                                                FStar_Syntax_Print.term_to_string
                                                  p in
                                              let uu___11 =
                                                FStar_SMTEncoding_Term.print_smt_term
                                                  illegal_subterm in
                                              FStar_Util.format2
                                                "Pattern %s contains illegal sub-term (%s); dropping it"
                                                uu___10 uu___11 in
                                            (FStar_Errors.Warning_SMTPatternIllFormed,
                                              uu___9) in
                                          FStar_Errors.log_issue
                                            p.FStar_Syntax_Syntax.pos uu___8);
                                         (pats1,
                                           (FStar_List.append d decls1))))))
                     pats ([], decls) in
                 (match uu___1 with
                  | (pats1, decls1) -> ((pats1 :: pats_l1), decls1))) pats_l
        ([], [])
and (encode_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun phi ->
    fun env ->
      let debug phi1 =
        let uu___ =
          FStar_All.pipe_left
            (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu___
        then
          let uu___1 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu___2 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu___1 uu___2
        else () in
      let enc f r l =
        let uu___ =
          FStar_Util.fold_map
            (fun decls ->
               fun x ->
                 let uu___1 = encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu___1 with
                 | (t, decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu___ with
        | (decls, args) ->
            let uu___1 =
              let uu___2 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___2.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___2.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu___1, decls) in
      let const_op f r uu___ = let uu___1 = f r in (uu___1, []) in
      let un_op f l =
        let uu___ = FStar_List.hd l in FStar_All.pipe_left f uu___ in
      let bin_op f uu___ =
        match uu___ with
        | t1::t2::[] -> f (t1, t2)
        | uu___1 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu___ =
          FStar_Util.fold_map
            (fun decls ->
               fun uu___1 ->
                 match uu___1 with
                 | (t, uu___2) ->
                     let uu___3 = encode_formula t env in
                     (match uu___3 with
                      | (phi1, decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu___ with
        | (decls, phis) ->
            let uu___1 =
              let uu___2 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___2.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___2.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu___1, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu___ ->
               match uu___ with
               | (a, q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu___1) -> false
                    | uu___1 -> true)) args in
        if (FStar_List.length rf) <> (Prims.of_int (2))
        then
          let uu___ =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu___
        else
          (let uu___1 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu___1 r rf) in
      let eq3_op r args =
        let n = FStar_List.length args in
        if n = (Prims.of_int (4))
        then
          let uu___ =
            enc
              (fun terms ->
                 match terms with
                 | t0::t1::v0::v1::[] ->
                     let uu___1 =
                       let uu___2 = FStar_SMTEncoding_Util.mkEq (t0, t1) in
                       let uu___3 = FStar_SMTEncoding_Util.mkEq (v0, v1) in
                       (uu___2, uu___3) in
                     FStar_SMTEncoding_Util.mkAnd uu___1
                 | uu___1 -> failwith "Impossible") in
          uu___ r args
        else
          (let uu___1 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n) in
           failwith uu___1) in
      let h_equals_op r args =
        let n = FStar_List.length args in
        if n = (Prims.of_int (4))
        then
          let uu___ =
            enc
              (fun terms ->
                 match terms with
                 | t0::v0::t1::v1::[] ->
                     let uu___1 =
                       let uu___2 = FStar_SMTEncoding_Util.mkEq (t0, t1) in
                       let uu___3 = FStar_SMTEncoding_Util.mkEq (v0, v1) in
                       (uu___2, uu___3) in
                     FStar_SMTEncoding_Util.mkAnd uu___1
                 | uu___1 -> failwith "Impossible") in
          uu___ r args
        else
          (let uu___1 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n) in
           failwith uu___1) in
      let mk_imp r uu___ =
        match uu___ with
        | (lhs, uu___1)::(rhs, uu___2)::[] ->
            let uu___3 = encode_formula rhs env in
            (match uu___3 with
             | (l1, decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp, uu___4) -> (l1, decls1)
                  | uu___4 ->
                      let uu___5 = encode_formula lhs env in
                      (match uu___5 with
                       | (l2, decls2) ->
                           let uu___6 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu___6, (FStar_List.append decls1 decls2)))))
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
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu___1 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu___ = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu___ in
      let connectives =
        let uu___ =
          let uu___1 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu___1) in
        let uu___1 =
          let uu___2 =
            let uu___3 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu___3) in
          let uu___3 =
            let uu___4 =
              let uu___5 =
                let uu___6 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu___6) in
              let uu___6 =
                let uu___7 =
                  let uu___8 =
                    let uu___9 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu___9) in
                  [uu___8;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.c_eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq3_op);
                  (FStar_Parser_Const.c_eq3_lid, h_equals_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu___7 in
              uu___5 :: uu___6 in
            (FStar_Parser_Const.imp_lid, mk_imp) :: uu___4 in
          uu___2 :: uu___3 in
        uu___ :: uu___1 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) ->
            let uu___ = encode_formula phi' env in
            (match uu___ with
             | (phi2, decls) ->
                 let uu___1 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu___1, decls))
        | FStar_Syntax_Syntax.Tm_meta uu___ ->
            let uu___1 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu___1 env
        | FStar_Syntax_Syntax.Tm_match (e, uu___, pats) ->
            let uu___1 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu___1 with | (t, decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false,
              { FStar_Syntax_Syntax.lbname = FStar_Pervasives.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu___;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu___1;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu___2;
                FStar_Syntax_Syntax.lbpos = uu___3;_}::[]),
             e2)
            ->
            let uu___4 = encode_let x t1 e1 e2 env encode_formula in
            (match uu___4 with | (t, decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head, args) ->
            let head1 = FStar_Syntax_Util.un_uinst head in
            (match ((head1.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                uu___::(x, uu___1)::(t, uu___2)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu___3 = encode_term x env in
                 (match uu___3 with
                  | (x1, decls) ->
                      let uu___4 = encode_term t env in
                      (match uu___4 with
                       | (t1, decls') ->
                           let uu___5 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu___5, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                (r, uu___)::(msg, uu___1)::(phi2, uu___2)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu___3 =
                   let uu___4 =
                     let uu___5 =
                       FStar_Syntax_Embeddings.unembed
                         FStar_Syntax_Embeddings.e_range r in
                     uu___5 false FStar_Syntax_Embeddings.id_norm_cb in
                   let uu___5 =
                     let uu___6 =
                       FStar_Syntax_Embeddings.unembed
                         FStar_Syntax_Embeddings.e_string msg in
                     uu___6 false FStar_Syntax_Embeddings.id_norm_cb in
                   (uu___4, uu___5) in
                 (match uu___3 with
                  | (FStar_Pervasives_Native.Some r1,
                     FStar_Pervasives_Native.Some s) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false)))) r1 in
                      fallback phi3
                  | (FStar_Pervasives_Native.None,
                     FStar_Pervasives_Native.Some s) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, (phi2.FStar_Syntax_Syntax.pos), false))))
                          phi2.FStar_Syntax_Syntax.pos in
                      fallback phi3
                  | uu___4 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv, (t, uu___)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu___ ->
                 let encode_valid uu___1 =
                   let uu___2 = encode_term phi1 env in
                   match uu___2 with
                   | (tt, decls) ->
                       let tt1 =
                         let uu___3 =
                           let uu___4 =
                             FStar_Range.use_range
                               tt.FStar_SMTEncoding_Term.rng in
                           let uu___5 =
                             FStar_Range.use_range
                               phi1.FStar_Syntax_Syntax.pos in
                           FStar_Range.rng_included uu___4 uu___5 in
                         if uu___3
                         then tt
                         else
                           (let uu___5 = tt in
                            {
                              FStar_SMTEncoding_Term.tm =
                                (uu___5.FStar_SMTEncoding_Term.tm);
                              FStar_SMTEncoding_Term.freevars =
                                (uu___5.FStar_SMTEncoding_Term.freevars);
                              FStar_SMTEncoding_Term.rng =
                                (phi1.FStar_Syntax_Syntax.pos)
                            }) in
                       let uu___3 = FStar_SMTEncoding_Term.mk_Valid tt1 in
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
                       FStar_Range.use_range tt.FStar_SMTEncoding_Term.rng in
                     let uu___4 =
                       FStar_Range.use_range phi1.FStar_Syntax_Syntax.pos in
                     FStar_Range.rng_included uu___3 uu___4 in
                   if uu___2
                   then tt
                   else
                     (let uu___4 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___4.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___4.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 let uu___2 = FStar_SMTEncoding_Term.mk_Valid tt1 in
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
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf, p::[]);
                             FStar_SMTEncoding_Term.freevars = uu___4;
                             FStar_SMTEncoding_Term.rng = uu___5;_}::[])::[]
                            when
                            let uu___6 =
                              FStar_Ident.string_of_lid
                                FStar_Parser_Const.guard_free in
                            uu___6 = gf -> []
                        | uu___4 -> guards in
                      let uu___4 = FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu___4, body1,
                        (FStar_List.append decls
                           (FStar_List.append decls' decls''))))) in
      debug phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let uu___1 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu___1 with
       | FStar_Pervasives_Native.None -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op, arms))
           ->
           let uu___2 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu___3 ->
                     match uu___3 with
                     | (l, uu___4) -> FStar_Ident.lid_equals op l)) in
           (match uu___2 with
            | FStar_Pervasives_Native.None -> fallback phi1
            | FStar_Pervasives_Native.Some (uu___3, f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars, pats, body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu___3 = encode_q_body env vars pats body in
             match uu___3 with
             | (vars1, pats1, guard, body1, decls) ->
                 let tm =
                   let uu___4 =
                     let uu___5 = FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu___5) in
                   FStar_SMTEncoding_Term.mkForall
                     phi1.FStar_Syntax_Syntax.pos uu___4 in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars, pats, body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu___3 = encode_q_body env vars pats body in
             match uu___3 with
             | (vars1, pats1, guard, body1, decls) ->
                 let uu___4 =
                   let uu___5 =
                     let uu___6 = FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu___6) in
                   FStar_SMTEncoding_Term.mkExists
                     phi1.FStar_Syntax_Syntax.pos uu___5 in
                 (uu___4, decls))))