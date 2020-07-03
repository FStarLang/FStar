open Prims
let mkForall_fuel' :
  'uuuuuu14 .
    Prims.string ->
      FStar_Range.range ->
        'uuuuuu14 ->
          (FStar_SMTEncoding_Term.pat Prims.list Prims.list *
            FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term) ->
            FStar_SMTEncoding_Term.term
  =
  fun mname ->
    fun r ->
      fun n ->
        fun uu____44 ->
          match uu____44 with
          | (pats, vars, body) ->
              let fallback uu____71 =
                FStar_SMTEncoding_Term.mkForall r (pats, vars, body) in
              let uu____76 = FStar_Options.unthrottle_inductives () in
              if uu____76
              then fallback ()
              else
                (let uu____78 =
                   FStar_SMTEncoding_Env.fresh_fvar mname "f"
                     FStar_SMTEncoding_Term.Fuel_sort in
                 match uu____78 with
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
                               | uu____111 -> p)) in
                     let pats1 = FStar_List.map add_fuel pats in
                     let body1 =
                       match body.FStar_SMTEncoding_Term.tm with
                       | FStar_SMTEncoding_Term.App
                           (FStar_SMTEncoding_Term.Imp, guard::body'::[]) ->
                           let guard1 =
                             match guard.FStar_SMTEncoding_Term.tm with
                             | FStar_SMTEncoding_Term.App
                                 (FStar_SMTEncoding_Term.And, guards) ->
                                 let uu____132 = add_fuel guards in
                                 FStar_SMTEncoding_Util.mk_and_l uu____132
                             | uu____135 ->
                                 let uu____136 = add_fuel [guard] in
                                 FStar_All.pipe_right uu____136 FStar_List.hd in
                           FStar_SMTEncoding_Util.mkImp (guard1, body')
                       | uu____141 -> body in
                     let vars1 =
                       let uu____151 =
                         FStar_SMTEncoding_Term.mk_fv
                           (fsym, FStar_SMTEncoding_Term.Fuel_sort) in
                       uu____151 :: vars in
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
      | FStar_Syntax_Syntax.Tm_arrow uu____202 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____217 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____224 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____225 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____238 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____257 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____259 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____259 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____277;
             FStar_Syntax_Syntax.vars = uu____278;_},
           uu____279)
          ->
          let uu____304 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____304 FStar_Option.isNone
      | uu____321 -> false
let (head_redex :
  FStar_SMTEncoding_Env.env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env ->
    fun t ->
      let uu____332 =
        let uu____333 = FStar_Syntax_Util.un_uinst t in
        uu____333.FStar_Syntax_Syntax.n in
      match uu____332 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____336, uu____337, FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___0_362 ->
                  match uu___0_362 with
                  | FStar_Syntax_Syntax.TOTAL -> true
                  | uu____363 -> false) rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____365 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____365 FStar_Option.isSome
      | uu____382 -> false
let (norm_with_steps :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun steps ->
    fun env ->
      fun t ->
        let uu____398 =
          let uu____401 =
            let uu____402 = FStar_TypeChecker_Env.current_module env in
            FStar_Ident.string_of_lid uu____402 in
          FStar_Pervasives_Native.Some uu____401 in
        FStar_Profiling.profile
          (fun uu____404 -> FStar_TypeChecker_Normalize.normalize steps env t)
          uu____398
          "FStar.TypeChecker.SMTEncoding.EncodeTerm.norm_with_steps"
let (normalize_refinement :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun steps ->
    fun env ->
      fun t ->
        let uu____420 =
          let uu____423 =
            let uu____424 = FStar_TypeChecker_Env.current_module env in
            FStar_Ident.string_of_lid uu____424 in
          FStar_Pervasives_Native.Some uu____423 in
        FStar_Profiling.profile
          (fun uu____426 ->
             FStar_TypeChecker_Normalize.normalize_refinement steps env t)
          uu____420
          "FStar.TypeChecker.SMTEncoding.EncodeTerm.normalize_refinement"
let (whnf :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun t ->
      let uu____437 = head_normal env t in
      if uu____437
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
      let uu____462 = FStar_Syntax_Util.head_and_args t' in
      match uu____462 with
      | (head', uu____482) ->
          let uu____507 = head_redex env head' in
          if uu____507
          then FStar_Pervasives_Native.None
          else FStar_Pervasives_Native.Some t'
let (trivial_post : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let uu____516 =
      let uu____517 = FStar_Syntax_Syntax.null_binder t in [uu____517] in
    let uu____536 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
    FStar_Syntax_Util.abs uu____516 uu____536 FStar_Pervasives_Native.None
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
                let uu____557 = FStar_SMTEncoding_Term.fv_sort var in
                match uu____557 with
                | FStar_SMTEncoding_Term.Fuel_sort ->
                    let uu____558 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____558
                | s ->
                    let uu____560 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____560) e)
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
          let uu____608 =
            let uu____613 =
              let uu____614 = FStar_Util.string_of_int arity in
              let uu____615 = FStar_Util.string_of_int n_args in
              FStar_Util.format3
                "Head symbol %s expects at least %s arguments; got only %s"
                head uu____614 uu____615 in
            (FStar_Errors.Fatal_SMTEncodingArityMismatch, uu____613) in
          FStar_Errors.raise_error uu____608 rng
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
              | uu____691 ->
                  FStar_SMTEncoding_Term.mkForall pos (pat, vars1, body) in
            let rec is_tot_fun_axioms ctx ctx_guard head1 vars1 guards1 =
              match (vars1, guards1) with
              | ([], []) -> FStar_SMTEncoding_Util.mkTrue
              | (uu____792::[], uu____793) ->
                  if is_pure
                  then
                    let uu____824 =
                      let uu____825 =
                        let uu____830 =
                          FStar_SMTEncoding_Term.mk_IsTotFun head1 in
                        (ctx_guard, uu____830) in
                      FStar_SMTEncoding_Util.mkImp uu____825 in
                    maybe_mkForall [[head1]] ctx uu____824
                  else FStar_SMTEncoding_Util.mkTrue
              | (x::vars2, g_x::guards2) ->
                  let is_tot_fun_head =
                    let uu____873 =
                      let uu____874 =
                        let uu____879 =
                          FStar_SMTEncoding_Term.mk_IsTotFun head1 in
                        (ctx_guard, uu____879) in
                      FStar_SMTEncoding_Util.mkImp uu____874 in
                    maybe_mkForall [[head1]] ctx uu____873 in
                  let app = mk_Apply head1 [x] in
                  let ctx1 = FStar_List.append ctx [x] in
                  let ctx_guard1 =
                    FStar_SMTEncoding_Util.mkAnd (ctx_guard, g_x) in
                  let rest =
                    is_tot_fun_axioms ctx1 ctx_guard1 app vars2 guards2 in
                  FStar_SMTEncoding_Util.mkAnd (is_tot_fun_head, rest)
              | uu____926 -> failwith "impossible: isTotFun_axioms" in
            is_tot_fun_axioms [] FStar_SMTEncoding_Util.mkTrue head vars
              guards
let (maybe_curry_app :
  FStar_Range.range ->
    (FStar_SMTEncoding_Term.op, FStar_SMTEncoding_Term.term)
      FStar_Util.either ->
      Prims.int ->
        FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term)
  =
  fun rng ->
    fun head ->
      fun arity ->
        fun args ->
          let n_args = FStar_List.length args in
          match head with
          | FStar_Util.Inr head1 -> mk_Apply_args head1 args
          | FStar_Util.Inl head1 ->
              if n_args = arity
              then FStar_SMTEncoding_Util.mkApp' (head1, args)
              else
                if n_args > arity
                then
                  (let uu____985 = FStar_Util.first_N arity args in
                   match uu____985 with
                   | (args1, rest) ->
                       let head2 =
                         FStar_SMTEncoding_Util.mkApp' (head1, args1) in
                       mk_Apply_args head2 rest)
                else
                  (let uu____1008 = FStar_SMTEncoding_Term.op_to_string head1 in
                   raise_arity_mismatch uu____1008 arity n_args rng)
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
          let uu____1028 = FStar_SMTEncoding_Env.force_thunk fvb in
          mk_Apply_args uu____1028 args
        else
          maybe_curry_app rng
            (FStar_Util.Inl
               (FStar_SMTEncoding_Term.Var (fvb.FStar_SMTEncoding_Env.smt_id)))
            fvb.FStar_SMTEncoding_Env.smt_arity args
let (is_app : FStar_SMTEncoding_Term.op -> Prims.bool) =
  fun uu___1_1034 ->
    match uu___1_1034 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____1035 -> false
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
                   FStar_SMTEncoding_Term.freevars = uu____1081;
                   FStar_SMTEncoding_Term.rng = uu____1082;_}::[]),
             x::xs1) when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)
              -> check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var f, args),
             uu____1109) ->
              let uu____1118 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a ->
                        fun v ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v
                          | uu____1131 -> false) args (FStar_List.rev xs)) in
              if uu____1118
              then
                let n = FStar_SMTEncoding_Env.tok_of_name env f in
                ((let uu____1138 =
                    FStar_All.pipe_left
                      (FStar_TypeChecker_Env.debug
                         env.FStar_SMTEncoding_Env.tcenv)
                      (FStar_Options.Other "PartialApp") in
                  if uu____1138
                  then
                    let uu____1139 = FStar_SMTEncoding_Term.print_smt_term t in
                    let uu____1140 =
                      match n with
                      | FStar_Pervasives_Native.None -> "None"
                      | FStar_Pervasives_Native.Some x ->
                          FStar_SMTEncoding_Term.print_smt_term x in
                    FStar_Util.print2
                      "is_eta_expansion %s  ... tok_of_name = %s\n"
                      uu____1139 uu____1140
                  else ());
                 n)
              else FStar_Pervasives_Native.None
          | (uu____1144, []) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____1148 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv ->
                        let uu____1154 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____1154)) in
              if uu____1148
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____1158 -> FStar_Pervasives_Native.None in
        check_partial_applications body (FStar_List.rev vars)
let check_pattern_vars :
  'uuuuuu1175 'uuuuuu1176 .
    FStar_SMTEncoding_Env.env_t ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu1175) Prims.list ->
        (FStar_Syntax_Syntax.term * 'uuuuuu1176) Prims.list -> unit
  =
  fun env ->
    fun vars ->
      fun pats ->
        let pats1 =
          FStar_All.pipe_right pats
            (FStar_List.map
               (fun uu____1234 ->
                  match uu____1234 with
                  | (x, uu____1240) ->
                      norm_with_steps
                        [FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.AllowUnboundUniverses;
                        FStar_TypeChecker_Env.EraseUniverses]
                        env.FStar_SMTEncoding_Env.tcenv x)) in
        match pats1 with
        | [] -> ()
        | hd::tl ->
            let pat_vars =
              let uu____1248 = FStar_Syntax_Free.names hd in
              FStar_List.fold_left
                (fun out ->
                   fun x ->
                     let uu____1260 = FStar_Syntax_Free.names x in
                     FStar_Util.set_union out uu____1260) uu____1248 tl in
            let uu____1263 =
              FStar_All.pipe_right vars
                (FStar_Util.find_opt
                   (fun uu____1290 ->
                      match uu____1290 with
                      | (b, uu____1296) ->
                          let uu____1297 = FStar_Util.set_mem b pat_vars in
                          Prims.op_Negation uu____1297)) in
            (match uu____1263 with
             | FStar_Pervasives_Native.None -> ()
             | FStar_Pervasives_Native.Some (x, uu____1303) ->
                 let pos =
                   FStar_List.fold_left
                     (fun out ->
                        fun t ->
                          FStar_Range.union_ranges out
                            t.FStar_Syntax_Syntax.pos)
                     hd.FStar_Syntax_Syntax.pos tl in
                 let uu____1317 =
                   let uu____1322 =
                     let uu____1323 = FStar_Syntax_Print.bv_to_string x in
                     FStar_Util.format1
                       "SMT pattern misses at least one bound variable: %s"
                       uu____1323 in
                   (FStar_Errors.Warning_SMTPatternIllFormed, uu____1322) in
                 FStar_Errors.log_issue pos uu____1317)
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
        | FStar_Syntax_Syntax.Tm_arrow uu____1598 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____1613 ->
            let uu____1620 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____1620
        | uu____1621 ->
            if norm1
            then let uu____1622 = whnf env t1 in aux false uu____1622
            else
              (let uu____1624 =
                 let uu____1625 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____1626 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____1625 uu____1626 in
               failwith uu____1624) in
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
    | FStar_Syntax_Syntax.Tm_refine (bv, uu____1664) ->
        let uu____1669 =
          curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort in
        (match uu____1669 with
         | (args, res) ->
             (match args with
              | [] ->
                  let uu____1690 = FStar_Syntax_Syntax.mk_Total k1 in
                  ([], uu____1690)
              | uu____1697 -> (args, res)))
    | uu____1698 ->
        let uu____1699 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____1699)
let is_arithmetic_primitive :
  'uuuuuu1712 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'uuuuuu1712 Prims.list -> Prims.bool
  =
  fun head ->
    fun args ->
      match ((head.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv, uu____1734::uu____1735::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv, uu____1739::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____1742 -> false
let (isInteger : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun tm ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n, FStar_Pervasives_Native.None)) -> true
    | uu____1765 -> false
let (getInteger : FStar_Syntax_Syntax.term' -> Prims.int) =
  fun tm ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n, FStar_Pervasives_Native.None)) -> FStar_Util.int_of_string n
    | uu____1782 -> failwith "Expected an Integer term"
let is_BitVector_primitive :
  'uuuuuu1789 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'uuuuuu1789)
        Prims.list -> Prims.bool
  =
  fun head ->
    fun args ->
      match ((head.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,
         (sz_arg, uu____1830)::uu____1831::uu____1832::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,
         (sz_arg, uu____1883)::uu____1884::[]) ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____1921 -> false
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
          let uu____2242 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue in
          (uu____2242, [])
      | FStar_Const.Const_bool (false) ->
          let uu____2243 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse in
          (uu____2243, [])
      | FStar_Const.Const_char c1 ->
          let uu____2245 =
            let uu____2246 =
              let uu____2253 =
                let uu____2256 =
                  let uu____2257 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1) in
                  FStar_SMTEncoding_Term.boxInt uu____2257 in
                [uu____2256] in
              ("FStar.Char.__char_of_int", uu____2253) in
            FStar_SMTEncoding_Util.mkApp uu____2246 in
          (uu____2245, [])
      | FStar_Const.Const_int (i, FStar_Pervasives_Native.None) ->
          let uu____2271 =
            let uu____2272 = FStar_SMTEncoding_Util.mkInteger i in
            FStar_SMTEncoding_Term.boxInt uu____2272 in
          (uu____2271, [])
      | FStar_Const.Const_int (repr, FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.FStar_SMTEncoding_Env.tcenv).FStar_TypeChecker_Env.dsenv
              repr sw FStar_Range.dummyRange in
          encode_term syntax_term env
      | FStar_Const.Const_string (s, uu____2291) ->
          let uu____2292 =
            let uu____2293 = FStar_SMTEncoding_Util.mk_String_const s in
            FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____2293 in
          (uu____2292, [])
      | FStar_Const.Const_range uu____2294 ->
          let uu____2295 = FStar_SMTEncoding_Term.mk_Range_const () in
          (uu____2295, [])
      | FStar_Const.Const_effect -> (FStar_SMTEncoding_Term.mk_Term_type, [])
      | FStar_Const.Const_real r ->
          let uu____2297 =
            let uu____2298 = FStar_SMTEncoding_Util.mkReal r in
            FStar_SMTEncoding_Term.boxReal uu____2298 in
          (uu____2297, [])
      | c1 ->
          let uu____2300 =
            let uu____2301 = FStar_Syntax_Print.const_to_string c1 in
            FStar_Util.format1 "Unhandled constant: %s" uu____2301 in
          failwith uu____2300
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
        (let uu____2328 =
           FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
             FStar_Options.Medium in
         if uu____2328
         then
           let uu____2329 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____2329
         else ());
        (let uu____2331 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2413 ->
                   fun b ->
                     match uu____2413 with
                     | (vars, guards, env1, decls, names) ->
                         let uu____2478 =
                           let x = FStar_Pervasives_Native.fst b in
                           let uu____2494 =
                             FStar_SMTEncoding_Env.gen_term_var env1 x in
                           match uu____2494 with
                           | (xxsym, xx, env') ->
                               let uu____2516 =
                                 let uu____2521 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____2521 env1 xx in
                               (match uu____2516 with
                                | (guard_x_t, decls') ->
                                    let uu____2536 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xxsym,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    (uu____2536, guard_x_t, env', decls', x)) in
                         (match uu____2478 with
                          | (v, g, env2, decls', n) ->
                              ((v :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n ::
                                names)))) ([], [], env, [], [])) in
         match uu____2331 with
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
          let uu____2635 = encode_term t env in
          match uu____2635 with
          | (t1, decls) ->
              let uu____2646 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____2646, decls)
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
          let uu____2657 = encode_term t env in
          match uu____2657 with
          | (t1, decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None ->
                   let uu____2672 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____2672, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____2674 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____2674, decls))
and (encode_arith_term :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun env ->
    fun head ->
      fun args_e ->
        let uu____2680 = encode_args args_e env in
        match uu____2680 with
        | (arg_tms, decls) ->
            let head_fv =
              match head.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____2699 -> failwith "Impossible" in
            let unary unbox arg_tms1 =
              let uu____2720 = FStar_List.hd arg_tms1 in unbox uu____2720 in
            let binary unbox arg_tms1 =
              let uu____2745 =
                let uu____2746 = FStar_List.hd arg_tms1 in unbox uu____2746 in
              let uu____2747 =
                let uu____2748 =
                  let uu____2749 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____2749 in
                unbox uu____2748 in
              (uu____2745, uu____2747) in
            let mk_default uu____2757 =
              let uu____2758 =
                FStar_SMTEncoding_Env.lookup_free_var_sym env
                  head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____2758 with
              | (fname, fuel_args, arity) ->
                  let args = FStar_List.append fuel_args arg_tms in
                  maybe_curry_app head.FStar_Syntax_Syntax.pos fname arity
                    args in
            let mk_l box op mk_args ts =
              let uu____2844 = FStar_Options.smtencoding_l_arith_native () in
              if uu____2844
              then
                let uu____2845 = let uu____2846 = mk_args ts in op uu____2846 in
                FStar_All.pipe_right uu____2845 box
              else mk_default () in
            let mk_nl box unbox nm op ts =
              let uu____2901 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____2901
              then
                let uu____2902 = binary unbox ts in
                match uu____2902 with
                | (t1, t2) ->
                    let uu____2909 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____2909 box
              else
                (let uu____2913 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____2913
                 then
                   let uu____2914 =
                     let uu____2915 = binary unbox ts in op uu____2915 in
                   FStar_All.pipe_right uu____2914 box
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
            let uu____3340 =
              let uu____3350 =
                FStar_List.tryFind
                  (fun uu____3374 ->
                     match uu____3374 with
                     | (l, uu____3384) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____3350 FStar_Util.must in
            (match uu____3340 with
             | (uu____3428, op) ->
                 let uu____3440 = op arg_tms in (uu____3440, decls))
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
        let uu____3456 = FStar_List.hd args_e in
        match uu____3456 with
        | (tm_sz, uu____3472) ->
            let uu____3481 = uu____3456 in
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz) in
            let sz_decls =
              let t_decls = FStar_SMTEncoding_Term.mkBvConstructor sz in
              FStar_SMTEncoding_Term.mk_decls "" sz_key t_decls [] in
            let uu____3488 =
              match ((head.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar fv,
                 uu____3512::(sz_arg, uu____3514)::uu____3515::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____3582 =
                    let uu____3583 = FStar_List.tail args_e in
                    FStar_List.tail uu____3583 in
                  let uu____3610 =
                    let uu____3613 = getInteger sz_arg.FStar_Syntax_Syntax.n in
                    FStar_Pervasives_Native.Some uu____3613 in
                  (uu____3582, uu____3610)
              | (FStar_Syntax_Syntax.Tm_fvar fv,
                 uu____3617::(sz_arg, uu____3619)::uu____3620::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____3687 =
                    let uu____3688 = FStar_Syntax_Print.term_to_string sz_arg in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____3688 in
                  failwith uu____3687
              | uu____3695 ->
                  let uu____3710 = FStar_List.tail args_e in
                  (uu____3710, FStar_Pervasives_Native.None) in
            (match uu____3488 with
             | (arg_tms, ext_sz) ->
                 let uu____3733 = encode_args arg_tms env in
                 (match uu____3733 with
                  | (arg_tms1, decls) ->
                      let head_fv =
                        match head.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____3754 -> failwith "Impossible" in
                      let unary arg_tms2 =
                        let uu____3765 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____3765 in
                      let unary_arith arg_tms2 =
                        let uu____3776 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxInt uu____3776 in
                      let binary arg_tms2 =
                        let uu____3791 =
                          let uu____3792 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3792 in
                        let uu____3793 =
                          let uu____3794 =
                            let uu____3795 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____3795 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3794 in
                        (uu____3791, uu____3793) in
                      let binary_arith arg_tms2 =
                        let uu____3812 =
                          let uu____3813 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3813 in
                        let uu____3814 =
                          let uu____3815 =
                            let uu____3816 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____3816 in
                          FStar_SMTEncoding_Term.unboxInt uu____3815 in
                        (uu____3812, uu____3814) in
                      let mk_bv op mk_args resBox ts =
                        let uu____3874 =
                          let uu____3875 = mk_args ts in op uu____3875 in
                        FStar_All.pipe_right uu____3874 resBox in
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
                        let uu____4007 =
                          let uu____4012 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None ->
                                failwith "impossible" in
                          FStar_SMTEncoding_Util.mkBvUext uu____4012 in
                        let uu____4014 =
                          let uu____4019 =
                            let uu____4020 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None ->
                                  failwith "impossible" in
                            sz + uu____4020 in
                          FStar_SMTEncoding_Term.boxBitVec uu____4019 in
                        mk_bv uu____4007 unary uu____4014 arg_tms2 in
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
                      let uu____4253 =
                        let uu____4263 =
                          FStar_List.tryFind
                            (fun uu____4287 ->
                               match uu____4287 with
                               | (l, uu____4297) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops in
                        FStar_All.pipe_right uu____4263 FStar_Util.must in
                      (match uu____4253 with
                       | (uu____4343, op) ->
                           let uu____4355 = op arg_tms1 in
                           (uu____4355, (FStar_List.append sz_decls decls)))))
and (encode_deeply_embedded_quantifier :
  FStar_Syntax_Syntax.term ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t ->
    fun env ->
      let env1 =
        let uu___601_4365 = env in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___601_4365.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___601_4365.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___601_4365.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___601_4365.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___601_4365.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___601_4365.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name =
            (uu___601_4365.FStar_SMTEncoding_Env.use_zfuel_name);
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___601_4365.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___601_4365.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier = true;
          FStar_SMTEncoding_Env.global_cache =
            (uu___601_4365.FStar_SMTEncoding_Env.global_cache)
        } in
      let uu____4366 = encode_term t env1 in
      match uu____4366 with
      | (tm, decls) ->
          let vars = FStar_SMTEncoding_Term.free_variables tm in
          let valid_tm = FStar_SMTEncoding_Term.mk_Valid tm in
          let key =
            FStar_SMTEncoding_Term.mkForall t.FStar_Syntax_Syntax.pos
              ([], vars, valid_tm) in
          let tkey_hash = FStar_SMTEncoding_Term.hash_of_term key in
          (match tm.FStar_SMTEncoding_Term.tm with
           | FStar_SMTEncoding_Term.App
               (uu____4391,
                {
                  FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV
                    uu____4392;
                  FStar_SMTEncoding_Term.freevars = uu____4393;
                  FStar_SMTEncoding_Term.rng = uu____4394;_}::{
                                                                FStar_SMTEncoding_Term.tm
                                                                  =
                                                                  FStar_SMTEncoding_Term.FreeV
                                                                  uu____4395;
                                                                FStar_SMTEncoding_Term.freevars
                                                                  =
                                                                  uu____4396;
                                                                FStar_SMTEncoding_Term.rng
                                                                  =
                                                                  uu____4397;_}::[])
               ->
               (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                  (FStar_Errors.Warning_QuantifierWithoutPattern,
                    "Not encoding deeply embedded, unguarded quantifier to SMT");
                (tm, decls))
           | uu____4433 ->
               let uu____4434 = encode_formula t env1 in
               (match uu____4434 with
                | (phi, decls') ->
                    let interp =
                      match vars with
                      | [] ->
                          let uu____4452 =
                            let uu____4457 =
                              FStar_SMTEncoding_Term.mk_Valid tm in
                            (uu____4457, phi) in
                          FStar_SMTEncoding_Util.mkIff uu____4452
                      | uu____4458 ->
                          let uu____4459 =
                            let uu____4470 =
                              let uu____4471 =
                                let uu____4476 =
                                  FStar_SMTEncoding_Term.mk_Valid tm in
                                (uu____4476, phi) in
                              FStar_SMTEncoding_Util.mkIff uu____4471 in
                            ([[valid_tm]], vars, uu____4470) in
                          FStar_SMTEncoding_Term.mkForall
                            t.FStar_Syntax_Syntax.pos uu____4459 in
                    let ax =
                      let uu____4486 =
                        let uu____4493 =
                          let uu____4494 =
                            FStar_Util.digest_of_string tkey_hash in
                          Prims.op_Hat "l_quant_interp_" uu____4494 in
                        (interp,
                          (FStar_Pervasives_Native.Some
                             "Interpretation of deeply embedded quantifier"),
                          uu____4493) in
                      FStar_SMTEncoding_Util.mkAssume uu____4486 in
                    let uu____4495 =
                      let uu____4496 =
                        let uu____4499 =
                          FStar_SMTEncoding_Term.mk_decls "" tkey_hash 
                            [ax] (FStar_List.append decls decls') in
                        FStar_List.append decls' uu____4499 in
                      FStar_List.append decls uu____4496 in
                    (tm, uu____4495)))
and (encode_term :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t ->
    fun env ->
      let t1 = FStar_Syntax_Subst.compress t in
      let t0 = t1 in
      (let uu____4511 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____4511
       then
         let uu____4512 = FStar_Syntax_Print.tag_of_term t1 in
         let uu____4513 = FStar_Syntax_Print.term_to_string t1 in
         FStar_Util.print2 "(%s)   %s\n" uu____4512 uu____4513
       else ());
      (match t1.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____4519 ->
           let uu____4534 =
             let uu____4535 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t1.FStar_Syntax_Syntax.pos in
             let uu____4536 = FStar_Syntax_Print.tag_of_term t1 in
             let uu____4537 = FStar_Syntax_Print.term_to_string t1 in
             FStar_Util.format3 "(%s) Impossible: %s\n%s\n" uu____4535
               uu____4536 uu____4537 in
           failwith uu____4534
       | FStar_Syntax_Syntax.Tm_unknown ->
           let uu____4542 =
             let uu____4543 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t1.FStar_Syntax_Syntax.pos in
             let uu____4544 = FStar_Syntax_Print.tag_of_term t1 in
             let uu____4545 = FStar_Syntax_Print.term_to_string t1 in
             FStar_Util.format3 "(%s) Impossible: %s\n%s\n" uu____4543
               uu____4544 uu____4545 in
           failwith uu____4542
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let e = FStar_Syntax_Util.unfold_lazy i in
           ((let uu____4553 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding") in
             if uu____4553
             then
               let uu____4554 = FStar_Syntax_Print.term_to_string t1 in
               let uu____4555 = FStar_Syntax_Print.term_to_string e in
               FStar_Util.print2 ">> Unfolded (%s) ~> (%s)\n" uu____4554
                 uu____4555
             else ());
            encode_term e env)
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____4558 =
             let uu____4559 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____4559 in
           failwith uu____4558
       | FStar_Syntax_Syntax.Tm_ascribed (t2, (k, uu____4566), uu____4567) ->
           let uu____4616 =
             match k with
             | FStar_Util.Inl t3 -> FStar_Syntax_Util.is_unit t3
             | uu____4624 -> false in
           if uu____4616
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t2 env
       | FStar_Syntax_Syntax.Tm_quoted (qt, uu____4639) ->
           let tv =
             let uu____4645 =
               let uu____4652 = FStar_Reflection_Basic.inspect_ln qt in
               FStar_Syntax_Embeddings.embed
                 FStar_Reflection_Embeddings.e_term_view uu____4652 in
             uu____4645 t1.FStar_Syntax_Syntax.pos
               FStar_Pervasives_Native.None
               FStar_Syntax_Embeddings.id_norm_cb in
           ((let uu____4656 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding") in
             if uu____4656
             then
               let uu____4657 = FStar_Syntax_Print.term_to_string t0 in
               let uu____4658 = FStar_Syntax_Print.term_to_string tv in
               FStar_Util.print2 ">> Inspected (%s) ~> (%s)\n" uu____4657
                 uu____4658
             else ());
            (let t2 =
               let uu____4663 =
                 let uu____4674 = FStar_Syntax_Syntax.as_arg tv in
                 [uu____4674] in
               FStar_Syntax_Util.mk_app
                 (FStar_Reflection_Data.refl_constant_term
                    FStar_Reflection_Data.fstar_refl_pack_ln) uu____4663 in
             encode_term t2 env))
       | FStar_Syntax_Syntax.Tm_meta
           (t2, FStar_Syntax_Syntax.Meta_pattern uu____4700) ->
           encode_term t2
             (let uu___674_4726 = env in
              {
                FStar_SMTEncoding_Env.bvar_bindings =
                  (uu___674_4726.FStar_SMTEncoding_Env.bvar_bindings);
                FStar_SMTEncoding_Env.fvar_bindings =
                  (uu___674_4726.FStar_SMTEncoding_Env.fvar_bindings);
                FStar_SMTEncoding_Env.depth =
                  (uu___674_4726.FStar_SMTEncoding_Env.depth);
                FStar_SMTEncoding_Env.tcenv =
                  (uu___674_4726.FStar_SMTEncoding_Env.tcenv);
                FStar_SMTEncoding_Env.warn =
                  (uu___674_4726.FStar_SMTEncoding_Env.warn);
                FStar_SMTEncoding_Env.nolabels =
                  (uu___674_4726.FStar_SMTEncoding_Env.nolabels);
                FStar_SMTEncoding_Env.use_zfuel_name =
                  (uu___674_4726.FStar_SMTEncoding_Env.use_zfuel_name);
                FStar_SMTEncoding_Env.encode_non_total_function_typ =
                  (uu___674_4726.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                FStar_SMTEncoding_Env.current_module_name =
                  (uu___674_4726.FStar_SMTEncoding_Env.current_module_name);
                FStar_SMTEncoding_Env.encoding_quantifier = false;
                FStar_SMTEncoding_Env.global_cache =
                  (uu___674_4726.FStar_SMTEncoding_Env.global_cache)
              })
       | FStar_Syntax_Syntax.Tm_meta (t2, uu____4728) -> encode_term t2 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t2 = FStar_SMTEncoding_Env.lookup_term_var env x in (t2, [])
       | FStar_Syntax_Syntax.Tm_fvar v ->
           let encode_freev uu____4745 =
             let fvb =
               FStar_SMTEncoding_Env.lookup_free_var_name env
                 v.FStar_Syntax_Syntax.fv_name in
             let tok =
               FStar_SMTEncoding_Env.lookup_free_var env
                 v.FStar_Syntax_Syntax.fv_name in
             let tkey_hash = FStar_SMTEncoding_Term.hash_of_term tok in
             let uu____4749 =
               if fvb.FStar_SMTEncoding_Env.smt_arity > Prims.int_zero
               then
                 match tok.FStar_SMTEncoding_Term.tm with
                 | FStar_SMTEncoding_Term.FreeV uu____4768 ->
                     let sym_name =
                       let uu____4776 = FStar_Util.digest_of_string tkey_hash in
                       Prims.op_Hat "@kick_partial_app_" uu____4776 in
                     let uu____4777 =
                       let uu____4780 =
                         let uu____4781 =
                           let uu____4788 =
                             FStar_SMTEncoding_Term.kick_partial_app tok in
                           (uu____4788,
                             (FStar_Pervasives_Native.Some "kick_partial_app"),
                             sym_name) in
                         FStar_SMTEncoding_Util.mkAssume uu____4781 in
                       [uu____4780] in
                     (uu____4777, sym_name)
                 | FStar_SMTEncoding_Term.App (uu____4791, []) ->
                     let sym_name =
                       let uu____4795 = FStar_Util.digest_of_string tkey_hash in
                       Prims.op_Hat "@kick_partial_app_" uu____4795 in
                     let uu____4796 =
                       let uu____4799 =
                         let uu____4800 =
                           let uu____4807 =
                             FStar_SMTEncoding_Term.kick_partial_app tok in
                           (uu____4807,
                             (FStar_Pervasives_Native.Some "kick_partial_app"),
                             sym_name) in
                         FStar_SMTEncoding_Util.mkAssume uu____4800 in
                       [uu____4799] in
                     (uu____4796, sym_name)
                 | uu____4810 -> ([], "")
               else ([], "") in
             match uu____4749 with
             | (aux_decls, sym_name) ->
                 let uu____4826 =
                   if aux_decls = []
                   then
                     FStar_All.pipe_right []
                       FStar_SMTEncoding_Term.mk_decls_trivial
                   else
                     FStar_SMTEncoding_Term.mk_decls sym_name tkey_hash
                       aux_decls [] in
                 (tok, uu____4826) in
           let uu____4832 = head_redex env t1 in
           if uu____4832
           then
             let uu____4837 = maybe_whnf env t1 in
             (match uu____4837 with
              | FStar_Pervasives_Native.None -> encode_freev ()
              | FStar_Pervasives_Native.Some t2 -> encode_term t2 env)
           else encode_freev ()
       | FStar_Syntax_Syntax.Tm_type uu____4846 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t2, uu____4848) -> encode_term t2 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders, c) ->
           let module_name = env.FStar_SMTEncoding_Env.current_module_name in
           let uu____4877 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____4877 with
            | (binders1, res) ->
                let uu____4888 =
                  (env.FStar_SMTEncoding_Env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____4888
                then
                  let uu____4893 =
                    encode_binders FStar_Pervasives_Native.None binders1 env in
                  (match uu____4893 with
                   | (vars, guards_l, env', decls, uu____4918) ->
                       let fsym =
                         let uu____4932 =
                           let uu____4937 =
                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                               module_name "f" in
                           (uu____4937, FStar_SMTEncoding_Term.Term_sort) in
                         FStar_SMTEncoding_Term.mk_fv uu____4932 in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____4940 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___733_4949 =
                              env.FStar_SMTEncoding_Env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___733_4949.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___733_4949.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___733_4949.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___733_4949.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___733_4949.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___733_4949.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___733_4949.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___733_4949.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___733_4949.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___733_4949.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___733_4949.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___733_4949.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___733_4949.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___733_4949.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___733_4949.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___733_4949.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___733_4949.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___733_4949.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___733_4949.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___733_4949.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___733_4949.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___733_4949.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___733_4949.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___733_4949.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___733_4949.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___733_4949.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___733_4949.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___733_4949.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___733_4949.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___733_4949.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___733_4949.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___733_4949.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___733_4949.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___733_4949.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___733_4949.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___733_4949.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___733_4949.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___733_4949.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___733_4949.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___733_4949.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___733_4949.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___733_4949.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___733_4949.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___733_4949.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___733_4949.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___733_4949.FStar_TypeChecker_Env.enable_defer_to_tac)
                            }) res in
                       (match uu____4940 with
                        | (pre_opt, res_t) ->
                            let uu____4960 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app in
                            (match uu____4960 with
                             | (res_pred, decls') ->
                                 let uu____4971 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None ->
                                       let uu____4984 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards_l in
                                       (uu____4984, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____4988 =
                                         encode_formula pre env' in
                                       (match uu____4988 with
                                        | (guard, decls0) ->
                                            let uu____5001 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards_l) in
                                            (uu____5001, decls0)) in
                                 (match uu____4971 with
                                  | (guards, guard_decls) ->
                                      let is_pure =
                                        let uu____5015 =
                                          FStar_All.pipe_right res
                                            (FStar_TypeChecker_Normalize.ghost_to_pure
                                               env.FStar_SMTEncoding_Env.tcenv) in
                                        FStar_All.pipe_right uu____5015
                                          FStar_Syntax_Util.is_pure_comp in
                                      let t_interp =
                                        let uu____5023 =
                                          let uu____5034 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards, res_pred) in
                                          ([[app]], vars, uu____5034) in
                                        FStar_SMTEncoding_Term.mkForall
                                          t1.FStar_Syntax_Syntax.pos
                                          uu____5023 in
                                      let t_interp1 =
                                        let tot_fun_axioms =
                                          isTotFun_axioms
                                            t1.FStar_Syntax_Syntax.pos f vars
                                            guards_l is_pure in
                                        FStar_SMTEncoding_Util.mkAnd
                                          (t_interp, tot_fun_axioms) in
                                      let cvars =
                                        let uu____5054 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp1 in
                                        FStar_All.pipe_right uu____5054
                                          (FStar_List.filter
                                             (fun x ->
                                                let uu____5071 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    x in
                                                let uu____5072 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    fsym in
                                                uu____5071 <> uu____5072)) in
                                      let tkey =
                                        FStar_SMTEncoding_Term.mkForall
                                          t1.FStar_Syntax_Syntax.pos
                                          ([], (fsym :: cvars), t_interp1) in
                                      let prefix =
                                        if is_pure
                                        then "Tm_arrow_"
                                        else "Tm_ghost_arrow_" in
                                      let tkey_hash =
                                        let uu____5089 =
                                          FStar_SMTEncoding_Term.hash_of_term
                                            tkey in
                                        Prims.op_Hat prefix uu____5089 in
                                      let tsym =
                                        let uu____5091 =
                                          FStar_Util.digest_of_string
                                            tkey_hash in
                                        Prims.op_Hat prefix uu____5091 in
                                      let cvar_sorts =
                                        FStar_List.map
                                          FStar_SMTEncoding_Term.fv_sort
                                          cvars in
                                      let caption =
                                        let uu____5102 =
                                          FStar_Options.log_queries () in
                                        if uu____5102
                                        then
                                          let uu____5103 =
                                            let uu____5104 =
                                              FStar_TypeChecker_Normalize.term_to_string
                                                env.FStar_SMTEncoding_Env.tcenv
                                                t0 in
                                            FStar_Util.replace_char
                                              uu____5104 10 32 in
                                          FStar_Pervasives_Native.Some
                                            uu____5103
                                        else FStar_Pervasives_Native.None in
                                      let tdecl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (tsym, cvar_sorts,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            caption) in
                                      let t2 =
                                        let uu____5110 =
                                          let uu____5117 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              cvars in
                                          (tsym, uu____5117) in
                                        FStar_SMTEncoding_Util.mkApp
                                          uu____5110 in
                                      let t_has_kind =
                                        FStar_SMTEncoding_Term.mk_HasType t2
                                          FStar_SMTEncoding_Term.mk_Term_type in
                                      let k_assumption =
                                        let a_name =
                                          Prims.op_Hat "kinding_" tsym in
                                        let uu____5131 =
                                          let uu____5138 =
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              ([[t_has_kind]], cvars,
                                                t_has_kind) in
                                          (uu____5138,
                                            (FStar_Pervasives_Native.Some
                                               a_name), a_name) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____5131 in
                                      let f_has_t =
                                        FStar_SMTEncoding_Term.mk_HasType f
                                          t2 in
                                      let f_has_t_z =
                                        FStar_SMTEncoding_Term.mk_HasTypeZ f
                                          t2 in
                                      let pre_typing =
                                        let a_name =
                                          Prims.op_Hat "pre_typing_" tsym in
                                        let uu____5151 =
                                          let uu____5158 =
                                            let uu____5159 =
                                              let uu____5170 =
                                                let uu____5171 =
                                                  let uu____5176 =
                                                    let uu____5177 =
                                                      FStar_SMTEncoding_Term.mk_PreType
                                                        f in
                                                    FStar_SMTEncoding_Term.mk_tester
                                                      "Tm_arrow" uu____5177 in
                                                  (f_has_t, uu____5176) in
                                                FStar_SMTEncoding_Util.mkImp
                                                  uu____5171 in
                                              ([[f_has_t]], (fsym :: cvars),
                                                uu____5170) in
                                            let uu____5192 =
                                              mkForall_fuel module_name
                                                t0.FStar_Syntax_Syntax.pos in
                                            uu____5192 uu____5159 in
                                          (uu____5158,
                                            (FStar_Pervasives_Native.Some
                                               "pre-typing for functions"),
                                            (Prims.op_Hat module_name
                                               (Prims.op_Hat "_" a_name))) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____5151 in
                                      let t_interp2 =
                                        let a_name =
                                          Prims.op_Hat "interpretation_" tsym in
                                        let uu____5209 =
                                          let uu____5216 =
                                            let uu____5217 =
                                              let uu____5228 =
                                                FStar_SMTEncoding_Util.mkIff
                                                  (f_has_t_z, t_interp1) in
                                              ([[f_has_t_z]], (fsym ::
                                                cvars), uu____5228) in
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              uu____5217 in
                                          (uu____5216,
                                            (FStar_Pervasives_Native.Some
                                               a_name),
                                            (Prims.op_Hat module_name
                                               (Prims.op_Hat "_" a_name))) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____5209 in
                                      let t_decls =
                                        [tdecl;
                                        k_assumption;
                                        pre_typing;
                                        t_interp2] in
                                      let uu____5246 =
                                        let uu____5247 =
                                          let uu____5250 =
                                            let uu____5253 =
                                              FStar_SMTEncoding_Term.mk_decls
                                                tsym tkey_hash t_decls
                                                (FStar_List.append decls
                                                   (FStar_List.append decls'
                                                      guard_decls)) in
                                            FStar_List.append guard_decls
                                              uu____5253 in
                                          FStar_List.append decls' uu____5250 in
                                        FStar_List.append decls uu____5247 in
                                      (t2, uu____5246)))))
                else
                  (let tkey_hash =
                     let uu____5258 =
                       encode_binders FStar_Pervasives_Native.None binders1
                         env in
                     match uu____5258 with
                     | (vars, guards_l, env_bs, uu____5278, uu____5279) ->
                         let c1 =
                           let uu____5295 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev
                               env.FStar_SMTEncoding_Env.tcenv res in
                           FStar_All.pipe_right uu____5295
                             FStar_Syntax_Syntax.mk_Comp in
                         let uu____5298 =
                           let uu____5303 =
                             FStar_All.pipe_right c1
                               FStar_Syntax_Util.comp_result in
                           encode_term uu____5303 env_bs in
                         (match uu____5298 with
                          | (ct, uu____5307) ->
                              let uu____5308 =
                                let uu____5315 =
                                  FStar_All.pipe_right c1
                                    FStar_Syntax_Util.comp_effect_args in
                                encode_args uu____5315 env_bs in
                              (match uu____5308 with
                               | (effect_args, uu____5317) ->
                                   let tkey =
                                     let uu____5323 =
                                       let uu____5334 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           (FStar_List.append guards_l
                                              (FStar_List.append [ct]
                                                 effect_args)) in
                                       ([], vars, uu____5334) in
                                     FStar_SMTEncoding_Term.mkForall
                                       t1.FStar_Syntax_Syntax.pos uu____5323 in
                                   let tkey_hash =
                                     let uu____5342 =
                                       let uu____5343 =
                                         FStar_SMTEncoding_Term.hash_of_term
                                           tkey in
                                       let uu____5344 =
                                         let uu____5345 =
                                           let uu____5346 =
                                             FStar_All.pipe_right c1
                                               FStar_Syntax_Util.comp_effect_name in
                                           FStar_All.pipe_right uu____5346
                                             FStar_Ident.string_of_lid in
                                         Prims.op_Hat "@Effect=" uu____5345 in
                                       Prims.op_Hat uu____5343 uu____5344 in
                                     Prims.op_Hat "Non_total_Tm_arrow"
                                       uu____5342 in
                                   FStar_Util.digest_of_string tkey_hash)) in
                   let tsym = Prims.op_Hat "Non_total_Tm_arrow_" tkey_hash in
                   let tdecl =
                     FStar_SMTEncoding_Term.DeclFun
                       (tsym, [], FStar_SMTEncoding_Term.Term_sort,
                         FStar_Pervasives_Native.None) in
                   let t2 = FStar_SMTEncoding_Util.mkApp (tsym, []) in
                   let t_kinding =
                     let a_name =
                       Prims.op_Hat "non_total_function_typing_" tsym in
                     let uu____5358 =
                       let uu____5365 =
                         FStar_SMTEncoding_Term.mk_HasType t2
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____5365,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"), a_name) in
                     FStar_SMTEncoding_Util.mkAssume uu____5358 in
                   let fsym =
                     FStar_SMTEncoding_Term.mk_fv
                       ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t2 in
                   let t_interp =
                     let a_name = Prims.op_Hat "pre_typing_" tsym in
                     let uu____5371 =
                       let uu____5378 =
                         let uu____5379 =
                           let uu____5390 =
                             let uu____5391 =
                               let uu____5396 =
                                 let uu____5397 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____5397 in
                               (f_has_t, uu____5396) in
                             FStar_SMTEncoding_Util.mkImp uu____5391 in
                           ([[f_has_t]], [fsym], uu____5390) in
                         let uu____5418 =
                           mkForall_fuel module_name
                             t0.FStar_Syntax_Syntax.pos in
                         uu____5418 uu____5379 in
                       (uu____5378, (FStar_Pervasives_Native.Some a_name),
                         a_name) in
                     FStar_SMTEncoding_Util.mkAssume uu____5371 in
                   let uu____5433 =
                     FStar_SMTEncoding_Term.mk_decls tsym tkey_hash
                       [tdecl; t_kinding; t_interp] [] in
                   (t2, uu____5433)))
       | FStar_Syntax_Syntax.Tm_refine uu____5434 ->
           let uu____5441 =
             let steps =
               [FStar_TypeChecker_Env.Weak;
               FStar_TypeChecker_Env.HNF;
               FStar_TypeChecker_Env.EraseUniverses] in
             let uu____5451 =
               normalize_refinement steps env.FStar_SMTEncoding_Env.tcenv t0 in
             match uu____5451 with
             | {
                 FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f);
                 FStar_Syntax_Syntax.pos = uu____5460;
                 FStar_Syntax_Syntax.vars = uu____5461;_} ->
                 let uu____5468 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f in
                 (match uu____5468 with
                  | (b, f1) ->
                      let uu____5495 =
                        let uu____5496 = FStar_List.hd b in
                        FStar_Pervasives_Native.fst uu____5496 in
                      (uu____5495, f1))
             | uu____5513 -> failwith "impossible" in
           (match uu____5441 with
            | (x, f) ->
                let uu____5530 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____5530 with
                 | (base_t, decls) ->
                     let uu____5541 =
                       FStar_SMTEncoding_Env.gen_term_var env x in
                     (match uu____5541 with
                      | (x1, xtm, env') ->
                          let uu____5555 = encode_formula f env' in
                          (match uu____5555 with
                           | (refinement, decls') ->
                               let uu____5566 =
                                 FStar_SMTEncoding_Env.fresh_fvar
                                   env.FStar_SMTEncoding_Env.current_module_name
                                   "f" FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____5566 with
                                | (fsym, fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____5588 =
                                        let uu____5597 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____5606 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____5597
                                          uu____5606 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____5588 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun y ->
                                              (let uu____5650 =
                                                 FStar_SMTEncoding_Term.fv_name
                                                   y in
                                               uu____5650 <> x1) &&
                                                (let uu____5652 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     y in
                                                 uu____5652 <> fsym))) in
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
                                    ((let uu____5676 =
                                        FStar_TypeChecker_Env.debug
                                          env.FStar_SMTEncoding_Env.tcenv
                                          (FStar_Options.Other "SMTEncoding") in
                                      if uu____5676
                                      then
                                        let uu____5677 =
                                          FStar_Syntax_Print.term_to_string f in
                                        let uu____5678 =
                                          FStar_Util.digest_of_string
                                            tkey_hash in
                                        FStar_Util.print3
                                          "Encoding Tm_refine %s with tkey_hash %s and digest %s\n"
                                          uu____5677 tkey_hash uu____5678
                                      else ());
                                     (let tsym =
                                        let uu____5681 =
                                          FStar_Util.digest_of_string
                                            tkey_hash in
                                        Prims.op_Hat "Tm_refine_" uu____5681 in
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
                                        let uu____5695 =
                                          let uu____5702 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              cvars1 in
                                          (tsym, uu____5702) in
                                        FStar_SMTEncoding_Util.mkApp
                                          uu____5695 in
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
                                        let uu____5719 =
                                          let uu____5726 =
                                            let uu____5727 =
                                              let uu____5738 =
                                                FStar_SMTEncoding_Util.mkIff
                                                  (t_haseq_ref, t_haseq_base) in
                                              ([[t_haseq_ref]], cvars1,
                                                uu____5738) in
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              uu____5727 in
                                          (uu____5726,
                                            (FStar_Pervasives_Native.Some
                                               (Prims.op_Hat "haseq for "
                                                  tsym)),
                                            (Prims.op_Hat "haseq" tsym)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____5719 in
                                      let t_kinding =
                                        let uu____5748 =
                                          let uu____5755 =
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              ([[t_has_kind]], cvars1,
                                                t_has_kind) in
                                          (uu____5755,
                                            (FStar_Pervasives_Native.Some
                                               "refinement kinding"),
                                            (Prims.op_Hat
                                               "refinement_kinding_" tsym)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____5748 in
                                      let t_interp =
                                        let uu____5765 =
                                          let uu____5772 =
                                            let uu____5773 =
                                              let uu____5784 =
                                                FStar_SMTEncoding_Util.mkIff
                                                  (x_has_t, encoding) in
                                              ([[x_has_t]], (ffv :: xfv ::
                                                cvars1), uu____5784) in
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              uu____5773 in
                                          (uu____5772,
                                            (FStar_Pervasives_Native.Some
                                               "refinement_interpretation"),
                                            (Prims.op_Hat
                                               "refinement_interpretation_"
                                               tsym)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____5765 in
                                      let t_decls =
                                        [tdecl; t_kinding; t_interp; t_haseq] in
                                      let uu____5808 =
                                        let uu____5809 =
                                          let uu____5812 =
                                            FStar_SMTEncoding_Term.mk_decls
                                              tsym tkey_hash t_decls
                                              (FStar_List.append decls decls') in
                                          FStar_List.append decls' uu____5812 in
                                        FStar_List.append decls uu____5809 in
                                      (t2, uu____5808))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv, uu____5816) ->
           let ttm =
             let uu____5834 =
               FStar_Syntax_Unionfind.uvar_id
                 uv.FStar_Syntax_Syntax.ctx_uvar_head in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____5834 in
           let uu____5835 =
             encode_term_pred FStar_Pervasives_Native.None
               uv.FStar_Syntax_Syntax.ctx_uvar_typ env ttm in
           (match uu____5835 with
            | (t_has_k, decls) ->
                let d =
                  let uu____5847 =
                    let uu____5854 =
                      let uu____5855 =
                        let uu____5856 =
                          let uu____5857 =
                            FStar_Syntax_Unionfind.uvar_id
                              uv.FStar_Syntax_Syntax.ctx_uvar_head in
                          FStar_Util.string_of_int uu____5857 in
                        FStar_Util.format1 "uvar_typing_%s" uu____5856 in
                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                        uu____5855 in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____5854) in
                  FStar_SMTEncoding_Util.mkAssume uu____5847 in
                let uu____5858 =
                  let uu____5859 =
                    FStar_All.pipe_right [d]
                      FStar_SMTEncoding_Term.mk_decls_trivial in
                  FStar_List.append decls uu____5859 in
                (ttm, uu____5858))
       | FStar_Syntax_Syntax.Tm_app uu____5866 ->
           let uu____5883 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____5883 with
            | (head, args_e) ->
                let uu____5930 =
                  let uu____5947 = head_redex env head in
                  if uu____5947
                  then
                    let uu____5964 = maybe_whnf env t0 in
                    match uu____5964 with
                    | FStar_Pervasives_Native.None -> (head, args_e)
                    | FStar_Pervasives_Native.Some t2 ->
                        FStar_Syntax_Util.head_and_args t2
                  else (head, args_e) in
                (match uu____5930 with
                 | (head1, args_e1) ->
                     let uu____6039 =
                       let uu____6054 =
                         let uu____6055 = FStar_Syntax_Subst.compress head1 in
                         uu____6055.FStar_Syntax_Syntax.n in
                       (uu____6054, args_e1) in
                     (match uu____6039 with
                      | uu____6072 when is_arithmetic_primitive head1 args_e1
                          -> encode_arith_term env head1 args_e1
                      | uu____6095 when is_BitVector_primitive head1 args_e1
                          -> encode_BitVector_term env head1 args_e1
                      | (FStar_Syntax_Syntax.Tm_fvar fv, uu____6113) when
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
                            FStar_Syntax_Syntax.pos = uu____6135;
                            FStar_Syntax_Syntax.vars = uu____6136;_},
                          uu____6137),
                         uu____6138) when
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
                            FStar_Syntax_Syntax.pos = uu____6164;
                            FStar_Syntax_Syntax.vars = uu____6165;_},
                          uu____6166),
                         (v0, uu____6168)::(v1, uu____6170)::(v2, uu____6172)::[])
                          when
                          FStar_Syntax_Syntax.fv_eq_lid fv
                            FStar_Parser_Const.lexcons_lid
                          ->
                          let uu____6243 = encode_term v0 env in
                          (match uu____6243 with
                           | (v01, decls0) ->
                               let uu____6254 = encode_term v1 env in
                               (match uu____6254 with
                                | (v11, decls1) ->
                                    let uu____6265 = encode_term v2 env in
                                    (match uu____6265 with
                                     | (v21, decls2) ->
                                         let uu____6276 =
                                           FStar_SMTEncoding_Util.mk_LexCons
                                             v01 v11 v21 in
                                         (uu____6276,
                                           (FStar_List.append decls0
                                              (FStar_List.append decls1
                                                 decls2))))))
                      | (FStar_Syntax_Syntax.Tm_fvar fv,
                         (v0, uu____6279)::(v1, uu____6281)::(v2, uu____6283)::[])
                          when
                          FStar_Syntax_Syntax.fv_eq_lid fv
                            FStar_Parser_Const.lexcons_lid
                          ->
                          let uu____6350 = encode_term v0 env in
                          (match uu____6350 with
                           | (v01, decls0) ->
                               let uu____6361 = encode_term v1 env in
                               (match uu____6361 with
                                | (v11, decls1) ->
                                    let uu____6372 = encode_term v2 env in
                                    (match uu____6372 with
                                     | (v21, decls2) ->
                                         let uu____6383 =
                                           FStar_SMTEncoding_Util.mk_LexCons
                                             v01 v11 v21 in
                                         (uu____6383,
                                           (FStar_List.append decls0
                                              (FStar_List.append decls1
                                                 decls2))))))
                      | (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range_of), (arg, uu____6385)::[])
                          ->
                          encode_const
                            (FStar_Const.Const_range
                               (arg.FStar_Syntax_Syntax.pos)) env
                      | (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_set_range_of),
                         (arg, uu____6421)::(rng, uu____6423)::[]) ->
                          encode_term arg env
                      | (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify), uu____6474) ->
                          let e0 =
                            let uu____6496 = FStar_List.hd args_e1 in
                            FStar_TypeChecker_Util.reify_body_with_arg
                              env.FStar_SMTEncoding_Env.tcenv [] head1
                              uu____6496 in
                          ((let uu____6506 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   env.FStar_SMTEncoding_Env.tcenv)
                                (FStar_Options.Other "SMTEncodingReify") in
                            if uu____6506
                            then
                              let uu____6507 =
                                FStar_Syntax_Print.term_to_string e0 in
                              FStar_Util.print1
                                "Result of normalization %s\n" uu____6507
                            else ());
                           (let e =
                              let uu____6510 =
                                FStar_TypeChecker_Util.remove_reify e0 in
                              let uu____6511 = FStar_List.tl args_e1 in
                              FStar_Syntax_Syntax.mk_Tm_app uu____6510
                                uu____6511 t0.FStar_Syntax_Syntax.pos in
                            encode_term e env))
                      | (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____6520),
                         (arg, uu____6522)::[]) -> encode_term arg env
                      | uu____6557 ->
                          let uu____6572 = encode_args args_e1 env in
                          (match uu____6572 with
                           | (args, decls) ->
                               let encode_partial_app ht_opt =
                                 let uu____6641 = encode_term head1 env in
                                 match uu____6641 with
                                 | (smt_head, decls') ->
                                     let app_tm = mk_Apply_args smt_head args in
                                     (match ht_opt with
                                      | uu____6661 when
                                          Prims.int_one = Prims.int_one ->
                                          (app_tm,
                                            (FStar_List.append decls decls'))
                                      | FStar_Pervasives_Native.Some
                                          (head_type, formals, c) ->
                                          ((let uu____6730 =
                                              FStar_TypeChecker_Env.debug
                                                env.FStar_SMTEncoding_Env.tcenv
                                                (FStar_Options.Other
                                                   "PartialApp") in
                                            if uu____6730
                                            then
                                              let uu____6731 =
                                                FStar_Syntax_Print.term_to_string
                                                  head1 in
                                              let uu____6732 =
                                                FStar_Syntax_Print.term_to_string
                                                  head_type in
                                              let uu____6733 =
                                                FStar_Syntax_Print.binders_to_string
                                                  ", " formals in
                                              let uu____6734 =
                                                FStar_Syntax_Print.comp_to_string
                                                  c in
                                              let uu____6735 =
                                                FStar_Syntax_Print.args_to_string
                                                  args_e1 in
                                              FStar_Util.print5
                                                "Encoding partial application:\n\thead=%s\n\thead_type=%s\n\tformals=%s\n\tcomp=%s\n\tactual args=%s\n"
                                                uu____6731 uu____6732
                                                uu____6733 uu____6734
                                                uu____6735
                                            else ());
                                           (let uu____6737 =
                                              FStar_Util.first_N
                                                (FStar_List.length args_e1)
                                                formals in
                                            match uu____6737 with
                                            | (formals1, rest) ->
                                                let subst =
                                                  FStar_List.map2
                                                    (fun uu____6835 ->
                                                       fun uu____6836 ->
                                                         match (uu____6835,
                                                                 uu____6836)
                                                         with
                                                         | ((bv, uu____6866),
                                                            (a, uu____6868))
                                                             ->
                                                             FStar_Syntax_Syntax.NT
                                                               (bv, a))
                                                    formals1 args_e1 in
                                                let ty =
                                                  let uu____6900 =
                                                    FStar_Syntax_Util.arrow
                                                      rest c in
                                                  FStar_All.pipe_right
                                                    uu____6900
                                                    (FStar_Syntax_Subst.subst
                                                       subst) in
                                                ((let uu____6904 =
                                                    FStar_TypeChecker_Env.debug
                                                      env.FStar_SMTEncoding_Env.tcenv
                                                      (FStar_Options.Other
                                                         "PartialApp") in
                                                  if uu____6904
                                                  then
                                                    let uu____6905 =
                                                      FStar_Syntax_Print.term_to_string
                                                        ty in
                                                    FStar_Util.print1
                                                      "Encoding partial application, after subst:\n\tty=%s\n"
                                                      uu____6905
                                                  else ());
                                                 (let uu____6907 =
                                                    let uu____6920 =
                                                      FStar_List.fold_left2
                                                        (fun uu____6955 ->
                                                           fun uu____6956 ->
                                                             fun e ->
                                                               match 
                                                                 (uu____6955,
                                                                   uu____6956)
                                                               with
                                                               | ((t_hyps,
                                                                   decls1),
                                                                  (bv,
                                                                   uu____6997))
                                                                   ->
                                                                   let t2 =
                                                                    FStar_Syntax_Subst.subst
                                                                    subst
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                   let uu____7025
                                                                    =
                                                                    encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    t2 env e in
                                                                   (match uu____7025
                                                                    with
                                                                    | 
                                                                    (t_hyp,
                                                                    decls'1)
                                                                    ->
                                                                    ((
                                                                    let uu____7041
                                                                    =
                                                                    FStar_TypeChecker_Env.debug
                                                                    env.FStar_SMTEncoding_Env.tcenv
                                                                    (FStar_Options.Other
                                                                    "PartialApp") in
                                                                    if
                                                                    uu____7041
                                                                    then
                                                                    let uu____7042
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2 in
                                                                    let uu____7043
                                                                    =
                                                                    FStar_SMTEncoding_Term.print_smt_term
                                                                    t_hyp in
                                                                    FStar_Util.print2
                                                                    "Encoded typing hypothesis for %s ... got %s\n"
                                                                    uu____7042
                                                                    uu____7043
                                                                    else ());
                                                                    ((t_hyp
                                                                    ::
                                                                    t_hyps),
                                                                    (FStar_List.append
                                                                    decls1
                                                                    decls'1)))))
                                                        ([], []) formals1
                                                        args in
                                                    match uu____6920 with
                                                    | (t_hyps, decls1) ->
                                                        let uu____7075 =
                                                          match smt_head.FStar_SMTEncoding_Term.tm
                                                          with
                                                          | FStar_SMTEncoding_Term.FreeV
                                                              uu____7084 ->
                                                              encode_term_pred
                                                                FStar_Pervasives_Native.None
                                                                head_type env
                                                                smt_head
                                                          | uu____7091 ->
                                                              (FStar_SMTEncoding_Util.mkTrue,
                                                                []) in
                                                        (match uu____7075
                                                         with
                                                         | (t_head_hyp,
                                                            decls'1) ->
                                                             let hyp =
                                                               FStar_SMTEncoding_Term.mk_and_l
                                                                 (t_head_hyp
                                                                 :: t_hyps)
                                                                 FStar_Range.dummyRange in
                                                             let uu____7107 =
                                                               encode_term_pred
                                                                 FStar_Pervasives_Native.None
                                                                 ty env
                                                                 app_tm in
                                                             (match uu____7107
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
                                                                  let uu____7129
                                                                    =
                                                                    let uu____7136
                                                                    =
                                                                    FStar_SMTEncoding_Term.fvs_subset_of
                                                                    cvars
                                                                    app_tm_vars in
                                                                    if
                                                                    uu____7136
                                                                    then
                                                                    ([app_tm],
                                                                    app_tm_vars)
                                                                    else
                                                                    (let uu____7146
                                                                    =
                                                                    let uu____7147
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    has_type_conclusion in
                                                                    FStar_SMTEncoding_Term.fvs_subset_of
                                                                    cvars
                                                                    uu____7147 in
                                                                    if
                                                                    uu____7146
                                                                    then
                                                                    ([has_type_conclusion],
                                                                    cvars)
                                                                    else
                                                                    ((
                                                                    let uu____7158
                                                                    =
                                                                    let uu____7163
                                                                    =
                                                                    let uu____7164
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t0 in
                                                                    FStar_Util.format1
                                                                    "No SMT pattern for partial application %s"
                                                                    uu____7164 in
                                                                    (FStar_Errors.Warning_SMTPatternIllFormed,
                                                                    uu____7163) in
                                                                    FStar_Errors.log_issue
                                                                    t0.FStar_Syntax_Syntax.pos
                                                                    uu____7158);
                                                                    ([],
                                                                    cvars))) in
                                                                  (match uu____7129
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
                                                  match uu____6907 with
                                                  | (vars, pattern1,
                                                     has_type, decls'') ->
                                                      ((let uu____7208 =
                                                          FStar_TypeChecker_Env.debug
                                                            env.FStar_SMTEncoding_Env.tcenv
                                                            (FStar_Options.Other
                                                               "PartialApp") in
                                                        if uu____7208
                                                        then
                                                          let uu____7209 =
                                                            FStar_SMTEncoding_Term.print_smt_term
                                                              has_type in
                                                          FStar_Util.print1
                                                            "Encoding partial application, after SMT encoded predicate:\n\t=%s\n"
                                                            uu____7209
                                                        else ());
                                                       (let tkey_hash =
                                                          FStar_SMTEncoding_Term.hash_of_term
                                                            app_tm in
                                                        let e_typing =
                                                          let uu____7213 =
                                                            let uu____7220 =
                                                              FStar_SMTEncoding_Term.mkForall
                                                                t0.FStar_Syntax_Syntax.pos
                                                                ([pattern1],
                                                                  vars,
                                                                  has_type) in
                                                            let uu____7229 =
                                                              let uu____7230
                                                                =
                                                                let uu____7231
                                                                  =
                                                                  FStar_SMTEncoding_Term.hash_of_term
                                                                    app_tm in
                                                                FStar_Util.digest_of_string
                                                                  uu____7231 in
                                                              Prims.op_Hat
                                                                "partial_app_typing_"
                                                                uu____7230 in
                                                            (uu____7220,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Partial app typing"),
                                                              uu____7229) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____7213 in
                                                        let uu____7232 =
                                                          let uu____7235 =
                                                            let uu____7238 =
                                                              let uu____7241
                                                                =
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
                                                                uu____7241 in
                                                            FStar_List.append
                                                              decls'
                                                              uu____7238 in
                                                          FStar_List.append
                                                            decls uu____7235 in
                                                        (app_tm, uu____7232)))))))
                                      | FStar_Pervasives_Native.None ->
                                          failwith "impossible") in
                               let encode_full_app fv =
                                 let uu____7284 =
                                   FStar_SMTEncoding_Env.lookup_free_var_sym
                                     env fv in
                                 match uu____7284 with
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
                                        FStar_Syntax_Syntax.pos = uu____7324;
                                        FStar_Syntax_Syntax.vars = uu____7325;_},
                                      uu____7326)
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
                                        FStar_Syntax_Syntax.pos = uu____7333;
                                        FStar_Syntax_Syntax.vars = uu____7334;_},
                                      uu____7335)
                                     ->
                                     let uu____7340 =
                                       let uu____7341 =
                                         let uu____7346 =
                                           FStar_TypeChecker_Env.lookup_lid
                                             env.FStar_SMTEncoding_Env.tcenv
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                         FStar_All.pipe_right uu____7346
                                           FStar_Pervasives_Native.fst in
                                       FStar_All.pipe_right uu____7341
                                         FStar_Pervasives_Native.snd in
                                     FStar_Pervasives_Native.Some uu____7340
                                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                                     let uu____7376 =
                                       let uu____7377 =
                                         let uu____7382 =
                                           FStar_TypeChecker_Env.lookup_lid
                                             env.FStar_SMTEncoding_Env.tcenv
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                         FStar_All.pipe_right uu____7382
                                           FStar_Pervasives_Native.fst in
                                       FStar_All.pipe_right uu____7377
                                         FStar_Pervasives_Native.snd in
                                     FStar_Pervasives_Native.Some uu____7376
                                 | FStar_Syntax_Syntax.Tm_ascribed
                                     (uu____7411,
                                      (FStar_Util.Inl t2, uu____7413),
                                      uu____7414)
                                     -> FStar_Pervasives_Native.Some t2
                                 | FStar_Syntax_Syntax.Tm_ascribed
                                     (uu____7461,
                                      (FStar_Util.Inr c, uu____7463),
                                      uu____7464)
                                     ->
                                     FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Util.comp_result c)
                                 | uu____7511 -> FStar_Pervasives_Native.None in
                               (match head_type with
                                | FStar_Pervasives_Native.None ->
                                    encode_partial_app
                                      FStar_Pervasives_Native.None
                                | FStar_Pervasives_Native.Some head_type1 ->
                                    let uu____7535 =
                                      let head_type2 =
                                        let uu____7557 =
                                          normalize_refinement
                                            [FStar_TypeChecker_Env.Weak;
                                            FStar_TypeChecker_Env.HNF;
                                            FStar_TypeChecker_Env.EraseUniverses]
                                            env.FStar_SMTEncoding_Env.tcenv
                                            head_type1 in
                                        FStar_All.pipe_left
                                          FStar_Syntax_Util.unrefine
                                          uu____7557 in
                                      let uu____7560 =
                                        curried_arrow_formals_comp head_type2 in
                                      match uu____7560 with
                                      | (formals, c) ->
                                          if
                                            (FStar_List.length formals) <
                                              (FStar_List.length args)
                                          then
                                            let head_type3 =
                                              let uu____7610 =
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
                                                uu____7610 in
                                            let uu____7611 =
                                              curried_arrow_formals_comp
                                                head_type3 in
                                            (match uu____7611 with
                                             | (formals1, c1) ->
                                                 (head_type3, formals1, c1))
                                          else (head_type2, formals, c) in
                                    (match uu____7535 with
                                     | (head_type2, formals, c) ->
                                         ((let uu____7693 =
                                             FStar_TypeChecker_Env.debug
                                               env.FStar_SMTEncoding_Env.tcenv
                                               (FStar_Options.Other
                                                  "PartialApp") in
                                           if uu____7693
                                           then
                                             let uu____7694 =
                                               FStar_Syntax_Print.term_to_string
                                                 head_type2 in
                                             let uu____7695 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " formals in
                                             let uu____7696 =
                                               FStar_Syntax_Print.args_to_string
                                                 args_e1 in
                                             FStar_Util.print3
                                               "Encoding partial application, head_type = %s, formals = %s, args = %s\n"
                                               uu____7694 uu____7695
                                               uu____7696
                                           else ());
                                          (match head2.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_uinst
                                               ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_fvar
                                                    fv;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____7703;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____7704;_},
                                                uu____7705)
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
                                           | uu____7723 ->
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
           let uu____7810 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____7810 with
            | (bs1, body1, opening) ->
                let fallback uu____7833 =
                  let f =
                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                      env.FStar_SMTEncoding_Env.current_module_name "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding")) in
                  let uu____7838 =
                    let uu____7839 =
                      FStar_SMTEncoding_Term.mk_fv
                        (f, FStar_SMTEncoding_Term.Term_sort) in
                    FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV
                      uu____7839 in
                  let uu____7840 =
                    FStar_All.pipe_right [decl]
                      FStar_SMTEncoding_Term.mk_decls_trivial in
                  (uu____7838, uu____7840) in
                let is_impure rc =
                  let uu____7849 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                      env.FStar_SMTEncoding_Env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect in
                  FStar_All.pipe_right uu____7849 Prims.op_Negation in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None ->
                        let uu____7861 =
                          let uu____7874 =
                            FStar_TypeChecker_Env.get_range
                              env.FStar_SMTEncoding_Env.tcenv in
                          FStar_TypeChecker_Util.new_implicit_var
                            "SMTEncoding codomain" uu____7874
                            env.FStar_SMTEncoding_Env.tcenv
                            FStar_Syntax_Util.ktype0 in
                        (match uu____7861 with
                         | (t2, uu____7876, uu____7877) -> t2)
                    | FStar_Pervasives_Native.Some t2 -> t2 in
                  let uu____7895 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid in
                  if uu____7895
                  then
                    let uu____7898 = FStar_Syntax_Syntax.mk_Total res_typ in
                    FStar_Pervasives_Native.Some uu____7898
                  else
                    (let uu____7900 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid in
                     if uu____7900
                     then
                       let uu____7903 = FStar_Syntax_Syntax.mk_GTotal res_typ in
                       FStar_Pervasives_Native.Some uu____7903
                     else FStar_Pervasives_Native.None) in
                (match lopt with
                 | FStar_Pervasives_Native.None ->
                     ((let uu____7910 =
                         let uu____7915 =
                           let uu____7916 =
                             FStar_Syntax_Print.term_to_string t0 in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____7916 in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____7915) in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____7910);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____7918 =
                       (is_impure rc) &&
                         (let uu____7920 =
                            FStar_SMTEncoding_Util.is_smt_reifiable_rc
                              env.FStar_SMTEncoding_Env.tcenv rc in
                          Prims.op_Negation uu____7920) in
                     if uu____7918
                     then fallback ()
                     else
                       (let uu____7926 =
                          encode_binders FStar_Pervasives_Native.None bs1 env in
                        match uu____7926 with
                        | (vars, guards, envbody, decls, uu____7951) ->
                            let body2 =
                              let uu____7965 =
                                FStar_SMTEncoding_Util.is_smt_reifiable_rc
                                  env.FStar_SMTEncoding_Env.tcenv rc in
                              if uu____7965
                              then
                                FStar_TypeChecker_Util.reify_body
                                  env.FStar_SMTEncoding_Env.tcenv [] body1
                              else body1 in
                            let uu____7967 = encode_term body2 envbody in
                            (match uu____7967 with
                             | (body3, decls') ->
                                 let is_pure =
                                   FStar_Syntax_Util.is_pure_effect
                                     rc.FStar_Syntax_Syntax.residual_effect in
                                 let uu____7979 =
                                   let uu____7988 = codomain_eff rc in
                                   match uu____7988 with
                                   | FStar_Pervasives_Native.None ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c in
                                       let uu____8007 = encode_term tfun env in
                                       (match uu____8007 with
                                        | (t2, decls1) ->
                                            ((FStar_Pervasives_Native.Some t2),
                                              decls1)) in
                                 (match uu____7979 with
                                  | (arrow_t_opt, decls'') ->
                                      let key_body =
                                        let uu____8041 =
                                          let uu____8052 =
                                            let uu____8053 =
                                              let uu____8058 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____8058, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8053 in
                                          ([], vars, uu____8052) in
                                        FStar_SMTEncoding_Term.mkForall
                                          t0.FStar_Syntax_Syntax.pos
                                          uu____8041 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let uu____8066 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None ->
                                            (cvars, key_body)
                                        | FStar_Pervasives_Native.Some t2 ->
                                            let uu____8082 =
                                              let uu____8085 =
                                                let uu____8094 =
                                                  FStar_SMTEncoding_Term.free_variables
                                                    t2 in
                                                FStar_List.append uu____8094
                                                  cvars in
                                              FStar_Util.remove_dups
                                                FStar_SMTEncoding_Term.fv_eq
                                                uu____8085 in
                                            let uu____8115 =
                                              FStar_SMTEncoding_Util.mkAnd
                                                (key_body, t2) in
                                            (uu____8082, uu____8115) in
                                      (match uu____8066 with
                                       | (cvars1, key_body1) ->
                                           let tkey =
                                             FStar_SMTEncoding_Term.mkForall
                                               t0.FStar_Syntax_Syntax.pos
                                               ([], cvars1, key_body1) in
                                           let tkey_hash =
                                             FStar_SMTEncoding_Term.hash_of_term
                                               tkey in
                                           ((let uu____8137 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env.FStar_SMTEncoding_Env.tcenv)
                                                 (FStar_Options.Other
                                                    "PartialApp") in
                                             if uu____8137
                                             then
                                               let uu____8138 =
                                                 let uu____8139 =
                                                   FStar_List.map
                                                     FStar_SMTEncoding_Term.fv_name
                                                     vars in
                                                 FStar_All.pipe_right
                                                   uu____8139
                                                   (FStar_String.concat ", ") in
                                               let uu____8144 =
                                                 FStar_SMTEncoding_Term.print_smt_term
                                                   body3 in
                                               FStar_Util.print2
                                                 "Checking eta expansion of\n\tvars={%s}\n\tbody=%s\n"
                                                 uu____8138 uu____8144
                                             else ());
                                            (let uu____8146 =
                                               is_an_eta_expansion env vars
                                                 body3 in
                                             match uu____8146 with
                                             | FStar_Pervasives_Native.Some
                                                 t2 ->
                                                 ((let uu____8155 =
                                                     FStar_All.pipe_left
                                                       (FStar_TypeChecker_Env.debug
                                                          env.FStar_SMTEncoding_Env.tcenv)
                                                       (FStar_Options.Other
                                                          "PartialApp") in
                                                   if uu____8155
                                                   then
                                                     let uu____8156 =
                                                       FStar_SMTEncoding_Term.print_smt_term
                                                         t2 in
                                                     FStar_Util.print1
                                                       "Yes, is an eta expansion of\n\tcore=%s\n"
                                                       uu____8156
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
                                                   let uu____8165 =
                                                     FStar_Util.digest_of_string
                                                       tkey_hash in
                                                   Prims.op_Hat "Tm_abs_"
                                                     uu____8165 in
                                                 let fdecl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (fsym, cvar_sorts,
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       FStar_Pervasives_Native.None) in
                                                 let f =
                                                   let uu____8170 =
                                                     let uu____8177 =
                                                       FStar_List.map
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                         cvars1 in
                                                     (fsym, uu____8177) in
                                                   FStar_SMTEncoding_Util.mkApp
                                                     uu____8170 in
                                                 let app = mk_Apply f vars in
                                                 let typing_f =
                                                   match arrow_t_opt with
                                                   | FStar_Pervasives_Native.None
                                                       ->
                                                       let tot_fun_ax =
                                                         let ax =
                                                           let uu____8190 =
                                                             FStar_All.pipe_right
                                                               vars
                                                               (FStar_List.map
                                                                  (fun
                                                                    uu____8198
                                                                    ->
                                                                    FStar_SMTEncoding_Util.mkTrue)) in
                                                           isTotFun_axioms
                                                             t0.FStar_Syntax_Syntax.pos
                                                             f vars
                                                             uu____8190
                                                             is_pure in
                                                         match cvars1 with
                                                         | [] -> ax
                                                         | uu____8199 ->
                                                             FStar_SMTEncoding_Term.mkForall
                                                               t0.FStar_Syntax_Syntax.pos
                                                               ([[f]],
                                                                 cvars1, ax) in
                                                       let a_name =
                                                         Prims.op_Hat
                                                           "tot_fun_" fsym in
                                                       let uu____8211 =
                                                         FStar_SMTEncoding_Util.mkAssume
                                                           (tot_fun_ax,
                                                             (FStar_Pervasives_Native.Some
                                                                a_name),
                                                             a_name) in
                                                       [uu____8211]
                                                   | FStar_Pervasives_Native.Some
                                                       t2 ->
                                                       let f_has_t =
                                                         FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                           FStar_Pervasives_Native.None
                                                           f t2 in
                                                       let a_name =
                                                         Prims.op_Hat
                                                           "typing_" fsym in
                                                       let uu____8215 =
                                                         let uu____8216 =
                                                           let uu____8223 =
                                                             FStar_SMTEncoding_Term.mkForall
                                                               t0.FStar_Syntax_Syntax.pos
                                                               ([[f]],
                                                                 cvars1,
                                                                 f_has_t) in
                                                           (uu____8223,
                                                             (FStar_Pervasives_Native.Some
                                                                a_name),
                                                             a_name) in
                                                         FStar_SMTEncoding_Util.mkAssume
                                                           uu____8216 in
                                                       [uu____8215] in
                                                 let interp_f =
                                                   let a_name =
                                                     Prims.op_Hat
                                                       "interpretation_" fsym in
                                                   let uu____8234 =
                                                     let uu____8241 =
                                                       let uu____8242 =
                                                         let uu____8253 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app, body3) in
                                                         ([[app]],
                                                           (FStar_List.append
                                                              vars cvars1),
                                                           uu____8253) in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         t0.FStar_Syntax_Syntax.pos
                                                         uu____8242 in
                                                     (uu____8241,
                                                       (FStar_Pervasives_Native.Some
                                                          a_name), a_name) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____8234 in
                                                 let f_decls =
                                                   FStar_List.append (fdecl
                                                     :: typing_f) [interp_f] in
                                                 let uu____8265 =
                                                   let uu____8266 =
                                                     let uu____8269 =
                                                       let uu____8272 =
                                                         FStar_SMTEncoding_Term.mk_decls
                                                           fsym tkey_hash
                                                           f_decls
                                                           (FStar_List.append
                                                              decls
                                                              (FStar_List.append
                                                                 decls'
                                                                 decls'')) in
                                                       FStar_List.append
                                                         decls'' uu____8272 in
                                                     FStar_List.append decls'
                                                       uu____8269 in
                                                   FStar_List.append decls
                                                     uu____8266 in
                                                 (f, uu____8265)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8275,
             { FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____8276;
               FStar_Syntax_Syntax.lbunivs = uu____8277;
               FStar_Syntax_Syntax.lbtyp = uu____8278;
               FStar_Syntax_Syntax.lbeff = uu____8279;
               FStar_Syntax_Syntax.lbdef = uu____8280;
               FStar_Syntax_Syntax.lbattrs = uu____8281;
               FStar_Syntax_Syntax.lbpos = uu____8282;_}::uu____8283),
            uu____8284)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false,
             { FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
               FStar_Syntax_Syntax.lbunivs = uu____8314;
               FStar_Syntax_Syntax.lbtyp = t11;
               FStar_Syntax_Syntax.lbeff = uu____8316;
               FStar_Syntax_Syntax.lbdef = e1;
               FStar_Syntax_Syntax.lbattrs = uu____8318;
               FStar_Syntax_Syntax.lbpos = uu____8319;_}::[]),
            e2)
           -> encode_let x t11 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let
           ((false, uu____8343::uu____8344), uu____8345) ->
           failwith "Impossible: non-recursive let with multiple bindings"
       | FStar_Syntax_Syntax.Tm_let ((uu____8364, lbs), uu____8366) ->
           let names =
             FStar_All.pipe_right lbs
               (FStar_List.map
                  (fun lb ->
                     let uu____8413 = lb in
                     match uu____8413 with
                     | { FStar_Syntax_Syntax.lbname = lbname;
                         FStar_Syntax_Syntax.lbunivs = uu____8419;
                         FStar_Syntax_Syntax.lbtyp = uu____8420;
                         FStar_Syntax_Syntax.lbeff = uu____8421;
                         FStar_Syntax_Syntax.lbdef = uu____8422;
                         FStar_Syntax_Syntax.lbattrs = uu____8423;
                         FStar_Syntax_Syntax.lbpos = uu____8424;_} ->
                         let x = FStar_Util.left lbname in
                         let uu____8440 =
                           FStar_Ident.string_of_id
                             x.FStar_Syntax_Syntax.ppname in
                         let uu____8441 = FStar_Syntax_Syntax.range_of_bv x in
                         (uu____8440, uu____8441))) in
           FStar_Exn.raise (FStar_SMTEncoding_Env.Inner_let_rec names)
       | FStar_Syntax_Syntax.Tm_match (e, pats) ->
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
              let uu____8498 =
                let uu____8503 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None) in
                encode_term uu____8503 env in
              match uu____8498 with
              | (ee1, decls1) ->
                  let uu____8528 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2 in
                  (match uu____8528 with
                   | (xs, e21) ->
                       let uu____8553 = FStar_List.hd xs in
                       (match uu____8553 with
                        | (x1, uu____8571) ->
                            let env' =
                              FStar_SMTEncoding_Env.push_term_var env x1 ee1 in
                            let uu____8577 = encode_body e21 env' in
                            (match uu____8577 with
                             | (ee2, decls2) ->
                                 (ee2, (FStar_List.append decls1 decls2)))))
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
            let uu____8607 =
              let uu____8614 =
                let uu____8615 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____8615 in
              FStar_SMTEncoding_Env.gen_term_var env uu____8614 in
            match uu____8607 with
            | (scrsym, scr', env1) ->
                let uu____8623 = encode_term e env1 in
                (match uu____8623 with
                 | (scr, decls) ->
                     let uu____8634 =
                       let encode_branch b uu____8663 =
                         match uu____8663 with
                         | (else_case, decls1) ->
                             let uu____8682 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____8682 with
                              | (p, w, br) ->
                                  let uu____8708 = encode_pat env1 p in
                                  (match uu____8708 with
                                   | (env0, pattern1) ->
                                       let guard = pattern1.guard scr' in
                                       let projections =
                                         pattern1.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2 ->
                                                 fun uu____8745 ->
                                                   match uu____8745 with
                                                   | (x, t) ->
                                                       FStar_SMTEncoding_Env.push_term_var
                                                         env2 x t) env1) in
                                       let uu____8752 =
                                         match w with
                                         | FStar_Pervasives_Native.None ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____8774 =
                                               encode_term w1 env2 in
                                             (match uu____8774 with
                                              | (w2, decls2) ->
                                                  let uu____8787 =
                                                    let uu____8788 =
                                                      let uu____8793 =
                                                        let uu____8794 =
                                                          let uu____8799 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____8799) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____8794 in
                                                      (guard, uu____8793) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____8788 in
                                                  (uu____8787, decls2)) in
                                       (match uu____8752 with
                                        | (guard1, decls2) ->
                                            let uu____8814 =
                                              encode_br br env2 in
                                            (match uu____8814 with
                                             | (br1, decls3) ->
                                                 let uu____8827 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____8827,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____8634 with
                      | (match_tm, decls1) ->
                          let uu____8848 =
                            let uu____8849 =
                              let uu____8860 =
                                let uu____8867 =
                                  let uu____8872 =
                                    FStar_SMTEncoding_Term.mk_fv
                                      (scrsym,
                                        FStar_SMTEncoding_Term.Term_sort) in
                                  (uu____8872, scr) in
                                [uu____8867] in
                              (uu____8860, match_tm) in
                            FStar_SMTEncoding_Term.mkLet' uu____8849
                              FStar_Range.dummyRange in
                          (uu____8848, decls1)))
and (encode_pat :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.pat -> (FStar_SMTEncoding_Env.env_t * pattern))
  =
  fun env ->
    fun pat ->
      (let uu____8894 =
         FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
           FStar_Options.Medium in
       if uu____8894
       then
         let uu____8895 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____8895
       else ());
      (let uu____8897 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____8897 with
       | (vars, pat_term) ->
           let uu____8914 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____8956 ->
                     fun v ->
                       match uu____8956 with
                       | (env1, vars1) ->
                           let uu____8992 =
                             FStar_SMTEncoding_Env.gen_term_var env1 v in
                           (match uu____8992 with
                            | (xx, uu____9010, env2) ->
                                let uu____9012 =
                                  let uu____9019 =
                                    let uu____9024 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xx,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    (v, uu____9024) in
                                  uu____9019 :: vars1 in
                                (env2, uu____9012))) (env, [])) in
           (match uu____8914 with
            | (env1, vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9078 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9079 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9080 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9088 = encode_const c env1 in
                      (match uu____9088 with
                       | (tm, decls) ->
                           ((match decls with
                             | uu____9096::uu____9097 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____9100 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f, args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon
                            env1.FStar_SMTEncoding_Env.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____9121 =
                          FStar_TypeChecker_Env.datacons_of_typ
                            env1.FStar_SMTEncoding_Env.tcenv tc_name in
                        match uu____9121 with
                        | (uu____9128, uu____9129::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9132 ->
                            FStar_SMTEncoding_Env.mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i ->
                                fun uu____9165 ->
                                  match uu____9165 with
                                  | (arg, uu____9173) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9179 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____9179)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x, uu____9210) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9241 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f, args) ->
                      let uu____9264 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i ->
                                fun uu____9308 ->
                                  match uu____9308 with
                                  | (arg, uu____9322) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9328 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____9328)) in
                      FStar_All.pipe_right uu____9264 FStar_List.flatten in
                let pat_term1 uu____9358 = encode_term pat_term env1 in
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
      let uu____9368 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9416 ->
                fun uu____9417 ->
                  match (uu____9416, uu____9417) with
                  | ((tms, decls), (t, uu____9457)) ->
                      let uu____9484 = encode_term t env in
                      (match uu____9484 with
                       | (t1, decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____9368 with | (l1, decls) -> ((FStar_List.rev l1), decls)
and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t ->
    fun env ->
      let universe_of_binders binders =
        FStar_List.map (fun uu____9562 -> FStar_Syntax_Syntax.U_zero) binders in
      let quant = FStar_Syntax_Util.smt_lemma_as_forall t universe_of_binders in
      let env1 =
        let uu___1425_9571 = env in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___1425_9571.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___1425_9571.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___1425_9571.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___1425_9571.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___1425_9571.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___1425_9571.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___1425_9571.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___1425_9571.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___1425_9571.FStar_SMTEncoding_Env.encoding_quantifier);
          FStar_SMTEncoding_Env.global_cache =
            (uu___1425_9571.FStar_SMTEncoding_Env.global_cache)
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
        let uu___1430_9587 = env in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___1430_9587.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___1430_9587.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___1430_9587.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___1430_9587.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___1430_9587.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___1430_9587.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___1430_9587.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___1430_9587.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___1430_9587.FStar_SMTEncoding_Env.encoding_quantifier);
          FStar_SMTEncoding_Env.global_cache =
            (uu___1430_9587.FStar_SMTEncoding_Env.global_cache)
        } in
      let encode_smt_pattern t =
        let uu____9602 = FStar_Syntax_Util.head_and_args t in
        match uu____9602 with
        | (head, args) ->
            let head1 = FStar_Syntax_Util.un_uinst head in
            (match ((head1.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                uu____9665::(x, uu____9667)::(t1, uu____9669)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____9736 = encode_term x env1 in
                 (match uu____9736 with
                  | (x1, decls) ->
                      let uu____9747 = encode_term t1 env1 in
                      (match uu____9747 with
                       | (t2, decls') ->
                           let uu____9758 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t2 in
                           (uu____9758, (FStar_List.append decls decls'))))
             | uu____9759 -> encode_term t env1) in
      FStar_List.fold_right
        (fun pats ->
           fun uu____9802 ->
             match uu____9802 with
             | (pats_l1, decls) ->
                 let uu____9847 =
                   FStar_List.fold_right
                     (fun uu____9882 ->
                        fun uu____9883 ->
                          match (uu____9882, uu____9883) with
                          | ((p, uu____9925), (pats1, decls1)) ->
                              let uu____9960 = encode_smt_pattern p in
                              (match uu____9960 with
                               | (t, d) ->
                                   let uu____9975 =
                                     FStar_SMTEncoding_Term.check_pattern_ok
                                       t in
                                   (match uu____9975 with
                                    | FStar_Pervasives_Native.None ->
                                        ((t :: pats1),
                                          (FStar_List.append d decls1))
                                    | FStar_Pervasives_Native.Some
                                        illegal_subterm ->
                                        ((let uu____9992 =
                                            let uu____9997 =
                                              let uu____9998 =
                                                FStar_Syntax_Print.term_to_string
                                                  p in
                                              let uu____9999 =
                                                FStar_SMTEncoding_Term.print_smt_term
                                                  illegal_subterm in
                                              FStar_Util.format2
                                                "Pattern %s contains illegal sub-term (%s); dropping it"
                                                uu____9998 uu____9999 in
                                            (FStar_Errors.Warning_SMTPatternIllFormed,
                                              uu____9997) in
                                          FStar_Errors.log_issue
                                            p.FStar_Syntax_Syntax.pos
                                            uu____9992);
                                         (pats1,
                                           (FStar_List.append d decls1))))))
                     pats ([], decls) in
                 (match uu____9847 with
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
        let uu____10056 =
          FStar_All.pipe_left
            (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____10056
        then
          let uu____10057 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____10058 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10057 uu____10058
        else () in
      let enc f r l =
        let uu____10097 =
          FStar_Util.fold_map
            (fun decls ->
               fun x ->
                 let uu____10129 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____10129 with
                 | (t, decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____10097 with
        | (decls, args) ->
            let uu____10160 =
              let uu___1494_10161 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___1494_10161.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___1494_10161.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____10160, decls) in
      let const_op f r uu____10196 =
        let uu____10209 = f r in (uu____10209, []) in
      let un_op f l =
        let uu____10232 = FStar_List.hd l in
        FStar_All.pipe_left f uu____10232 in
      let bin_op f uu___2_10252 =
        match uu___2_10252 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10263 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____10303 =
          FStar_Util.fold_map
            (fun decls ->
               fun uu____10328 ->
                 match uu____10328 with
                 | (t, uu____10344) ->
                     let uu____10349 = encode_formula t env in
                     (match uu____10349 with
                      | (phi1, decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____10303 with
        | (decls, phis) ->
            let uu____10378 =
              let uu___1524_10379 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___1524_10379.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___1524_10379.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____10378, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____10442 ->
               match uu____10442 with
               | (a, q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____10461) -> false
                    | uu____10462 -> true)) args in
        if (FStar_List.length rf) <> (Prims.of_int (2))
        then
          let uu____10477 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____10477
        else
          (let uu____10491 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____10491 r rf) in
      let eq3_op r args =
        let n = FStar_List.length args in
        if n = (Prims.of_int (4))
        then
          let uu____10556 =
            enc
              (fun terms ->
                 match terms with
                 | t0::t1::v0::v1::[] ->
                     let uu____10588 =
                       let uu____10593 = FStar_SMTEncoding_Util.mkEq (t0, t1) in
                       let uu____10594 = FStar_SMTEncoding_Util.mkEq (v0, v1) in
                       (uu____10593, uu____10594) in
                     FStar_SMTEncoding_Util.mkAnd uu____10588
                 | uu____10595 -> failwith "Impossible") in
          uu____10556 r args
        else
          (let uu____10599 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n) in
           failwith uu____10599) in
      let h_equals_op r args =
        let n = FStar_List.length args in
        if n = (Prims.of_int (4))
        then
          let uu____10656 =
            enc
              (fun terms ->
                 match terms with
                 | t0::v0::t1::v1::[] ->
                     let uu____10688 =
                       let uu____10693 = FStar_SMTEncoding_Util.mkEq (t0, t1) in
                       let uu____10694 = FStar_SMTEncoding_Util.mkEq (v0, v1) in
                       (uu____10693, uu____10694) in
                     FStar_SMTEncoding_Util.mkAnd uu____10688
                 | uu____10695 -> failwith "Impossible") in
          uu____10656 r args
        else
          (let uu____10699 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n) in
           failwith uu____10699) in
      let mk_imp r uu___3_10726 =
        match uu___3_10726 with
        | (lhs, uu____10732)::(rhs, uu____10734)::[] ->
            let uu____10775 = encode_formula rhs env in
            (match uu____10775 with
             | (l1, decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp, uu____10790) ->
                      (l1, decls1)
                  | uu____10795 ->
                      let uu____10796 = encode_formula lhs env in
                      (match uu____10796 with
                       | (l2, decls2) ->
                           let uu____10807 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____10807, (FStar_List.append decls1 decls2)))))
        | uu____10808 -> failwith "impossible" in
      let mk_ite r uu___4_10835 =
        match uu___4_10835 with
        | (guard, uu____10841)::(_then, uu____10843)::(_else, uu____10845)::[]
            ->
            let uu____10902 = encode_formula guard env in
            (match uu____10902 with
             | (g, decls1) ->
                 let uu____10913 = encode_formula _then env in
                 (match uu____10913 with
                  | (t, decls2) ->
                      let uu____10924 = encode_formula _else env in
                      (match uu____10924 with
                       | (e, decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____10936 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____10965 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____10965 in
      let connectives =
        let uu____10995 =
          let uu____11020 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____11020) in
        let uu____11063 =
          let uu____11090 =
            let uu____11115 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____11115) in
          let uu____11158 =
            let uu____11185 =
              let uu____11212 =
                let uu____11237 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____11237) in
              let uu____11280 =
                let uu____11307 =
                  let uu____11334 =
                    let uu____11359 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____11359) in
                  [uu____11334;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.c_eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq3_op);
                  (FStar_Parser_Const.c_eq3_lid, h_equals_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11307 in
              uu____11212 :: uu____11280 in
            (FStar_Parser_Const.imp_lid, mk_imp) :: uu____11185 in
          uu____11090 :: uu____11158 in
        uu____10995 :: uu____11063 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) ->
            let uu____11900 = encode_formula phi' env in
            (match uu____11900 with
             | (phi2, decls) ->
                 let uu____11911 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____11911, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____11912 ->
            let uu____11919 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____11919 env
        | FStar_Syntax_Syntax.Tm_match (e, pats) ->
            let uu____11958 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____11958 with | (t, decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false,
              { FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____11970;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____11972;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____11974;
                FStar_Syntax_Syntax.lbpos = uu____11975;_}::[]),
             e2)
            ->
            let uu____11999 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____11999 with | (t, decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head, args) ->
            let head1 = FStar_Syntax_Util.un_uinst head in
            (match ((head1.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                uu____12052::(x, uu____12054)::(t, uu____12056)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12123 = encode_term x env in
                 (match uu____12123 with
                  | (x1, decls) ->
                      let uu____12134 = encode_term t env in
                      (match uu____12134 with
                       | (t1, decls') ->
                           let uu____12145 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____12145, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                (r, uu____12148)::(msg, uu____12150)::(phi2, uu____12152)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12219 =
                   let uu____12228 =
                     let uu____12231 =
                       FStar_Syntax_Embeddings.unembed
                         FStar_Syntax_Embeddings.e_range r in
                     uu____12231 false FStar_Syntax_Embeddings.id_norm_cb in
                   let uu____12238 =
                     let uu____12241 =
                       FStar_Syntax_Embeddings.unembed
                         FStar_Syntax_Embeddings.e_string msg in
                     uu____12241 false FStar_Syntax_Embeddings.id_norm_cb in
                   (uu____12228, uu____12238) in
                 (match uu____12219 with
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
                  | uu____12277 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv, (t, uu____12288)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____12323 ->
                 let encode_valid uu____12347 =
                   let uu____12348 = encode_term phi1 env in
                   match uu____12348 with
                   | (tt, decls) ->
                       let tt1 =
                         let uu____12360 =
                           let uu____12361 =
                             FStar_Range.use_range
                               tt.FStar_SMTEncoding_Term.rng in
                           let uu____12362 =
                             FStar_Range.use_range
                               phi1.FStar_Syntax_Syntax.pos in
                           FStar_Range.rng_included uu____12361 uu____12362 in
                         if uu____12360
                         then tt
                         else
                           (let uu___1713_12364 = tt in
                            {
                              FStar_SMTEncoding_Term.tm =
                                (uu___1713_12364.FStar_SMTEncoding_Term.tm);
                              FStar_SMTEncoding_Term.freevars =
                                (uu___1713_12364.FStar_SMTEncoding_Term.freevars);
                              FStar_SMTEncoding_Term.rng =
                                (phi1.FStar_Syntax_Syntax.pos)
                            }) in
                       let uu____12365 = FStar_SMTEncoding_Term.mk_Valid tt1 in
                       (uu____12365, decls) in
                 let uu____12366 = head_redex env head1 in
                 if uu____12366
                 then
                   let uu____12371 = maybe_whnf env head1 in
                   (match uu____12371 with
                    | FStar_Pervasives_Native.None -> encode_valid ()
                    | FStar_Pervasives_Native.Some phi2 ->
                        encode_formula phi2 env)
                 else encode_valid ())
        | uu____12380 ->
            let uu____12381 = encode_term phi1 env in
            (match uu____12381 with
             | (tt, decls) ->
                 let tt1 =
                   let uu____12393 =
                     let uu____12394 =
                       FStar_Range.use_range tt.FStar_SMTEncoding_Term.rng in
                     let uu____12395 =
                       FStar_Range.use_range phi1.FStar_Syntax_Syntax.pos in
                     FStar_Range.rng_included uu____12394 uu____12395 in
                   if uu____12393
                   then tt
                   else
                     (let uu___1725_12397 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___1725_12397.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___1725_12397.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 let uu____12398 = FStar_SMTEncoding_Term.mk_Valid tt1 in
                 (uu____12398, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____12442 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____12442 with
        | (vars, guards, env2, decls, uu____12481) ->
            let uu____12494 = encode_smt_patterns ps env2 in
            (match uu____12494 with
             | (pats, decls') ->
                 let uu____12531 = encode_formula body env2 in
                 (match uu____12531 with
                  | (body1, decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf, p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12563;
                             FStar_SMTEncoding_Term.rng = uu____12564;_}::[])::[]
                            when
                            let uu____12581 =
                              FStar_Ident.string_of_lid
                                FStar_Parser_Const.guard_free in
                            uu____12581 = gf -> []
                        | uu____12582 -> guards in
                      let uu____12587 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____12587, body1,
                        (FStar_List.append decls
                           (FStar_List.append decls' decls''))))) in
      debug phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let uu____12598 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____12598 with
       | FStar_Pervasives_Native.None -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op, arms))
           ->
           let uu____12607 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____12713 ->
                     match uu____12713 with
                     | (l, uu____12737) -> FStar_Ident.lid_equals op l)) in
           (match uu____12607 with
            | FStar_Pervasives_Native.None -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____12806, f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars, pats, body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____12898 = encode_q_body env vars pats body in
             match uu____12898 with
             | (vars1, pats1, guard, body1, decls) ->
                 let tm =
                   let uu____12943 =
                     let uu____12954 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____12954) in
                   FStar_SMTEncoding_Term.mkForall
                     phi1.FStar_Syntax_Syntax.pos uu____12943 in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars, pats, body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____12985 = encode_q_body env vars pats body in
             match uu____12985 with
             | (vars1, pats1, guard, body1, decls) ->
                 let uu____13029 =
                   let uu____13030 =
                     let uu____13041 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____13041) in
                   FStar_SMTEncoding_Term.mkExists
                     phi1.FStar_Syntax_Syntax.pos uu____13030 in
                 (uu____13029, decls))))