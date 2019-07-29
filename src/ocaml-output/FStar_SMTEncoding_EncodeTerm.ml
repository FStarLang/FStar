open Prims
let mkForall_fuel' :
  'Auu____14 .
    Prims.string ->
      FStar_Range.range ->
        'Auu____14 ->
          (FStar_SMTEncoding_Term.pat Prims.list Prims.list *
            FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term) ->
            FStar_SMTEncoding_Term.term
  =
  fun mname ->
    fun r ->
      fun n1 ->
        fun uu____45 ->
          match uu____45 with
          | (pats, vars, body) ->
              let fallback uu____73 =
                FStar_SMTEncoding_Term.mkForall r (pats, vars, body) in
              let uu____78 = FStar_Options.unthrottle_inductives () in
              if uu____78
              then fallback ()
              else
                (let uu____83 =
                   FStar_SMTEncoding_Env.fresh_fvar mname "f"
                     FStar_SMTEncoding_Term.Fuel_sort in
                 match uu____83 with
                 | (fsym, fterm) ->
                     let add_fuel1 tms =
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
                               | uu____123 -> p)) in
                     let pats1 = FStar_List.map add_fuel1 pats in
                     let body1 =
                       match body.FStar_SMTEncoding_Term.tm with
                       | FStar_SMTEncoding_Term.App
                           (FStar_SMTEncoding_Term.Imp, guard::body'::[]) ->
                           let guard1 =
                             match guard.FStar_SMTEncoding_Term.tm with
                             | FStar_SMTEncoding_Term.App
                                 (FStar_SMTEncoding_Term.And, guards) ->
                                 let uu____144 = add_fuel1 guards in
                                 FStar_SMTEncoding_Util.mk_and_l uu____144
                             | uu____147 ->
                                 let uu____148 = add_fuel1 [guard] in
                                 FStar_All.pipe_right uu____148 FStar_List.hd in
                           FStar_SMTEncoding_Util.mkImp (guard1, body')
                       | uu____153 -> body in
                     let vars1 =
                       let uu____165 =
                         FStar_SMTEncoding_Term.mk_fv
                           (fsym, FStar_SMTEncoding_Term.Fuel_sort) in
                       uu____165 :: vars in
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
      | FStar_Syntax_Syntax.Tm_arrow uu____229 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____245 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____253 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____255 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____269 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____289 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____292 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____292 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____311;
             FStar_Syntax_Syntax.vars = uu____312;_},
           uu____313)
          ->
          let uu____338 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____338 FStar_Option.isNone
      | uu____356 -> false
let (head_redex :
  FStar_SMTEncoding_Env.env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env ->
    fun t ->
      let uu____370 =
        let uu____371 = FStar_Syntax_Util.un_uinst t in
        uu____371.FStar_Syntax_Syntax.n in
      match uu____370 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____375, uu____376, FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___0_401 ->
                  match uu___0_401 with
                  | FStar_Syntax_Syntax.TOTAL -> true
                  | uu____404 -> false) rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____407 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____407 FStar_Option.isSome
      | uu____425 -> false
let (whnf :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun t ->
      let uu____438 = head_normal env t in
      if uu____438
      then t
      else
        FStar_TypeChecker_Normalize.normalize
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
      FStar_TypeChecker_Normalize.normalize
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
      let uu____468 = FStar_Syntax_Util.head_and_args t' in
      match uu____468 with
      | (head', uu____488) ->
          let uu____513 = head_redex env head' in
          if uu____513
          then FStar_Pervasives_Native.None
          else FStar_Pervasives_Native.Some t'
let (trivial_post : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let uu____526 =
      let uu____527 = FStar_Syntax_Syntax.null_binder t in [uu____527] in
    let uu____546 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
    FStar_Syntax_Util.abs uu____526 uu____546 FStar_Pervasives_Native.None
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
                let uu____568 = FStar_SMTEncoding_Term.fv_sort var in
                match uu____568 with
                | FStar_SMTEncoding_Term.Fuel_sort ->
                    let uu____569 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____569
                | s ->
                    let uu____572 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____572) e)
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
  fun head1 ->
    fun arity ->
      fun n_args ->
        fun rng ->
          let uu____628 =
            let uu____634 =
              let uu____636 = FStar_Util.string_of_int arity in
              let uu____638 = FStar_Util.string_of_int n_args in
              FStar_Util.format3
                "Head symbol %s expects at least %s arguments; got only %s"
                head1 uu____636 uu____638 in
            (FStar_Errors.Fatal_SMTEncodingArityMismatch, uu____634) in
          FStar_Errors.raise_error uu____628 rng
let (isTotFun_axioms :
  FStar_Range.range ->
    FStar_SMTEncoding_Term.term ->
      FStar_SMTEncoding_Term.fvs ->
        FStar_SMTEncoding_Term.term Prims.list ->
          Prims.bool -> FStar_SMTEncoding_Term.term)
  =
  fun pos ->
    fun head1 ->
      fun vars ->
        fun guards ->
          fun is_pure ->
            let maybe_mkForall pat vars1 body =
              match vars1 with
              | [] -> body
              | uu____726 ->
                  FStar_SMTEncoding_Term.mkForall pos (pat, vars1, body) in
            let rec is_tot_fun_axioms ctx ctx_guard head2 vars1 guards1 =
              match (vars1, guards1) with
              | ([], []) -> FStar_SMTEncoding_Util.mkTrue
              | (uu____843::[], uu____844) ->
                  if is_pure
                  then
                    let uu____884 =
                      let uu____885 =
                        let uu____890 =
                          FStar_SMTEncoding_Term.mk_IsTotFun head2 in
                        (ctx_guard, uu____890) in
                      FStar_SMTEncoding_Util.mkImp uu____885 in
                    maybe_mkForall [[head2]] ctx uu____884
                  else FStar_SMTEncoding_Util.mkTrue
              | (x::vars2, g_x::guards2) ->
                  let is_tot_fun_head =
                    let uu____942 =
                      let uu____943 =
                        let uu____948 =
                          FStar_SMTEncoding_Term.mk_IsTotFun head2 in
                        (ctx_guard, uu____948) in
                      FStar_SMTEncoding_Util.mkImp uu____943 in
                    maybe_mkForall [[head2]] ctx uu____942 in
                  let app = mk_Apply head2 [x] in
                  let ctx1 = FStar_List.append ctx [x] in
                  let ctx_guard1 =
                    FStar_SMTEncoding_Util.mkAnd (ctx_guard, g_x) in
                  let rest =
                    is_tot_fun_axioms ctx1 ctx_guard1 app vars2 guards2 in
                  FStar_SMTEncoding_Util.mkAnd (is_tot_fun_head, rest)
              | uu____1007 -> failwith "impossible: isTotFun_axioms" in
            is_tot_fun_axioms [] FStar_SMTEncoding_Util.mkTrue head1 vars
              guards
let (maybe_curry_app :
  FStar_Range.range ->
    (FStar_SMTEncoding_Term.op, FStar_SMTEncoding_Term.term)
      FStar_Util.either ->
      Prims.int ->
        FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term)
  =
  fun rng ->
    fun head1 ->
      fun arity ->
        fun args ->
          let n_args = FStar_List.length args in
          match head1 with
          | FStar_Util.Inr head2 -> mk_Apply_args head2 args
          | FStar_Util.Inl head2 ->
              if n_args = arity
              then FStar_SMTEncoding_Util.mkApp' (head2, args)
              else
                if n_args > arity
                then
                  (let uu____1078 = FStar_Util.first_N arity args in
                   match uu____1078 with
                   | (args1, rest) ->
                       let head3 =
                         FStar_SMTEncoding_Util.mkApp' (head2, args1) in
                       mk_Apply_args head3 rest)
                else
                  (let uu____1102 = FStar_SMTEncoding_Term.op_to_string head2 in
                   raise_arity_mismatch uu____1102 arity n_args rng)
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
          let uu____1125 = FStar_SMTEncoding_Env.force_thunk fvb in
          mk_Apply_args uu____1125 args
        else
          maybe_curry_app rng
            (FStar_Util.Inl
               (FStar_SMTEncoding_Term.Var (fvb.FStar_SMTEncoding_Env.smt_id)))
            fvb.FStar_SMTEncoding_Env.smt_arity args
let (is_app : FStar_SMTEncoding_Term.op -> Prims.bool) =
  fun uu___1_1134 ->
    match uu___1_1134 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____1140 -> false
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
                   FStar_SMTEncoding_Term.freevars = uu____1188;
                   FStar_SMTEncoding_Term.rng = uu____1189;_}::[]),
             x::xs1) when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)
              -> check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var f, args),
             uu____1220) ->
              let uu____1230 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a ->
                        fun v1 ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____1247 -> false) args (FStar_List.rev xs)) in
              if uu____1230
              then
                let n1 = FStar_SMTEncoding_Env.tok_of_name env f in
                ((let uu____1256 =
                    FStar_All.pipe_left
                      (FStar_TypeChecker_Env.debug
                         env.FStar_SMTEncoding_Env.tcenv)
                      (FStar_Options.Other "PartialApp") in
                  if uu____1256
                  then
                    let uu____1261 = FStar_SMTEncoding_Term.print_smt_term t in
                    let uu____1263 =
                      match n1 with
                      | FStar_Pervasives_Native.None -> "None"
                      | FStar_Pervasives_Native.Some x ->
                          FStar_SMTEncoding_Term.print_smt_term x in
                    FStar_Util.print2
                      "is_eta_expansion %s  ... tok_of_name = %s\n"
                      uu____1261 uu____1263
                  else ());
                 n1)
              else FStar_Pervasives_Native.None
          | (uu____1273, []) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____1277 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv ->
                        let uu____1285 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____1285)) in
              if uu____1277
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____1292 -> FStar_Pervasives_Native.None in
        check_partial_applications body (FStar_List.rev vars)
let check_pattern_vars :
  'Auu____1310 'Auu____1311 .
    FStar_SMTEncoding_Env.env_t ->
      (FStar_Syntax_Syntax.bv * 'Auu____1310) Prims.list ->
        (FStar_Syntax_Syntax.term * 'Auu____1311) Prims.list -> unit
  =
  fun env ->
    fun vars ->
      fun pats ->
        let pats1 =
          FStar_All.pipe_right pats
            (FStar_List.map
               (fun uu____1369 ->
                  match uu____1369 with
                  | (x, uu____1375) ->
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.AllowUnboundUniverses;
                        FStar_TypeChecker_Env.EraseUniverses]
                        env.FStar_SMTEncoding_Env.tcenv x)) in
        match pats1 with
        | [] -> ()
        | hd1::tl1 ->
            let pat_vars =
              let uu____1383 = FStar_Syntax_Free.names hd1 in
              FStar_List.fold_left
                (fun out ->
                   fun x ->
                     let uu____1395 = FStar_Syntax_Free.names x in
                     FStar_Util.set_union out uu____1395) uu____1383 tl1 in
            let uu____1398 =
              FStar_All.pipe_right vars
                (FStar_Util.find_opt
                   (fun uu____1425 ->
                      match uu____1425 with
                      | (b, uu____1432) ->
                          let uu____1433 = FStar_Util.set_mem b pat_vars in
                          Prims.op_Negation uu____1433)) in
            (match uu____1398 with
             | FStar_Pervasives_Native.None -> ()
             | FStar_Pervasives_Native.Some (x, uu____1440) ->
                 let pos =
                   FStar_List.fold_left
                     (fun out ->
                        fun t ->
                          FStar_Range.union_ranges out
                            t.FStar_Syntax_Syntax.pos)
                     hd1.FStar_Syntax_Syntax.pos tl1 in
                 let uu____1454 =
                   let uu____1460 =
                     let uu____1462 = FStar_Syntax_Print.bv_to_string x in
                     FStar_Util.format1
                       "SMT pattern misses at least one bound variable: %s"
                       uu____1462 in
                   (FStar_Errors.Warning_SMTPatternIllFormed, uu____1460) in
                 FStar_Errors.log_issue pos uu____1454)
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
        | FStar_Syntax_Syntax.Tm_arrow uu____1748 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____1763 ->
            let uu____1770 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____1770
        | uu____1772 ->
            if norm1
            then let uu____1774 = whnf env t1 in aux false uu____1774
            else
              (let uu____1778 =
                 let uu____1780 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____1782 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____1780 uu____1782 in
               failwith uu____1778) in
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
    | FStar_Syntax_Syntax.Tm_refine (bv, uu____1824) ->
        let uu____1829 =
          curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort in
        (match uu____1829 with
         | (args, res) ->
             (match args with
              | [] ->
                  let uu____1850 = FStar_Syntax_Syntax.mk_Total k1 in
                  ([], uu____1850)
              | uu____1857 -> (args, res)))
    | uu____1858 ->
        let uu____1859 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____1859)
let is_arithmetic_primitive :
  'Auu____1873 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____1873 Prims.list -> Prims.bool
  =
  fun head1 ->
    fun args ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv, uu____1896::uu____1897::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv, uu____1901::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____1904 -> false
let (isInteger : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun tm ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1, FStar_Pervasives_Native.None)) -> true
    | uu____1935 -> false
let (getInteger : FStar_Syntax_Syntax.term' -> Prims.int) =
  fun tm ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1, FStar_Pervasives_Native.None)) -> FStar_Util.int_of_string n1
    | uu____1958 -> failwith "Expected an Integer term"
let is_BitVector_primitive :
  'Auu____1968 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____1968)
        Prims.list -> Prims.bool
  =
  fun head1 ->
    fun args ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,
         (sz_arg, uu____2010)::uu____2011::uu____2012::[]) ->
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
         (sz_arg, uu____2063)::uu____2064::[]) ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____2101 -> false
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
          let uu____2425 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue in
          (uu____2425, [])
      | FStar_Const.Const_bool (false) ->
          let uu____2427 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse in
          (uu____2427, [])
      | FStar_Const.Const_char c1 ->
          let uu____2430 =
            let uu____2431 =
              let uu____2439 =
                let uu____2442 =
                  let uu____2443 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1) in
                  FStar_SMTEncoding_Term.boxInt uu____2443 in
                [uu____2442] in
              ("FStar.Char.__char_of_int", uu____2439) in
            FStar_SMTEncoding_Util.mkApp uu____2431 in
          (uu____2430, [])
      | FStar_Const.Const_int (i, FStar_Pervasives_Native.None) ->
          let uu____2461 =
            let uu____2462 = FStar_SMTEncoding_Util.mkInteger i in
            FStar_SMTEncoding_Term.boxInt uu____2462 in
          (uu____2461, [])
      | FStar_Const.Const_int (repr, FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.FStar_SMTEncoding_Env.tcenv).FStar_TypeChecker_Env.dsenv
              repr sw FStar_Range.dummyRange in
          encode_term syntax_term env
      | FStar_Const.Const_string (s, uu____2483) ->
          let uu____2486 =
            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.string_const s in
          (uu____2486, [])
      | FStar_Const.Const_range uu____2487 ->
          let uu____2488 = FStar_SMTEncoding_Term.mk_Range_const () in
          (uu____2488, [])
      | FStar_Const.Const_effect -> (FStar_SMTEncoding_Term.mk_Term_type, [])
      | FStar_Const.Const_real r ->
          let uu____2491 =
            let uu____2492 = FStar_SMTEncoding_Util.mkReal r in
            FStar_SMTEncoding_Term.boxReal uu____2492 in
          (uu____2491, [])
      | c1 ->
          let uu____2494 =
            let uu____2496 = FStar_Syntax_Print.const_to_string c1 in
            FStar_Util.format1 "Unhandled constant: %s" uu____2496 in
          failwith uu____2494
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
        (let uu____2525 =
           FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
             FStar_Options.Medium in
         if uu____2525
         then
           let uu____2528 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____2528
         else ());
        (let uu____2534 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2616 ->
                   fun b ->
                     match uu____2616 with
                     | (vars, guards, env1, decls, names1) ->
                         let uu____2681 =
                           let x = FStar_Pervasives_Native.fst b in
                           let uu____2697 =
                             FStar_SMTEncoding_Env.gen_term_var env1 x in
                           match uu____2697 with
                           | (xxsym, xx, env') ->
                               let uu____2722 =
                                 let uu____2727 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____2727 env1 xx in
                               (match uu____2722 with
                                | (guard_x_t, decls') ->
                                    let uu____2742 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xxsym,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    (uu____2742, guard_x_t, env', decls', x)) in
                         (match uu____2681 with
                          | (v1, g, env2, decls', n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____2534 with
         | (vars, guards, env1, decls, names1) ->
             ((FStar_List.rev vars), (FStar_List.rev guards), env1, decls,
               (FStar_List.rev names1)))
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
          let uu____2842 = encode_term t env in
          match uu____2842 with
          | (t1, decls) ->
              let uu____2853 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____2853, decls)
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
          let uu____2864 = encode_term t env in
          match uu____2864 with
          | (t1, decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None ->
                   let uu____2879 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____2879, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____2881 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____2881, decls))
and (encode_arith_term :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun env ->
    fun head1 ->
      fun args_e ->
        let uu____2887 = encode_args args_e env in
        match uu____2887 with
        | (arg_tms, decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____2906 -> failwith "Impossible" in
            let unary unbox arg_tms1 =
              let uu____2928 = FStar_List.hd arg_tms1 in unbox uu____2928 in
            let binary unbox arg_tms1 =
              let uu____2953 =
                let uu____2954 = FStar_List.hd arg_tms1 in unbox uu____2954 in
              let uu____2955 =
                let uu____2956 =
                  let uu____2957 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____2957 in
                unbox uu____2956 in
              (uu____2953, uu____2955) in
            let mk_default uu____2965 =
              let uu____2966 =
                FStar_SMTEncoding_Env.lookup_free_var_sym env
                  head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____2966 with
              | (fname, fuel_args, arity) ->
                  let args = FStar_List.append fuel_args arg_tms in
                  maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity
                    args in
            let mk_l box op mk_args ts =
              let uu____3055 = FStar_Options.smtencoding_l_arith_native () in
              if uu____3055
              then
                let uu____3058 = let uu____3059 = mk_args ts in op uu____3059 in
                FStar_All.pipe_right uu____3058 box
              else mk_default () in
            let mk_nl box unbox nm op ts =
              let uu____3117 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____3117
              then
                let uu____3120 = binary unbox ts in
                match uu____3120 with
                | (t1, t2) ->
                    let uu____3127 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____3127 box
              else
                (let uu____3133 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____3133
                 then
                   let uu____3136 =
                     let uu____3137 = binary unbox ts in op uu____3137 in
                   FStar_All.pipe_right uu____3136 box
                 else mk_default ()) in
            let add1 box unbox =
              mk_l box FStar_SMTEncoding_Util.mkAdd (binary unbox) in
            let sub1 box unbox =
              mk_l box FStar_SMTEncoding_Util.mkSub (binary unbox) in
            let minus1 box unbox =
              mk_l box FStar_SMTEncoding_Util.mkMinus (unary unbox) in
            let mul1 box unbox nm =
              mk_nl box unbox nm FStar_SMTEncoding_Util.mkMul in
            let div1 box unbox nm =
              mk_nl box unbox nm FStar_SMTEncoding_Util.mkDiv in
            let modulus box unbox =
              mk_nl box unbox "_mod" FStar_SMTEncoding_Util.mkMod in
            let ops =
              [(FStar_Parser_Const.op_Addition,
                 (add1 FStar_SMTEncoding_Term.boxInt
                    FStar_SMTEncoding_Term.unboxInt));
              (FStar_Parser_Const.op_Subtraction,
                (sub1 FStar_SMTEncoding_Term.boxInt
                   FStar_SMTEncoding_Term.unboxInt));
              (FStar_Parser_Const.op_Multiply,
                (mul1 FStar_SMTEncoding_Term.boxInt
                   FStar_SMTEncoding_Term.unboxInt "_mul"));
              (FStar_Parser_Const.op_Division,
                (div1 FStar_SMTEncoding_Term.boxInt
                   FStar_SMTEncoding_Term.unboxInt "_div"));
              (FStar_Parser_Const.op_Modulus,
                (modulus FStar_SMTEncoding_Term.boxInt
                   FStar_SMTEncoding_Term.unboxInt));
              (FStar_Parser_Const.op_Minus,
                (minus1 FStar_SMTEncoding_Term.boxInt
                   FStar_SMTEncoding_Term.unboxInt));
              (FStar_Parser_Const.real_op_Addition,
                (add1 FStar_SMTEncoding_Term.boxReal
                   FStar_SMTEncoding_Term.unboxReal));
              (FStar_Parser_Const.real_op_Subtraction,
                (sub1 FStar_SMTEncoding_Term.boxReal
                   FStar_SMTEncoding_Term.unboxReal));
              (FStar_Parser_Const.real_op_Multiply,
                (mul1 FStar_SMTEncoding_Term.boxReal
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
            let uu____3572 =
              let uu____3582 =
                FStar_List.tryFind
                  (fun uu____3606 ->
                     match uu____3606 with
                     | (l, uu____3617) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____3582 FStar_Util.must in
            (match uu____3572 with
             | (uu____3661, op) ->
                 let uu____3673 = op arg_tms in (uu____3673, decls))
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
    fun head1 ->
      fun args_e ->
        let uu____3689 = FStar_List.hd args_e in
        match uu____3689 with
        | (tm_sz, uu____3705) ->
            let uu____3714 = uu____3689 in
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz) in
            let sz_decls =
              let t_decls1 = FStar_SMTEncoding_Term.mkBvConstructor sz in
              FStar_SMTEncoding_Term.mk_decls "" sz_key t_decls1 [] in
            let uu____3725 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar fv,
                 uu____3751::(sz_arg, uu____3753)::uu____3754::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____3821 =
                    let uu____3822 = FStar_List.tail args_e in
                    FStar_List.tail uu____3822 in
                  let uu____3849 =
                    let uu____3853 = getInteger sz_arg.FStar_Syntax_Syntax.n in
                    FStar_Pervasives_Native.Some uu____3853 in
                  (uu____3821, uu____3849)
              | (FStar_Syntax_Syntax.Tm_fvar fv,
                 uu____3860::(sz_arg, uu____3862)::uu____3863::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____3930 =
                    let uu____3932 = FStar_Syntax_Print.term_to_string sz_arg in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____3932 in
                  failwith uu____3930
              | uu____3942 ->
                  let uu____3957 = FStar_List.tail args_e in
                  (uu____3957, FStar_Pervasives_Native.None) in
            (match uu____3725 with
             | (arg_tms, ext_sz) ->
                 let uu____3984 = encode_args arg_tms env in
                 (match uu____3984 with
                  | (arg_tms1, decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____4005 -> failwith "Impossible" in
                      let unary arg_tms2 =
                        let uu____4017 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____4017 in
                      let unary_arith arg_tms2 =
                        let uu____4028 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxInt uu____4028 in
                      let binary arg_tms2 =
                        let uu____4043 =
                          let uu____4044 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____4044 in
                        let uu____4045 =
                          let uu____4046 =
                            let uu____4047 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____4047 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____4046 in
                        (uu____4043, uu____4045) in
                      let binary_arith arg_tms2 =
                        let uu____4064 =
                          let uu____4065 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____4065 in
                        let uu____4066 =
                          let uu____4067 =
                            let uu____4068 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____4068 in
                          FStar_SMTEncoding_Term.unboxInt uu____4067 in
                        (uu____4064, uu____4066) in
                      let mk_bv op mk_args resBox ts =
                        let uu____4126 =
                          let uu____4127 = mk_args ts in op uu____4127 in
                        FStar_All.pipe_right uu____4126 resBox in
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
                        let uu____4259 =
                          let uu____4264 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None ->
                                failwith "impossible" in
                          FStar_SMTEncoding_Util.mkBvUext uu____4264 in
                        let uu____4273 =
                          let uu____4278 =
                            let uu____4280 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None ->
                                  failwith "impossible" in
                            sz + uu____4280 in
                          FStar_SMTEncoding_Term.boxBitVec uu____4278 in
                        mk_bv uu____4259 unary uu____4273 arg_tms2 in
                      let to_int1 =
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
                        (FStar_Parser_Const.bv_to_nat_lid, to_int1);
                        (FStar_Parser_Const.nat_to_bv_lid, bv_to)] in
                      let uu____4520 =
                        let uu____4530 =
                          FStar_List.tryFind
                            (fun uu____4554 ->
                               match uu____4554 with
                               | (l, uu____4565) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops in
                        FStar_All.pipe_right uu____4530 FStar_Util.must in
                      (match uu____4520 with
                       | (uu____4611, op) ->
                           let uu____4623 = op arg_tms1 in
                           (uu____4623, (FStar_List.append sz_decls decls)))))
and (encode_deeply_embedded_quantifier :
  FStar_Syntax_Syntax.term ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t ->
    fun env ->
      let env1 =
        let uu___594_4633 = env in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___594_4633.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___594_4633.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___594_4633.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___594_4633.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___594_4633.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___594_4633.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name =
            (uu___594_4633.FStar_SMTEncoding_Env.use_zfuel_name);
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___594_4633.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___594_4633.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier = true;
          FStar_SMTEncoding_Env.global_cache =
            (uu___594_4633.FStar_SMTEncoding_Env.global_cache)
        } in
      let uu____4635 = encode_term t env1 in
      match uu____4635 with
      | (tm, decls) ->
          let vars = FStar_SMTEncoding_Term.free_variables tm in
          let valid_tm = FStar_SMTEncoding_Term.mk_Valid tm in
          let key =
            FStar_SMTEncoding_Term.mkForall t.FStar_Syntax_Syntax.pos
              ([], vars, valid_tm) in
          let tkey_hash = FStar_SMTEncoding_Term.hash_of_term key in
          (match tm.FStar_SMTEncoding_Term.tm with
           | FStar_SMTEncoding_Term.App
               (uu____4661,
                {
                  FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV
                    uu____4662;
                  FStar_SMTEncoding_Term.freevars = uu____4663;
                  FStar_SMTEncoding_Term.rng = uu____4664;_}::{
                                                                FStar_SMTEncoding_Term.tm
                                                                  =
                                                                  FStar_SMTEncoding_Term.FreeV
                                                                  uu____4665;
                                                                FStar_SMTEncoding_Term.freevars
                                                                  =
                                                                  uu____4666;
                                                                FStar_SMTEncoding_Term.rng
                                                                  =
                                                                  uu____4667;_}::[])
               ->
               (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                  (FStar_Errors.Warning_QuantifierWithoutPattern,
                    "Not encoding deeply embedded, unguarded quantifier to SMT");
                (tm, decls))
           | uu____4713 ->
               let uu____4714 = encode_formula t env1 in
               (match uu____4714 with
                | (phi, decls') ->
                    let interp =
                      match vars with
                      | [] ->
                          let uu____4734 =
                            let uu____4739 =
                              FStar_SMTEncoding_Term.mk_Valid tm in
                            (uu____4739, phi) in
                          FStar_SMTEncoding_Util.mkIff uu____4734
                      | uu____4740 ->
                          let uu____4741 =
                            let uu____4752 =
                              let uu____4753 =
                                let uu____4758 =
                                  FStar_SMTEncoding_Term.mk_Valid tm in
                                (uu____4758, phi) in
                              FStar_SMTEncoding_Util.mkIff uu____4753 in
                            ([[valid_tm]], vars, uu____4752) in
                          FStar_SMTEncoding_Term.mkForall
                            t.FStar_Syntax_Syntax.pos uu____4741 in
                    let ax =
                      let uu____4768 =
                        let uu____4776 =
                          let uu____4778 =
                            FStar_Util.digest_of_string tkey_hash in
                          Prims.op_Hat "l_quant_interp_" uu____4778 in
                        (interp,
                          (FStar_Pervasives_Native.Some
                             "Interpretation of deeply embedded quantifier"),
                          uu____4776) in
                      FStar_SMTEncoding_Util.mkAssume uu____4768 in
                    let uu____4784 =
                      let uu____4785 =
                        let uu____4788 =
                          FStar_SMTEncoding_Term.mk_decls "" tkey_hash 
                            [ax] (FStar_List.append decls decls') in
                        FStar_List.append decls' uu____4788 in
                      FStar_List.append decls uu____4785 in
                    (tm, uu____4784)))
and (encode_term :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t ->
    fun env ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____4800 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____4800
       then
         let uu____4805 = FStar_Syntax_Print.tag_of_term t in
         let uu____4807 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____4809 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____4805 uu____4807
           uu____4809
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____4818 ->
           let uu____4841 =
             let uu____4843 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____4846 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____4848 = FStar_Syntax_Print.term_to_string t0 in
             let uu____4850 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____4843
               uu____4846 uu____4848 uu____4850 in
           failwith uu____4841
       | FStar_Syntax_Syntax.Tm_unknown ->
           let uu____4857 =
             let uu____4859 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____4862 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____4864 = FStar_Syntax_Print.term_to_string t0 in
             let uu____4866 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____4859
               uu____4862 uu____4864 uu____4866 in
           failwith uu____4857
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let e = FStar_Syntax_Util.unfold_lazy i in
           ((let uu____4876 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding") in
             if uu____4876
             then
               let uu____4881 = FStar_Syntax_Print.term_to_string t0 in
               let uu____4883 = FStar_Syntax_Print.term_to_string e in
               FStar_Util.print2 ">> Unfolded (%s) ~> (%s)\n" uu____4881
                 uu____4883
             else ());
            encode_term e env)
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____4889 =
             let uu____4891 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____4891 in
           failwith uu____4889
       | FStar_Syntax_Syntax.Tm_ascribed (t1, (k, uu____4900), uu____4901) ->
           let uu____4950 =
             match k with
             | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
             | uu____4960 -> false in
           if uu____4950
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t1 env
       | FStar_Syntax_Syntax.Tm_quoted (qt, uu____4978) ->
           let tv =
             let uu____4984 =
               let uu____4991 = FStar_Reflection_Basic.inspect_ln qt in
               FStar_Syntax_Embeddings.embed
                 FStar_Reflection_Embeddings.e_term_view uu____4991 in
             uu____4984 t.FStar_Syntax_Syntax.pos
               FStar_Pervasives_Native.None
               FStar_Syntax_Embeddings.id_norm_cb in
           ((let uu____4995 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding") in
             if uu____4995
             then
               let uu____5000 = FStar_Syntax_Print.term_to_string t0 in
               let uu____5002 = FStar_Syntax_Print.term_to_string tv in
               FStar_Util.print2 ">> Inspected (%s) ~> (%s)\n" uu____5000
                 uu____5002
             else ());
            (let t1 =
               let uu____5010 =
                 let uu____5021 = FStar_Syntax_Syntax.as_arg tv in
                 [uu____5021] in
               FStar_Syntax_Util.mk_app
                 (FStar_Reflection_Data.refl_constant_term
                    FStar_Reflection_Data.fstar_refl_pack_ln) uu____5010 in
             encode_term t1 env))
       | FStar_Syntax_Syntax.Tm_meta
           (t1, FStar_Syntax_Syntax.Meta_pattern uu____5047) ->
           encode_term t1
             (let uu___666_5073 = env in
              {
                FStar_SMTEncoding_Env.bvar_bindings =
                  (uu___666_5073.FStar_SMTEncoding_Env.bvar_bindings);
                FStar_SMTEncoding_Env.fvar_bindings =
                  (uu___666_5073.FStar_SMTEncoding_Env.fvar_bindings);
                FStar_SMTEncoding_Env.depth =
                  (uu___666_5073.FStar_SMTEncoding_Env.depth);
                FStar_SMTEncoding_Env.tcenv =
                  (uu___666_5073.FStar_SMTEncoding_Env.tcenv);
                FStar_SMTEncoding_Env.warn =
                  (uu___666_5073.FStar_SMTEncoding_Env.warn);
                FStar_SMTEncoding_Env.nolabels =
                  (uu___666_5073.FStar_SMTEncoding_Env.nolabels);
                FStar_SMTEncoding_Env.use_zfuel_name =
                  (uu___666_5073.FStar_SMTEncoding_Env.use_zfuel_name);
                FStar_SMTEncoding_Env.encode_non_total_function_typ =
                  (uu___666_5073.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                FStar_SMTEncoding_Env.current_module_name =
                  (uu___666_5073.FStar_SMTEncoding_Env.current_module_name);
                FStar_SMTEncoding_Env.encoding_quantifier = false;
                FStar_SMTEncoding_Env.global_cache =
                  (uu___666_5073.FStar_SMTEncoding_Env.global_cache)
              })
       | FStar_Syntax_Syntax.Tm_meta (t1, uu____5076) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = FStar_SMTEncoding_Env.lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let encode_freev uu____5093 =
             let fvb =
               FStar_SMTEncoding_Env.lookup_free_var_name env
                 v1.FStar_Syntax_Syntax.fv_name in
             let tok =
               FStar_SMTEncoding_Env.lookup_free_var env
                 v1.FStar_Syntax_Syntax.fv_name in
             let tkey_hash = FStar_SMTEncoding_Term.hash_of_term tok in
             let uu____5098 =
               if fvb.FStar_SMTEncoding_Env.smt_arity > Prims.int_zero
               then
                 match tok.FStar_SMTEncoding_Term.tm with
                 | FStar_SMTEncoding_Term.FreeV uu____5122 ->
                     let sym_name =
                       let uu____5133 = FStar_Util.digest_of_string tkey_hash in
                       Prims.op_Hat "@kick_partial_app_" uu____5133 in
                     let uu____5136 =
                       let uu____5139 =
                         let uu____5140 =
                           let uu____5148 =
                             FStar_SMTEncoding_Term.kick_partial_app tok in
                           (uu____5148,
                             (FStar_Pervasives_Native.Some "kick_partial_app"),
                             sym_name) in
                         FStar_SMTEncoding_Util.mkAssume uu____5140 in
                       [uu____5139] in
                     (uu____5136, sym_name)
                 | FStar_SMTEncoding_Term.App (uu____5155, []) ->
                     let sym_name =
                       let uu____5160 = FStar_Util.digest_of_string tkey_hash in
                       Prims.op_Hat "@kick_partial_app_" uu____5160 in
                     let uu____5163 =
                       let uu____5166 =
                         let uu____5167 =
                           let uu____5175 =
                             FStar_SMTEncoding_Term.kick_partial_app tok in
                           (uu____5175,
                             (FStar_Pervasives_Native.Some "kick_partial_app"),
                             sym_name) in
                         FStar_SMTEncoding_Util.mkAssume uu____5167 in
                       [uu____5166] in
                     (uu____5163, sym_name)
                 | uu____5182 -> ([], "")
               else ([], "") in
             match uu____5098 with
             | (aux_decls, sym_name) ->
                 let uu____5205 =
                   if aux_decls = []
                   then
                     FStar_All.pipe_right []
                       FStar_SMTEncoding_Term.mk_decls_trivial
                   else
                     FStar_SMTEncoding_Term.mk_decls sym_name tkey_hash
                       aux_decls [] in
                 (tok, uu____5205) in
           let uu____5213 = head_redex env t in
           if uu____5213
           then
             let uu____5220 = maybe_whnf env t in
             (match uu____5220 with
              | FStar_Pervasives_Native.None -> encode_freev ()
              | FStar_Pervasives_Native.Some t1 -> encode_term t1 env)
           else encode_freev ()
       | FStar_Syntax_Syntax.Tm_type uu____5230 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1, uu____5232) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders, c) ->
           let module_name = env.FStar_SMTEncoding_Env.current_module_name in
           let uu____5262 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____5262 with
            | (binders1, res) ->
                let uu____5273 =
                  (env.FStar_SMTEncoding_Env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____5273
                then
                  let uu____5280 =
                    encode_binders FStar_Pervasives_Native.None binders1 env in
                  (match uu____5280 with
                   | (vars, guards_l, env', decls, uu____5305) ->
                       let fsym =
                         let uu____5319 =
                           let uu____5325 =
                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                               module_name "f" in
                           (uu____5325, FStar_SMTEncoding_Term.Term_sort) in
                         FStar_SMTEncoding_Term.mk_fv uu____5319 in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____5331 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___725_5340 =
                              env.FStar_SMTEncoding_Env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___725_5340.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___725_5340.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___725_5340.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___725_5340.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___725_5340.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___725_5340.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___725_5340.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___725_5340.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___725_5340.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___725_5340.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___725_5340.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___725_5340.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___725_5340.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___725_5340.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___725_5340.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___725_5340.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___725_5340.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___725_5340.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___725_5340.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___725_5340.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___725_5340.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___725_5340.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___725_5340.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___725_5340.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___725_5340.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___725_5340.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___725_5340.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___725_5340.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___725_5340.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___725_5340.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___725_5340.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___725_5340.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___725_5340.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___725_5340.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___725_5340.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___725_5340.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___725_5340.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___725_5340.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___725_5340.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___725_5340.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___725_5340.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___725_5340.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___725_5340.FStar_TypeChecker_Env.strict_args_tab)
                            }) res in
                       (match uu____5331 with
                        | (pre_opt, res_t) ->
                            let uu____5352 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app in
                            (match uu____5352 with
                             | (res_pred, decls') ->
                                 let uu____5363 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None ->
                                       let uu____5376 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards_l in
                                       (uu____5376, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____5380 =
                                         encode_formula pre env' in
                                       (match uu____5380 with
                                        | (guard, decls0) ->
                                            let uu____5393 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards_l) in
                                            (uu____5393, decls0)) in
                                 (match uu____5363 with
                                  | (guards, guard_decls) ->
                                      let is_pure =
                                        let uu____5408 =
                                          FStar_All.pipe_right res
                                            (FStar_TypeChecker_Normalize.ghost_to_pure
                                               env.FStar_SMTEncoding_Env.tcenv) in
                                        FStar_All.pipe_right uu____5408
                                          FStar_Syntax_Util.is_pure_comp in
                                      let t_interp =
                                        let uu____5417 =
                                          let uu____5428 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards, res_pred) in
                                          ([[app]], vars, uu____5428) in
                                        FStar_SMTEncoding_Term.mkForall
                                          t.FStar_Syntax_Syntax.pos
                                          uu____5417 in
                                      let t_interp1 =
                                        let tot_fun_axioms =
                                          isTotFun_axioms
                                            t.FStar_Syntax_Syntax.pos f vars
                                            guards_l is_pure in
                                        FStar_SMTEncoding_Util.mkAnd
                                          (t_interp, tot_fun_axioms) in
                                      let cvars =
                                        let uu____5450 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp1 in
                                        FStar_All.pipe_right uu____5450
                                          (FStar_List.filter
                                             (fun x ->
                                                let uu____5469 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    x in
                                                let uu____5471 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    fsym in
                                                uu____5469 <> uu____5471)) in
                                      let tkey =
                                        FStar_SMTEncoding_Term.mkForall
                                          t.FStar_Syntax_Syntax.pos
                                          ([], (fsym :: cvars), t_interp1) in
                                      let prefix1 =
                                        if is_pure
                                        then "Tm_arrow_"
                                        else "Tm_ghost_arrow_" in
                                      let tkey_hash =
                                        let uu____5499 =
                                          FStar_SMTEncoding_Term.hash_of_term
                                            tkey in
                                        Prims.op_Hat prefix1 uu____5499 in
                                      let tsym =
                                        let uu____5503 =
                                          FStar_Util.digest_of_string
                                            tkey_hash in
                                        Prims.op_Hat prefix1 uu____5503 in
                                      let cvar_sorts =
                                        FStar_List.map
                                          FStar_SMTEncoding_Term.fv_sort
                                          cvars in
                                      let caption =
                                        let uu____5517 =
                                          FStar_Options.log_queries () in
                                        if uu____5517
                                        then
                                          let uu____5520 =
                                            let uu____5522 =
                                              FStar_TypeChecker_Normalize.term_to_string
                                                env.FStar_SMTEncoding_Env.tcenv
                                                t0 in
                                            FStar_Util.replace_char
                                              uu____5522 10 32 in
                                          FStar_Pervasives_Native.Some
                                            uu____5520
                                        else FStar_Pervasives_Native.None in
                                      let tdecl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (tsym, cvar_sorts,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            caption) in
                                      let t1 =
                                        let uu____5535 =
                                          let uu____5543 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              cvars in
                                          (tsym, uu____5543) in
                                        FStar_SMTEncoding_Util.mkApp
                                          uu____5535 in
                                      let t_has_kind =
                                        FStar_SMTEncoding_Term.mk_HasType t1
                                          FStar_SMTEncoding_Term.mk_Term_type in
                                      let k_assumption =
                                        let a_name =
                                          Prims.op_Hat "kinding_" tsym in
                                        let uu____5562 =
                                          let uu____5570 =
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              ([[t_has_kind]], cvars,
                                                t_has_kind) in
                                          (uu____5570,
                                            (FStar_Pervasives_Native.Some
                                               a_name), a_name) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____5562 in
                                      let f_has_t =
                                        FStar_SMTEncoding_Term.mk_HasType f
                                          t1 in
                                      let f_has_t_z =
                                        FStar_SMTEncoding_Term.mk_HasTypeZ f
                                          t1 in
                                      let pre_typing =
                                        let a_name =
                                          Prims.op_Hat "pre_typing_" tsym in
                                        let uu____5587 =
                                          let uu____5595 =
                                            let uu____5596 =
                                              let uu____5607 =
                                                let uu____5608 =
                                                  let uu____5613 =
                                                    let uu____5614 =
                                                      FStar_SMTEncoding_Term.mk_PreType
                                                        f in
                                                    FStar_SMTEncoding_Term.mk_tester
                                                      "Tm_arrow" uu____5614 in
                                                  (f_has_t, uu____5613) in
                                                FStar_SMTEncoding_Util.mkImp
                                                  uu____5608 in
                                              ([[f_has_t]], (fsym :: cvars),
                                                uu____5607) in
                                            let uu____5632 =
                                              mkForall_fuel module_name
                                                t0.FStar_Syntax_Syntax.pos in
                                            uu____5632 uu____5596 in
                                          (uu____5595,
                                            (FStar_Pervasives_Native.Some
                                               "pre-typing for functions"),
                                            (Prims.op_Hat module_name
                                               (Prims.op_Hat "_" a_name))) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____5587 in
                                      let t_interp2 =
                                        let a_name =
                                          Prims.op_Hat "interpretation_" tsym in
                                        let uu____5655 =
                                          let uu____5663 =
                                            let uu____5664 =
                                              let uu____5675 =
                                                FStar_SMTEncoding_Util.mkIff
                                                  (f_has_t_z, t_interp1) in
                                              ([[f_has_t_z]], (fsym ::
                                                cvars), uu____5675) in
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              uu____5664 in
                                          (uu____5663,
                                            (FStar_Pervasives_Native.Some
                                               a_name),
                                            (Prims.op_Hat module_name
                                               (Prims.op_Hat "_" a_name))) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____5655 in
                                      let t_decls1 =
                                        [tdecl;
                                        k_assumption;
                                        pre_typing;
                                        t_interp2] in
                                      let uu____5698 =
                                        let uu____5699 =
                                          let uu____5702 =
                                            let uu____5705 =
                                              FStar_SMTEncoding_Term.mk_decls
                                                tsym tkey_hash t_decls1
                                                (FStar_List.append decls
                                                   (FStar_List.append decls'
                                                      guard_decls)) in
                                            FStar_List.append guard_decls
                                              uu____5705 in
                                          FStar_List.append decls' uu____5702 in
                                        FStar_List.append decls uu____5699 in
                                      (t1, uu____5698)))))
                else
                  (let tsym =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                       module_name "Non_total_Tm_arrow" in
                   let tdecl =
                     FStar_SMTEncoding_Term.DeclFun
                       (tsym, [], FStar_SMTEncoding_Term.Term_sort,
                         FStar_Pervasives_Native.None) in
                   let t1 = FStar_SMTEncoding_Util.mkApp (tsym, []) in
                   let t_kinding =
                     let a_name =
                       Prims.op_Hat "non_total_function_typing_" tsym in
                     let uu____5726 =
                       let uu____5734 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____5734,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"), a_name) in
                     FStar_SMTEncoding_Util.mkAssume uu____5726 in
                   let fsym =
                     FStar_SMTEncoding_Term.mk_fv
                       ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.op_Hat "pre_typing_" tsym in
                     let uu____5747 =
                       let uu____5755 =
                         let uu____5756 =
                           let uu____5767 =
                             let uu____5768 =
                               let uu____5773 =
                                 let uu____5774 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____5774 in
                               (f_has_t, uu____5773) in
                             FStar_SMTEncoding_Util.mkImp uu____5768 in
                           ([[f_has_t]], [fsym], uu____5767) in
                         let uu____5800 =
                           mkForall_fuel module_name
                             t0.FStar_Syntax_Syntax.pos in
                         uu____5800 uu____5756 in
                       (uu____5755, (FStar_Pervasives_Native.Some a_name),
                         a_name) in
                     FStar_SMTEncoding_Util.mkAssume uu____5747 in
                   let uu____5817 =
                     FStar_All.pipe_right [tdecl; t_kinding; t_interp]
                       FStar_SMTEncoding_Term.mk_decls_trivial in
                   (t1, uu____5817)))
       | FStar_Syntax_Syntax.Tm_refine uu____5820 ->
           let uu____5827 =
             let steps =
               [FStar_TypeChecker_Env.Weak;
               FStar_TypeChecker_Env.HNF;
               FStar_TypeChecker_Env.EraseUniverses] in
             let uu____5837 =
               FStar_TypeChecker_Normalize.normalize_refinement steps
                 env.FStar_SMTEncoding_Env.tcenv t0 in
             match uu____5837 with
             | {
                 FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f);
                 FStar_Syntax_Syntax.pos = uu____5846;
                 FStar_Syntax_Syntax.vars = uu____5847;_} ->
                 let uu____5854 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f in
                 (match uu____5854 with
                  | (b, f1) ->
                      let uu____5881 =
                        let uu____5882 = FStar_List.hd b in
                        FStar_Pervasives_Native.fst uu____5882 in
                      (uu____5881, f1))
             | uu____5899 -> failwith "impossible" in
           (match uu____5827 with
            | (x, f) ->
                let uu____5917 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____5917 with
                 | (base_t, decls) ->
                     let uu____5928 =
                       FStar_SMTEncoding_Env.gen_term_var env x in
                     (match uu____5928 with
                      | (x1, xtm, env') ->
                          let uu____5945 = encode_formula f env' in
                          (match uu____5945 with
                           | (refinement, decls') ->
                               let uu____5956 =
                                 FStar_SMTEncoding_Env.fresh_fvar
                                   env.FStar_SMTEncoding_Env.current_module_name
                                   "f" FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____5956 with
                                | (fsym, fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____5984 =
                                        let uu____5995 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____6006 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____5995
                                          uu____6006 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____5984 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun y ->
                                              (let uu____6060 =
                                                 FStar_SMTEncoding_Term.fv_name
                                                   y in
                                               uu____6060 <> x1) &&
                                                (let uu____6064 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     y in
                                                 uu____6064 <> fsym))) in
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
                                    ((let uu____6097 =
                                        FStar_TypeChecker_Env.debug
                                          env.FStar_SMTEncoding_Env.tcenv
                                          (FStar_Options.Other "SMTEncoding") in
                                      if uu____6097
                                      then
                                        let uu____6101 =
                                          FStar_Syntax_Print.term_to_string f in
                                        let uu____6103 =
                                          FStar_Util.digest_of_string
                                            tkey_hash in
                                        FStar_Util.print3
                                          "Encoding Tm_refine %s with tkey_hash %s and digest %s\n"
                                          uu____6101 tkey_hash uu____6103
                                      else ());
                                     (let tsym =
                                        let uu____6110 =
                                          FStar_Util.digest_of_string
                                            tkey_hash in
                                        Prims.op_Hat "Tm_refine_" uu____6110 in
                                      let cvar_sorts =
                                        FStar_List.map
                                          FStar_SMTEncoding_Term.fv_sort
                                          cvars1 in
                                      let tdecl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (tsym, cvar_sorts,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            FStar_Pervasives_Native.None) in
                                      let t1 =
                                        let uu____6130 =
                                          let uu____6138 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              cvars1 in
                                          (tsym, uu____6138) in
                                        FStar_SMTEncoding_Util.mkApp
                                          uu____6130 in
                                      let x_has_base_t =
                                        FStar_SMTEncoding_Term.mk_HasType xtm
                                          base_t in
                                      let x_has_t =
                                        FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                          (FStar_Pervasives_Native.Some fterm)
                                          xtm t1 in
                                      let t_has_kind =
                                        FStar_SMTEncoding_Term.mk_HasType t1
                                          FStar_SMTEncoding_Term.mk_Term_type in
                                      let t_haseq_base =
                                        FStar_SMTEncoding_Term.mk_haseq
                                          base_t in
                                      let t_haseq_ref =
                                        FStar_SMTEncoding_Term.mk_haseq t1 in
                                      let t_haseq1 =
                                        let uu____6158 =
                                          let uu____6166 =
                                            let uu____6167 =
                                              let uu____6178 =
                                                FStar_SMTEncoding_Util.mkIff
                                                  (t_haseq_ref, t_haseq_base) in
                                              ([[t_haseq_ref]], cvars1,
                                                uu____6178) in
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              uu____6167 in
                                          (uu____6166,
                                            (FStar_Pervasives_Native.Some
                                               (Prims.op_Hat "haseq for "
                                                  tsym)),
                                            (Prims.op_Hat "haseq" tsym)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____6158 in
                                      let t_kinding =
                                        let uu____6192 =
                                          let uu____6200 =
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              ([[t_has_kind]], cvars1,
                                                t_has_kind) in
                                          (uu____6200,
                                            (FStar_Pervasives_Native.Some
                                               "refinement kinding"),
                                            (Prims.op_Hat
                                               "refinement_kinding_" tsym)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____6192 in
                                      let t_interp =
                                        let uu____6214 =
                                          let uu____6222 =
                                            let uu____6223 =
                                              let uu____6234 =
                                                FStar_SMTEncoding_Util.mkIff
                                                  (x_has_t, encoding) in
                                              ([[x_has_t]], (ffv :: xfv ::
                                                cvars1), uu____6234) in
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              uu____6223 in
                                          (uu____6222,
                                            (FStar_Pervasives_Native.Some
                                               "refinement_interpretation"),
                                            (Prims.op_Hat
                                               "refinement_interpretation_"
                                               tsym)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____6214 in
                                      let t_decls1 =
                                        [tdecl;
                                        t_kinding;
                                        t_interp;
                                        t_haseq1] in
                                      let uu____6266 =
                                        let uu____6267 =
                                          let uu____6270 =
                                            FStar_SMTEncoding_Term.mk_decls
                                              tsym tkey_hash t_decls1
                                              (FStar_List.append decls decls') in
                                          FStar_List.append decls' uu____6270 in
                                        FStar_List.append decls uu____6267 in
                                      (t1, uu____6266))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv, uu____6274) ->
           let ttm =
             let uu____6292 =
               FStar_Syntax_Unionfind.uvar_id
                 uv.FStar_Syntax_Syntax.ctx_uvar_head in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____6292 in
           let uu____6294 =
             encode_term_pred FStar_Pervasives_Native.None
               uv.FStar_Syntax_Syntax.ctx_uvar_typ env ttm in
           (match uu____6294 with
            | (t_has_k, decls) ->
                let d =
                  let uu____6306 =
                    let uu____6314 =
                      let uu____6316 =
                        let uu____6318 =
                          let uu____6320 =
                            FStar_Syntax_Unionfind.uvar_id
                              uv.FStar_Syntax_Syntax.ctx_uvar_head in
                          FStar_Util.string_of_int uu____6320 in
                        FStar_Util.format1 "uvar_typing_%s" uu____6318 in
                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                        uu____6316 in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____6314) in
                  FStar_SMTEncoding_Util.mkAssume uu____6306 in
                let uu____6326 =
                  let uu____6327 =
                    FStar_All.pipe_right [d]
                      FStar_SMTEncoding_Term.mk_decls_trivial in
                  FStar_List.append decls uu____6327 in
                (ttm, uu____6326))
       | FStar_Syntax_Syntax.Tm_app uu____6334 ->
           let uu____6351 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____6351 with
            | (head1, args_e) ->
                let uu____6398 =
                  let uu____6415 = head_redex env head1 in
                  if uu____6415
                  then
                    let uu____6434 = maybe_whnf env t0 in
                    match uu____6434 with
                    | FStar_Pervasives_Native.None -> (head1, args_e)
                    | FStar_Pervasives_Native.Some t1 ->
                        FStar_Syntax_Util.head_and_args t1
                  else (head1, args_e) in
                (match uu____6398 with
                 | (head2, args_e1) ->
                     let uu____6510 =
                       let uu____6525 =
                         let uu____6526 = FStar_Syntax_Subst.compress head2 in
                         uu____6526.FStar_Syntax_Syntax.n in
                       (uu____6525, args_e1) in
                     (match uu____6510 with
                      | uu____6543 when is_arithmetic_primitive head2 args_e1
                          -> encode_arith_term env head2 args_e1
                      | uu____6566 when is_BitVector_primitive head2 args_e1
                          -> encode_BitVector_term env head2 args_e1
                      | (FStar_Syntax_Syntax.Tm_fvar fv, uu____6584) when
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
                            FStar_Syntax_Syntax.pos = uu____6606;
                            FStar_Syntax_Syntax.vars = uu____6607;_},
                          uu____6608),
                         uu____6609) when
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
                            FStar_Syntax_Syntax.pos = uu____6635;
                            FStar_Syntax_Syntax.vars = uu____6636;_},
                          uu____6637),
                         (v0, uu____6639)::(v1, uu____6641)::(v2, uu____6643)::[])
                          when
                          FStar_Syntax_Syntax.fv_eq_lid fv
                            FStar_Parser_Const.lexcons_lid
                          ->
                          let uu____6714 = encode_term v0 env in
                          (match uu____6714 with
                           | (v01, decls0) ->
                               let uu____6725 = encode_term v1 env in
                               (match uu____6725 with
                                | (v11, decls1) ->
                                    let uu____6736 = encode_term v2 env in
                                    (match uu____6736 with
                                     | (v21, decls2) ->
                                         let uu____6747 =
                                           FStar_SMTEncoding_Util.mk_LexCons
                                             v01 v11 v21 in
                                         (uu____6747,
                                           (FStar_List.append decls0
                                              (FStar_List.append decls1
                                                 decls2))))))
                      | (FStar_Syntax_Syntax.Tm_fvar fv,
                         (v0, uu____6750)::(v1, uu____6752)::(v2, uu____6754)::[])
                          when
                          FStar_Syntax_Syntax.fv_eq_lid fv
                            FStar_Parser_Const.lexcons_lid
                          ->
                          let uu____6821 = encode_term v0 env in
                          (match uu____6821 with
                           | (v01, decls0) ->
                               let uu____6832 = encode_term v1 env in
                               (match uu____6832 with
                                | (v11, decls1) ->
                                    let uu____6843 = encode_term v2 env in
                                    (match uu____6843 with
                                     | (v21, decls2) ->
                                         let uu____6854 =
                                           FStar_SMTEncoding_Util.mk_LexCons
                                             v01 v11 v21 in
                                         (uu____6854,
                                           (FStar_List.append decls0
                                              (FStar_List.append decls1
                                                 decls2))))))
                      | (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range_of), (arg, uu____6856)::[])
                          ->
                          encode_const
                            (FStar_Const.Const_range
                               (arg.FStar_Syntax_Syntax.pos)) env
                      | (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_set_range_of),
                         (arg, uu____6892)::(rng, uu____6894)::[]) ->
                          encode_term arg env
                      | (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify), uu____6945) ->
                          let e0 =
                            let uu____6967 = FStar_List.hd args_e1 in
                            FStar_TypeChecker_Util.reify_body_with_arg
                              env.FStar_SMTEncoding_Env.tcenv head2
                              uu____6967 in
                          ((let uu____6977 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   env.FStar_SMTEncoding_Env.tcenv)
                                (FStar_Options.Other "SMTEncodingReify") in
                            if uu____6977
                            then
                              let uu____6982 =
                                FStar_Syntax_Print.term_to_string e0 in
                              FStar_Util.print1
                                "Result of normalization %s\n" uu____6982
                            else ());
                           (let e =
                              let uu____6990 =
                                let uu____6995 =
                                  FStar_TypeChecker_Util.remove_reify e0 in
                                let uu____6996 = FStar_List.tl args_e1 in
                                FStar_Syntax_Syntax.mk_Tm_app uu____6995
                                  uu____6996 in
                              uu____6990 FStar_Pervasives_Native.None
                                t0.FStar_Syntax_Syntax.pos in
                            encode_term e env))
                      | (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____7005),
                         (arg, uu____7007)::[]) -> encode_term arg env
                      | uu____7042 ->
                          let uu____7057 = encode_args args_e1 env in
                          (match uu____7057 with
                           | (args, decls) ->
                               let encode_partial_app ht_opt =
                                 let uu____7126 = encode_term head2 env in
                                 match uu____7126 with
                                 | (smt_head, decls') ->
                                     let app_tm = mk_Apply_args smt_head args in
                                     (match ht_opt with
                                      | uu____7146 ->
                                          (app_tm,
                                            (FStar_List.append decls decls'))
                                      | FStar_Pervasives_Native.Some
                                          (head_type, formals, c) ->
                                          ((let uu____7215 =
                                              FStar_TypeChecker_Env.debug
                                                env.FStar_SMTEncoding_Env.tcenv
                                                (FStar_Options.Other
                                                   "PartialApp") in
                                            if uu____7215
                                            then
                                              let uu____7219 =
                                                FStar_Syntax_Print.term_to_string
                                                  head2 in
                                              let uu____7221 =
                                                FStar_Syntax_Print.term_to_string
                                                  head_type in
                                              let uu____7223 =
                                                FStar_Syntax_Print.binders_to_string
                                                  ", " formals in
                                              let uu____7226 =
                                                FStar_Syntax_Print.comp_to_string
                                                  c in
                                              let uu____7228 =
                                                FStar_Syntax_Print.args_to_string
                                                  args_e1 in
                                              FStar_Util.print5
                                                "Encoding partial application:\n\thead=%s\n\thead_type=%s\n\tformals=%s\n\tcomp=%s\n\tactual args=%s\n"
                                                uu____7219 uu____7221
                                                uu____7223 uu____7226
                                                uu____7228
                                            else ());
                                           (let uu____7233 =
                                              FStar_Util.first_N
                                                (FStar_List.length args_e1)
                                                formals in
                                            match uu____7233 with
                                            | (formals1, rest) ->
                                                let subst1 =
                                                  FStar_List.map2
                                                    (fun uu____7331 ->
                                                       fun uu____7332 ->
                                                         match (uu____7331,
                                                                 uu____7332)
                                                         with
                                                         | ((bv, uu____7362),
                                                            (a, uu____7364))
                                                             ->
                                                             FStar_Syntax_Syntax.NT
                                                               (bv, a))
                                                    formals1 args_e1 in
                                                let ty =
                                                  let uu____7396 =
                                                    FStar_Syntax_Util.arrow
                                                      rest c in
                                                  FStar_All.pipe_right
                                                    uu____7396
                                                    (FStar_Syntax_Subst.subst
                                                       subst1) in
                                                ((let uu____7400 =
                                                    FStar_TypeChecker_Env.debug
                                                      env.FStar_SMTEncoding_Env.tcenv
                                                      (FStar_Options.Other
                                                         "PartialApp") in
                                                  if uu____7400
                                                  then
                                                    let uu____7404 =
                                                      FStar_Syntax_Print.term_to_string
                                                        ty in
                                                    FStar_Util.print1
                                                      "Encoding partial application, after subst:\n\tty=%s\n"
                                                      uu____7404
                                                  else ());
                                                 (let uu____7409 =
                                                    let uu____7422 =
                                                      FStar_List.fold_left2
                                                        (fun uu____7457 ->
                                                           fun uu____7458 ->
                                                             fun e ->
                                                               match 
                                                                 (uu____7457,
                                                                   uu____7458)
                                                               with
                                                               | ((t_hyps,
                                                                   decls1),
                                                                  (bv,
                                                                   uu____7499))
                                                                   ->
                                                                   let t1 =
                                                                    FStar_Syntax_Subst.subst
                                                                    subst1
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                   let uu____7527
                                                                    =
                                                                    encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    t1 env e in
                                                                   (match uu____7527
                                                                    with
                                                                    | 
                                                                    (t_hyp,
                                                                    decls'1)
                                                                    ->
                                                                    ((
                                                                    let uu____7543
                                                                    =
                                                                    FStar_TypeChecker_Env.debug
                                                                    env.FStar_SMTEncoding_Env.tcenv
                                                                    (FStar_Options.Other
                                                                    "PartialApp") in
                                                                    if
                                                                    uu____7543
                                                                    then
                                                                    let uu____7547
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1 in
                                                                    let uu____7549
                                                                    =
                                                                    FStar_SMTEncoding_Term.print_smt_term
                                                                    t_hyp in
                                                                    FStar_Util.print2
                                                                    "Encoded typing hypothesis for %s ... got %s\n"
                                                                    uu____7547
                                                                    uu____7549
                                                                    else ());
                                                                    ((t_hyp
                                                                    ::
                                                                    t_hyps),
                                                                    (FStar_List.append
                                                                    decls1
                                                                    decls'1)))))
                                                        ([], []) formals1
                                                        args in
                                                    match uu____7422 with
                                                    | (t_hyps, decls1) ->
                                                        let uu____7584 =
                                                          match smt_head.FStar_SMTEncoding_Term.tm
                                                          with
                                                          | FStar_SMTEncoding_Term.FreeV
                                                              uu____7593 ->
                                                              encode_term_pred
                                                                FStar_Pervasives_Native.None
                                                                head_type env
                                                                smt_head
                                                          | uu____7602 ->
                                                              (FStar_SMTEncoding_Util.mkTrue,
                                                                []) in
                                                        (match uu____7584
                                                         with
                                                         | (t_head_hyp,
                                                            decls'1) ->
                                                             let hyp =
                                                               FStar_SMTEncoding_Term.mk_and_l
                                                                 (t_head_hyp
                                                                 :: t_hyps)
                                                                 FStar_Range.dummyRange in
                                                             let uu____7618 =
                                                               encode_term_pred
                                                                 FStar_Pervasives_Native.None
                                                                 ty env
                                                                 app_tm in
                                                             (match uu____7618
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
                                                                  let uu____7640
                                                                    =
                                                                    let uu____7647
                                                                    =
                                                                    FStar_SMTEncoding_Term.fvs_subset_of
                                                                    cvars
                                                                    app_tm_vars in
                                                                    if
                                                                    uu____7647
                                                                    then
                                                                    ([app_tm],
                                                                    app_tm_vars)
                                                                    else
                                                                    (let uu____7660
                                                                    =
                                                                    let uu____7662
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    has_type_conclusion in
                                                                    FStar_SMTEncoding_Term.fvs_subset_of
                                                                    cvars
                                                                    uu____7662 in
                                                                    if
                                                                    uu____7660
                                                                    then
                                                                    ([has_type_conclusion],
                                                                    cvars)
                                                                    else
                                                                    ((
                                                                    let uu____7675
                                                                    =
                                                                    let uu____7681
                                                                    =
                                                                    let uu____7683
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t0 in
                                                                    FStar_Util.format1
                                                                    "No SMT pattern for partial application %s"
                                                                    uu____7683 in
                                                                    (FStar_Errors.Warning_SMTPatternIllFormed,
                                                                    uu____7681) in
                                                                    FStar_Errors.log_issue
                                                                    t0.FStar_Syntax_Syntax.pos
                                                                    uu____7675);
                                                                    ([],
                                                                    cvars))) in
                                                                  (match uu____7640
                                                                   with
                                                                   | 
                                                                   (pattern,
                                                                    vars) ->
                                                                    (vars,
                                                                    pattern,
                                                                    has_type,
                                                                    (FStar_List.append
                                                                    decls1
                                                                    (FStar_List.append
                                                                    decls'1
                                                                    decls'')))))) in
                                                  match uu____7409 with
                                                  | (vars, pattern, has_type,
                                                     decls'') ->
                                                      ((let uu____7730 =
                                                          FStar_TypeChecker_Env.debug
                                                            env.FStar_SMTEncoding_Env.tcenv
                                                            (FStar_Options.Other
                                                               "PartialApp") in
                                                        if uu____7730
                                                        then
                                                          let uu____7734 =
                                                            FStar_SMTEncoding_Term.print_smt_term
                                                              has_type in
                                                          FStar_Util.print1
                                                            "Encoding partial application, after SMT encoded predicate:\n\t=%s\n"
                                                            uu____7734
                                                        else ());
                                                       (let tkey_hash =
                                                          FStar_SMTEncoding_Term.hash_of_term
                                                            app_tm in
                                                        let e_typing =
                                                          let uu____7742 =
                                                            let uu____7750 =
                                                              FStar_SMTEncoding_Term.mkForall
                                                                t0.FStar_Syntax_Syntax.pos
                                                                ([pattern],
                                                                  vars,
                                                                  has_type) in
                                                            let uu____7759 =
                                                              let uu____7761
                                                                =
                                                                let uu____7763
                                                                  =
                                                                  FStar_SMTEncoding_Term.hash_of_term
                                                                    app_tm in
                                                                FStar_Util.digest_of_string
                                                                  uu____7763 in
                                                              Prims.op_Hat
                                                                "partial_app_typing_"
                                                                uu____7761 in
                                                            (uu____7750,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Partial app typing"),
                                                              uu____7759) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____7742 in
                                                        let uu____7769 =
                                                          let uu____7772 =
                                                            let uu____7775 =
                                                              let uu____7778
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
                                                                uu____7778 in
                                                            FStar_List.append
                                                              decls'
                                                              uu____7775 in
                                                          FStar_List.append
                                                            decls uu____7772 in
                                                        (app_tm, uu____7769)))))))) in
                               let encode_full_app fv =
                                 let uu____7798 =
                                   FStar_SMTEncoding_Env.lookup_free_var_sym
                                     env fv in
                                 match uu____7798 with
                                 | (fname, fuel_args, arity) ->
                                     let tm =
                                       maybe_curry_app
                                         t0.FStar_Syntax_Syntax.pos fname
                                         arity
                                         (FStar_List.append fuel_args args) in
                                     (tm, decls) in
                               let head3 = FStar_Syntax_Subst.compress head2 in
                               let head_type =
                                 match head3.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_uinst
                                     ({
                                        FStar_Syntax_Syntax.n =
                                          FStar_Syntax_Syntax.Tm_name x;
                                        FStar_Syntax_Syntax.pos = uu____7841;
                                        FStar_Syntax_Syntax.vars = uu____7842;_},
                                      uu____7843)
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
                                        FStar_Syntax_Syntax.pos = uu____7850;
                                        FStar_Syntax_Syntax.vars = uu____7851;_},
                                      uu____7852)
                                     ->
                                     let uu____7857 =
                                       let uu____7858 =
                                         let uu____7863 =
                                           FStar_TypeChecker_Env.lookup_lid
                                             env.FStar_SMTEncoding_Env.tcenv
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                         FStar_All.pipe_right uu____7863
                                           FStar_Pervasives_Native.fst in
                                       FStar_All.pipe_right uu____7858
                                         FStar_Pervasives_Native.snd in
                                     FStar_Pervasives_Native.Some uu____7857
                                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                                     let uu____7893 =
                                       let uu____7894 =
                                         let uu____7899 =
                                           FStar_TypeChecker_Env.lookup_lid
                                             env.FStar_SMTEncoding_Env.tcenv
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                         FStar_All.pipe_right uu____7899
                                           FStar_Pervasives_Native.fst in
                                       FStar_All.pipe_right uu____7894
                                         FStar_Pervasives_Native.snd in
                                     FStar_Pervasives_Native.Some uu____7893
                                 | FStar_Syntax_Syntax.Tm_ascribed
                                     (uu____7928,
                                      (FStar_Util.Inl t1, uu____7930),
                                      uu____7931)
                                     -> FStar_Pervasives_Native.Some t1
                                 | FStar_Syntax_Syntax.Tm_ascribed
                                     (uu____7978,
                                      (FStar_Util.Inr c, uu____7980),
                                      uu____7981)
                                     ->
                                     FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Util.comp_result c)
                                 | uu____8028 -> FStar_Pervasives_Native.None in
                               (match head_type with
                                | FStar_Pervasives_Native.None ->
                                    encode_partial_app
                                      FStar_Pervasives_Native.None
                                | FStar_Pervasives_Native.Some head_type1 ->
                                    let uu____8052 =
                                      let head_type2 =
                                        let uu____8074 =
                                          FStar_TypeChecker_Normalize.normalize_refinement
                                            [FStar_TypeChecker_Env.Weak;
                                            FStar_TypeChecker_Env.HNF;
                                            FStar_TypeChecker_Env.EraseUniverses]
                                            env.FStar_SMTEncoding_Env.tcenv
                                            head_type1 in
                                        FStar_All.pipe_left
                                          FStar_Syntax_Util.unrefine
                                          uu____8074 in
                                      let uu____8077 =
                                        curried_arrow_formals_comp head_type2 in
                                      match uu____8077 with
                                      | (formals, c) ->
                                          if
                                            (FStar_List.length formals) <
                                              (FStar_List.length args)
                                          then
                                            let head_type3 =
                                              let uu____8128 =
                                                FStar_TypeChecker_Normalize.normalize_refinement
                                                  [FStar_TypeChecker_Env.Weak;
                                                  FStar_TypeChecker_Env.HNF;
                                                  FStar_TypeChecker_Env.EraseUniverses;
                                                  FStar_TypeChecker_Env.UnfoldUntil
                                                    FStar_Syntax_Syntax.delta_constant]
                                                  env.FStar_SMTEncoding_Env.tcenv
                                                  head_type2 in
                                              FStar_All.pipe_left
                                                FStar_Syntax_Util.unrefine
                                                uu____8128 in
                                            let uu____8129 =
                                              curried_arrow_formals_comp
                                                head_type3 in
                                            (match uu____8129 with
                                             | (formals1, c1) ->
                                                 (head_type3, formals1, c1))
                                          else (head_type2, formals, c) in
                                    (match uu____8052 with
                                     | (head_type2, formals, c) ->
                                         ((let uu____8212 =
                                             FStar_TypeChecker_Env.debug
                                               env.FStar_SMTEncoding_Env.tcenv
                                               (FStar_Options.Other
                                                  "PartialApp") in
                                           if uu____8212
                                           then
                                             let uu____8216 =
                                               FStar_Syntax_Print.term_to_string
                                                 head_type2 in
                                             let uu____8218 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " formals in
                                             let uu____8221 =
                                               FStar_Syntax_Print.args_to_string
                                                 args_e1 in
                                             FStar_Util.print3
                                               "Encoding partial application, head_type = %s, formals = %s, args = %s\n"
                                               uu____8216 uu____8218
                                               uu____8221
                                           else ());
                                          (match head3.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_uinst
                                               ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_fvar
                                                    fv;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____8231;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____8232;_},
                                                uu____8233)
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
                                           | uu____8251 ->
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
           let uu____8340 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____8340 with
            | (bs1, body1, opening) ->
                let fallback uu____8363 =
                  let f =
                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                      env.FStar_SMTEncoding_Env.current_module_name "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding")) in
                  let uu____8373 =
                    let uu____8374 =
                      FStar_SMTEncoding_Term.mk_fv
                        (f, FStar_SMTEncoding_Term.Term_sort) in
                    FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV
                      uu____8374 in
                  let uu____8376 =
                    FStar_All.pipe_right [decl]
                      FStar_SMTEncoding_Term.mk_decls_trivial in
                  (uu____8373, uu____8376) in
                let is_impure rc =
                  let uu____8386 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                      env.FStar_SMTEncoding_Env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect in
                  FStar_All.pipe_right uu____8386 Prims.op_Negation in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None ->
                        let uu____8401 =
                          let uu____8414 =
                            FStar_TypeChecker_Env.get_range
                              env.FStar_SMTEncoding_Env.tcenv in
                          FStar_TypeChecker_Util.new_implicit_var
                            "SMTEncoding codomain" uu____8414
                            env.FStar_SMTEncoding_Env.tcenv
                            FStar_Syntax_Util.ktype0 in
                        (match uu____8401 with
                         | (t1, uu____8417, uu____8418) -> t1)
                    | FStar_Pervasives_Native.Some t1 -> t1 in
                  let uu____8436 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid in
                  if uu____8436
                  then
                    let uu____8441 = FStar_Syntax_Syntax.mk_Total res_typ in
                    FStar_Pervasives_Native.Some uu____8441
                  else
                    (let uu____8444 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid in
                     if uu____8444
                     then
                       let uu____8449 = FStar_Syntax_Syntax.mk_GTotal res_typ in
                       FStar_Pervasives_Native.Some uu____8449
                     else FStar_Pervasives_Native.None) in
                (match lopt with
                 | FStar_Pervasives_Native.None ->
                     ((let uu____8457 =
                         let uu____8463 =
                           let uu____8465 =
                             FStar_Syntax_Print.term_to_string t0 in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____8465 in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____8463) in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____8457);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8470 =
                       (is_impure rc) &&
                         (let uu____8473 =
                            FStar_TypeChecker_Env.is_reifiable_rc
                              env.FStar_SMTEncoding_Env.tcenv rc in
                          Prims.op_Negation uu____8473) in
                     if uu____8470
                     then fallback ()
                     else
                       (let uu____8482 =
                          encode_binders FStar_Pervasives_Native.None bs1 env in
                        match uu____8482 with
                        | (vars, guards, envbody, decls, uu____8507) ->
                            let body2 =
                              let uu____8521 =
                                FStar_TypeChecker_Env.is_reifiable_rc
                                  env.FStar_SMTEncoding_Env.tcenv rc in
                              if uu____8521
                              then
                                FStar_TypeChecker_Util.reify_body
                                  env.FStar_SMTEncoding_Env.tcenv body1
                              else body1 in
                            let uu____8526 = encode_term body2 envbody in
                            (match uu____8526 with
                             | (body3, decls') ->
                                 let is_pure =
                                   FStar_Syntax_Util.is_pure_effect
                                     rc.FStar_Syntax_Syntax.residual_effect in
                                 let uu____8539 =
                                   let uu____8548 = codomain_eff rc in
                                   match uu____8548 with
                                   | FStar_Pervasives_Native.None ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c in
                                       let uu____8567 = encode_term tfun env in
                                       (match uu____8567 with
                                        | (t1, decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1)) in
                                 (match uu____8539 with
                                  | (arrow_t_opt, decls'') ->
                                      let key_body =
                                        let uu____8601 =
                                          let uu____8612 =
                                            let uu____8613 =
                                              let uu____8618 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____8618, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8613 in
                                          ([], vars, uu____8612) in
                                        FStar_SMTEncoding_Term.mkForall
                                          t0.FStar_Syntax_Syntax.pos
                                          uu____8601 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let uu____8626 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None ->
                                            (cvars, key_body)
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____8642 =
                                              let uu____8645 =
                                                let uu____8656 =
                                                  FStar_SMTEncoding_Term.free_variables
                                                    t1 in
                                                FStar_List.append uu____8656
                                                  cvars in
                                              FStar_Util.remove_dups
                                                FStar_SMTEncoding_Term.fv_eq
                                                uu____8645 in
                                            let uu____8683 =
                                              FStar_SMTEncoding_Util.mkAnd
                                                (key_body, t1) in
                                            (uu____8642, uu____8683) in
                                      (match uu____8626 with
                                       | (cvars1, key_body1) ->
                                           let tkey =
                                             FStar_SMTEncoding_Term.mkForall
                                               t0.FStar_Syntax_Syntax.pos
                                               ([], cvars1, key_body1) in
                                           let tkey_hash =
                                             FStar_SMTEncoding_Term.hash_of_term
                                               tkey in
                                           ((let uu____8706 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env.FStar_SMTEncoding_Env.tcenv)
                                                 (FStar_Options.Other
                                                    "PartialApp") in
                                             if uu____8706
                                             then
                                               let uu____8711 =
                                                 let uu____8713 =
                                                   FStar_List.map
                                                     FStar_SMTEncoding_Term.fv_name
                                                     vars in
                                                 FStar_All.pipe_right
                                                   uu____8713
                                                   (FStar_String.concat ", ") in
                                               let uu____8723 =
                                                 FStar_SMTEncoding_Term.print_smt_term
                                                   body3 in
                                               FStar_Util.print2
                                                 "Checking eta expansion of\n\tvars={%s}\n\tbody=%s\n"
                                                 uu____8711 uu____8723
                                             else ());
                                            (let uu____8728 =
                                               is_an_eta_expansion env vars
                                                 body3 in
                                             match uu____8728 with
                                             | FStar_Pervasives_Native.Some
                                                 t1 ->
                                                 ((let uu____8737 =
                                                     FStar_All.pipe_left
                                                       (FStar_TypeChecker_Env.debug
                                                          env.FStar_SMTEncoding_Env.tcenv)
                                                       (FStar_Options.Other
                                                          "PartialApp") in
                                                   if uu____8737
                                                   then
                                                     let uu____8742 =
                                                       FStar_SMTEncoding_Term.print_smt_term
                                                         t1 in
                                                     FStar_Util.print1
                                                       "Yes, is an eta expansion of\n\tcore=%s\n"
                                                       uu____8742
                                                   else ());
                                                  (let decls1 =
                                                     FStar_List.append decls
                                                       (FStar_List.append
                                                          decls' decls'') in
                                                   (t1, decls1)))
                                             | FStar_Pervasives_Native.None
                                                 ->
                                                 let cvar_sorts =
                                                   FStar_List.map
                                                     FStar_SMTEncoding_Term.fv_sort
                                                     cvars1 in
                                                 let fsym =
                                                   let uu____8755 =
                                                     FStar_Util.digest_of_string
                                                       tkey_hash in
                                                   Prims.op_Hat "Tm_abs_"
                                                     uu____8755 in
                                                 let fdecl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (fsym, cvar_sorts,
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       FStar_Pervasives_Native.None) in
                                                 let f =
                                                   let uu____8764 =
                                                     let uu____8772 =
                                                       FStar_List.map
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                         cvars1 in
                                                     (fsym, uu____8772) in
                                                   FStar_SMTEncoding_Util.mkApp
                                                     uu____8764 in
                                                 let app = mk_Apply f vars in
                                                 let typing_f =
                                                   match arrow_t_opt with
                                                   | FStar_Pervasives_Native.None
                                                       ->
                                                       let tot_fun_ax =
                                                         let ax =
                                                           let uu____8786 =
                                                             FStar_All.pipe_right
                                                               vars
                                                               (FStar_List.map
                                                                  (fun
                                                                    uu____8794
                                                                    ->
                                                                    FStar_SMTEncoding_Util.mkTrue)) in
                                                           isTotFun_axioms
                                                             t0.FStar_Syntax_Syntax.pos
                                                             f vars
                                                             uu____8786
                                                             is_pure in
                                                         match cvars1 with
                                                         | [] -> ax
                                                         | uu____8795 ->
                                                             FStar_SMTEncoding_Term.mkForall
                                                               t0.FStar_Syntax_Syntax.pos
                                                               ([[f]],
                                                                 cvars1, ax) in
                                                       let a_name =
                                                         Prims.op_Hat
                                                           "tot_fun_" fsym in
                                                       let uu____8809 =
                                                         FStar_SMTEncoding_Util.mkAssume
                                                           (tot_fun_ax,
                                                             (FStar_Pervasives_Native.Some
                                                                a_name),
                                                             a_name) in
                                                       [uu____8809]
                                                   | FStar_Pervasives_Native.Some
                                                       t1 ->
                                                       let f_has_t =
                                                         FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                           FStar_Pervasives_Native.None
                                                           f t1 in
                                                       let a_name =
                                                         Prims.op_Hat
                                                           "typing_" fsym in
                                                       let uu____8817 =
                                                         let uu____8818 =
                                                           let uu____8826 =
                                                             FStar_SMTEncoding_Term.mkForall
                                                               t0.FStar_Syntax_Syntax.pos
                                                               ([[f]],
                                                                 cvars1,
                                                                 f_has_t) in
                                                           (uu____8826,
                                                             (FStar_Pervasives_Native.Some
                                                                a_name),
                                                             a_name) in
                                                         FStar_SMTEncoding_Util.mkAssume
                                                           uu____8818 in
                                                       [uu____8817] in
                                                 let interp_f =
                                                   let a_name =
                                                     Prims.op_Hat
                                                       "interpretation_" fsym in
                                                   let uu____8841 =
                                                     let uu____8849 =
                                                       let uu____8850 =
                                                         let uu____8861 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app, body3) in
                                                         ([[app]],
                                                           (FStar_List.append
                                                              vars cvars1),
                                                           uu____8861) in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         t0.FStar_Syntax_Syntax.pos
                                                         uu____8850 in
                                                     (uu____8849,
                                                       (FStar_Pervasives_Native.Some
                                                          a_name), a_name) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____8841 in
                                                 let f_decls =
                                                   FStar_List.append (fdecl
                                                     :: typing_f) [interp_f] in
                                                 let uu____8875 =
                                                   let uu____8876 =
                                                     let uu____8879 =
                                                       let uu____8882 =
                                                         FStar_SMTEncoding_Term.mk_decls
                                                           fsym tkey_hash
                                                           f_decls
                                                           (FStar_List.append
                                                              decls
                                                              (FStar_List.append
                                                                 decls'
                                                                 decls'')) in
                                                       FStar_List.append
                                                         decls'' uu____8882 in
                                                     FStar_List.append decls'
                                                       uu____8879 in
                                                   FStar_List.append decls
                                                     uu____8876 in
                                                 (f, uu____8875)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8885,
             { FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____8886;
               FStar_Syntax_Syntax.lbunivs = uu____8887;
               FStar_Syntax_Syntax.lbtyp = uu____8888;
               FStar_Syntax_Syntax.lbeff = uu____8889;
               FStar_Syntax_Syntax.lbdef = uu____8890;
               FStar_Syntax_Syntax.lbattrs = uu____8891;
               FStar_Syntax_Syntax.lbpos = uu____8892;_}::uu____8893),
            uu____8894)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false,
             { FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
               FStar_Syntax_Syntax.lbunivs = uu____8928;
               FStar_Syntax_Syntax.lbtyp = t1;
               FStar_Syntax_Syntax.lbeff = uu____8930;
               FStar_Syntax_Syntax.lbdef = e1;
               FStar_Syntax_Syntax.lbattrs = uu____8932;
               FStar_Syntax_Syntax.lbpos = uu____8933;_}::[]),
            e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let
           ((false, uu____8960::uu____8961), uu____8962) ->
           failwith "Impossible: non-recursive let with multiple bindings"
       | FStar_Syntax_Syntax.Tm_let ((uu____8985, lbs), uu____8987) ->
           let names1 =
             FStar_All.pipe_right lbs
               (FStar_List.map
                  (fun lb ->
                     let uu____9040 = lb in
                     match uu____9040 with
                     | { FStar_Syntax_Syntax.lbname = lbname;
                         FStar_Syntax_Syntax.lbunivs = uu____9047;
                         FStar_Syntax_Syntax.lbtyp = uu____9048;
                         FStar_Syntax_Syntax.lbeff = uu____9049;
                         FStar_Syntax_Syntax.lbdef = uu____9050;
                         FStar_Syntax_Syntax.lbattrs = uu____9051;
                         FStar_Syntax_Syntax.lbpos = uu____9052;_} ->
                         let x = FStar_Util.left lbname in
                         let uu____9068 =
                           FStar_Ident.text_of_id
                             x.FStar_Syntax_Syntax.ppname in
                         let uu____9070 = FStar_Syntax_Syntax.range_of_bv x in
                         (uu____9068, uu____9070))) in
           FStar_Exn.raise (FStar_SMTEncoding_Env.Inner_let_rec names1)
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
              let uu____9128 =
                let uu____9133 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None) in
                encode_term uu____9133 env in
              match uu____9128 with
              | (ee1, decls1) ->
                  let uu____9158 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2 in
                  (match uu____9158 with
                   | (xs, e21) ->
                       let uu____9183 = FStar_List.hd xs in
                       (match uu____9183 with
                        | (x1, uu____9201) ->
                            let env' =
                              FStar_SMTEncoding_Env.push_term_var env x1 ee1 in
                            let uu____9207 = encode_body e21 env' in
                            (match uu____9207 with
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
            let uu____9237 =
              let uu____9245 =
                let uu____9246 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____9246 in
              FStar_SMTEncoding_Env.gen_term_var env uu____9245 in
            match uu____9237 with
            | (scrsym, scr', env1) ->
                let uu____9256 = encode_term e env1 in
                (match uu____9256 with
                 | (scr, decls) ->
                     let uu____9267 =
                       let encode_branch b uu____9296 =
                         match uu____9296 with
                         | (else_case, decls1) ->
                             let uu____9315 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____9315 with
                              | (p, w, br) ->
                                  let uu____9341 = encode_pat env1 p in
                                  (match uu____9341 with
                                   | (env0, pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2 ->
                                                 fun uu____9378 ->
                                                   match uu____9378 with
                                                   | (x, t) ->
                                                       FStar_SMTEncoding_Env.push_term_var
                                                         env2 x t) env1) in
                                       let uu____9385 =
                                         match w with
                                         | FStar_Pervasives_Native.None ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____9407 =
                                               encode_term w1 env2 in
                                             (match uu____9407 with
                                              | (w2, decls2) ->
                                                  let uu____9420 =
                                                    let uu____9421 =
                                                      let uu____9426 =
                                                        let uu____9427 =
                                                          let uu____9432 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____9432) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____9427 in
                                                      (guard, uu____9426) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____9421 in
                                                  (uu____9420, decls2)) in
                                       (match uu____9385 with
                                        | (guard1, decls2) ->
                                            let uu____9447 =
                                              encode_br br env2 in
                                            (match uu____9447 with
                                             | (br1, decls3) ->
                                                 let uu____9460 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____9460,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____9267 with
                      | (match_tm, decls1) ->
                          let uu____9481 =
                            let uu____9482 =
                              let uu____9493 =
                                let uu____9500 =
                                  let uu____9505 =
                                    FStar_SMTEncoding_Term.mk_fv
                                      (scrsym,
                                        FStar_SMTEncoding_Term.Term_sort) in
                                  (uu____9505, scr) in
                                [uu____9500] in
                              (uu____9493, match_tm) in
                            FStar_SMTEncoding_Term.mkLet' uu____9482
                              FStar_Range.dummyRange in
                          (uu____9481, decls1)))
and (encode_pat :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.pat -> (FStar_SMTEncoding_Env.env_t * pattern))
  =
  fun env ->
    fun pat ->
      (let uu____9528 =
         FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
           FStar_Options.Medium in
       if uu____9528
       then
         let uu____9531 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____9531
       else ());
      (let uu____9536 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____9536 with
       | (vars, pat_term) ->
           let uu____9553 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____9595 ->
                     fun v1 ->
                       match uu____9595 with
                       | (env1, vars1) ->
                           let uu____9631 =
                             FStar_SMTEncoding_Env.gen_term_var env1 v1 in
                           (match uu____9631 with
                            | (xx, uu____9650, env2) ->
                                let uu____9654 =
                                  let uu____9661 =
                                    let uu____9666 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xx,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    (v1, uu____9666) in
                                  uu____9661 :: vars1 in
                                (env2, uu____9654))) (env, [])) in
           (match uu____9553 with
            | (env1, vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9721 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9722 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9723 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9731 = encode_const c env1 in
                      (match uu____9731 with
                       | (tm, decls) ->
                           ((match decls with
                             | uu____9739::uu____9740 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____9744 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f, args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon
                            env1.FStar_SMTEncoding_Env.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____9767 =
                          FStar_TypeChecker_Env.datacons_of_typ
                            env1.FStar_SMTEncoding_Env.tcenv tc_name in
                        match uu____9767 with
                        | (uu____9775, uu____9776::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9781 ->
                            FStar_SMTEncoding_Env.mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i ->
                                fun uu____9817 ->
                                  match uu____9817 with
                                  | (arg, uu____9827) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9836 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____9836)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x, uu____9868) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9899 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f, args) ->
                      let uu____9924 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i ->
                                fun uu____9970 ->
                                  match uu____9970 with
                                  | (arg, uu____9986) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9995 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____9995)) in
                      FStar_All.pipe_right uu____9924 FStar_List.flatten in
                let pat_term1 uu____10026 = encode_term pat_term env1 in
                let pattern =
                  {
                    pat_vars = vars1;
                    pat_term = pat_term1;
                    guard = (mk_guard pat);
                    projections = (mk_projections pat)
                  } in
                (env1, pattern)))
and (encode_args :
  FStar_Syntax_Syntax.args ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term Prims.list *
        FStar_SMTEncoding_Term.decls_t))
  =
  fun l ->
    fun env ->
      let uu____10036 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____10084 ->
                fun uu____10085 ->
                  match (uu____10084, uu____10085) with
                  | ((tms, decls), (t, uu____10125)) ->
                      let uu____10152 = encode_term t env in
                      (match uu____10152 with
                       | (t1, decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____10036 with | (l1, decls) -> ((FStar_List.rev l1), decls)
and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t ->
    fun env ->
      let universe_of_binders binders =
        FStar_List.map (fun uu____10230 -> FStar_Syntax_Syntax.U_zero)
          binders in
      let quant = FStar_Syntax_Util.smt_lemma_as_forall t universe_of_binders in
      let env1 =
        let uu___1400_10239 = env in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___1400_10239.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___1400_10239.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___1400_10239.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___1400_10239.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___1400_10239.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___1400_10239.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___1400_10239.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___1400_10239.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___1400_10239.FStar_SMTEncoding_Env.encoding_quantifier);
          FStar_SMTEncoding_Env.global_cache =
            (uu___1400_10239.FStar_SMTEncoding_Env.global_cache)
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
        let uu___1405_10256 = env in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___1405_10256.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___1405_10256.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___1405_10256.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___1405_10256.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___1405_10256.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___1405_10256.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___1405_10256.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___1405_10256.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___1405_10256.FStar_SMTEncoding_Env.encoding_quantifier);
          FStar_SMTEncoding_Env.global_cache =
            (uu___1405_10256.FStar_SMTEncoding_Env.global_cache)
        } in
      let encode_smt_pattern t =
        let uu____10272 = FStar_Syntax_Util.head_and_args t in
        match uu____10272 with
        | (head1, args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                uu____10335::(x, uu____10337)::(t1, uu____10339)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____10406 = encode_term x env1 in
                 (match uu____10406 with
                  | (x1, decls) ->
                      let uu____10417 = encode_term t1 env1 in
                      (match uu____10417 with
                       | (t2, decls') ->
                           let uu____10428 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t2 in
                           (uu____10428, (FStar_List.append decls decls'))))
             | uu____10429 -> encode_term t env1) in
      FStar_List.fold_right
        (fun pats ->
           fun uu____10472 ->
             match uu____10472 with
             | (pats_l1, decls) ->
                 let uu____10517 =
                   FStar_List.fold_right
                     (fun uu____10552 ->
                        fun uu____10553 ->
                          match (uu____10552, uu____10553) with
                          | ((p, uu____10595), (pats1, decls1)) ->
                              let uu____10630 = encode_smt_pattern p in
                              (match uu____10630 with
                               | (t, d) ->
                                   let uu____10645 =
                                     FStar_SMTEncoding_Term.check_pattern_ok
                                       t in
                                   (match uu____10645 with
                                    | FStar_Pervasives_Native.None ->
                                        ((t :: pats1),
                                          (FStar_List.append d decls1))
                                    | FStar_Pervasives_Native.Some
                                        illegal_subterm ->
                                        ((let uu____10662 =
                                            let uu____10668 =
                                              let uu____10670 =
                                                FStar_Syntax_Print.term_to_string
                                                  p in
                                              let uu____10672 =
                                                FStar_SMTEncoding_Term.print_smt_term
                                                  illegal_subterm in
                                              FStar_Util.format2
                                                "Pattern %s contains illegal sub-term (%s); dropping it"
                                                uu____10670 uu____10672 in
                                            (FStar_Errors.Warning_SMTPatternIllFormed,
                                              uu____10668) in
                                          FStar_Errors.log_issue
                                            p.FStar_Syntax_Syntax.pos
                                            uu____10662);
                                         (pats1,
                                           (FStar_List.append d decls1))))))
                     pats ([], decls) in
                 (match uu____10517 with
                  | (pats1, decls1) -> ((pats1 :: pats_l1), decls1))) pats_l
        ([], [])
and (encode_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun phi ->
    fun env ->
      let debug1 phi1 =
        let uu____10732 =
          FStar_All.pipe_left
            (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____10732
        then
          let uu____10737 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____10739 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10737 uu____10739
        else () in
      let enc f r l =
        let uu____10781 =
          FStar_Util.fold_map
            (fun decls ->
               fun x ->
                 let uu____10813 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____10813 with
                 | (t, decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____10781 with
        | (decls, args) ->
            let uu____10844 =
              let uu___1469_10845 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___1469_10845.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___1469_10845.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____10844, decls) in
      let const_op f r uu____10880 =
        let uu____10893 = f r in (uu____10893, []) in
      let un_op f l =
        let uu____10916 = FStar_List.hd l in
        FStar_All.pipe_left f uu____10916 in
      let bin_op f uu___2_10936 =
        match uu___2_10936 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10947 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____10988 =
          FStar_Util.fold_map
            (fun decls ->
               fun uu____11013 ->
                 match uu____11013 with
                 | (t, uu____11029) ->
                     let uu____11034 = encode_formula t env in
                     (match uu____11034 with
                      | (phi1, decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____10988 with
        | (decls, phis) ->
            let uu____11063 =
              let uu___1499_11064 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___1499_11064.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___1499_11064.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____11063, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____11127 ->
               match uu____11127 with
               | (a, q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____11148) -> false
                    | uu____11151 -> true)) args in
        if (FStar_List.length rf) <> (Prims.of_int (2))
        then
          let uu____11170 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____11170
        else
          (let uu____11187 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____11187 r rf) in
      let eq3_op r args =
        let n1 = FStar_List.length args in
        if n1 = (Prims.of_int (4))
        then
          let uu____11255 =
            enc
              (fun terms ->
                 match terms with
                 | t0::t1::v0::v1::[] ->
                     let uu____11287 =
                       let uu____11292 = FStar_SMTEncoding_Util.mkEq (t0, t1) in
                       let uu____11293 = FStar_SMTEncoding_Util.mkEq (v0, v1) in
                       (uu____11292, uu____11293) in
                     FStar_SMTEncoding_Util.mkAnd uu____11287
                 | uu____11294 -> failwith "Impossible") in
          uu____11255 r args
        else
          (let uu____11300 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1) in
           failwith uu____11300) in
      let h_equals_op r args =
        let n1 = FStar_List.length args in
        if n1 = (Prims.of_int (4))
        then
          let uu____11362 =
            enc
              (fun terms ->
                 match terms with
                 | t0::v0::t1::v1::[] ->
                     let uu____11394 =
                       let uu____11399 = FStar_SMTEncoding_Util.mkEq (t0, t1) in
                       let uu____11400 = FStar_SMTEncoding_Util.mkEq (v0, v1) in
                       (uu____11399, uu____11400) in
                     FStar_SMTEncoding_Util.mkAnd uu____11394
                 | uu____11401 -> failwith "Impossible") in
          uu____11362 r args
        else
          (let uu____11407 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1) in
           failwith uu____11407) in
      let mk_imp1 r uu___3_11436 =
        match uu___3_11436 with
        | (lhs, uu____11442)::(rhs, uu____11444)::[] ->
            let uu____11485 = encode_formula rhs env in
            (match uu____11485 with
             | (l1, decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp, uu____11500) ->
                      (l1, decls1)
                  | uu____11505 ->
                      let uu____11506 = encode_formula lhs env in
                      (match uu____11506 with
                       | (l2, decls2) ->
                           let uu____11517 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____11517, (FStar_List.append decls1 decls2)))))
        | uu____11518 -> failwith "impossible" in
      let mk_ite r uu___4_11546 =
        match uu___4_11546 with
        | (guard, uu____11552)::(_then, uu____11554)::(_else, uu____11556)::[]
            ->
            let uu____11613 = encode_formula guard env in
            (match uu____11613 with
             | (g, decls1) ->
                 let uu____11624 = encode_formula _then env in
                 (match uu____11624 with
                  | (t, decls2) ->
                      let uu____11635 = encode_formula _else env in
                      (match uu____11635 with
                       | (e, decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11647 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____11677 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____11677 in
      let connectives =
        let uu____11707 =
          let uu____11732 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____11732) in
        let uu____11775 =
          let uu____11802 =
            let uu____11827 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____11827) in
          let uu____11870 =
            let uu____11897 =
              let uu____11924 =
                let uu____11949 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____11949) in
              let uu____11992 =
                let uu____12019 =
                  let uu____12046 =
                    let uu____12071 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____12071) in
                  [uu____12046;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.c_eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq3_op);
                  (FStar_Parser_Const.c_eq3_lid, h_equals_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____12019 in
              uu____11924 :: uu____11992 in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11897 in
          uu____11802 :: uu____11870 in
        uu____11707 :: uu____11775 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) ->
            let uu____12616 = encode_formula phi' env in
            (match uu____12616 with
             | (phi2, decls) ->
                 let uu____12627 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____12627, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____12629 ->
            let uu____12636 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____12636 env
        | FStar_Syntax_Syntax.Tm_match (e, pats) ->
            let uu____12675 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____12675 with | (t, decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false,
              { FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____12687;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____12689;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____12691;
                FStar_Syntax_Syntax.lbpos = uu____12692;_}::[]),
             e2)
            ->
            let uu____12719 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____12719 with | (t, decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1, args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                uu____12772::(x, uu____12774)::(t, uu____12776)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12843 = encode_term x env in
                 (match uu____12843 with
                  | (x1, decls) ->
                      let uu____12854 = encode_term t env in
                      (match uu____12854 with
                       | (t1, decls') ->
                           let uu____12865 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____12865, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                (r, uu____12868)::(msg, uu____12870)::(phi2, uu____12872)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12939 =
                   let uu____12944 =
                     let uu____12945 = FStar_Syntax_Subst.compress r in
                     uu____12945.FStar_Syntax_Syntax.n in
                   let uu____12948 =
                     let uu____12949 = FStar_Syntax_Subst.compress msg in
                     uu____12949.FStar_Syntax_Syntax.n in
                   (uu____12944, uu____12948) in
                 (match uu____12939 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1), FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s, uu____12958))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1 in
                      fallback phi3
                  | uu____12969 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv, (t, uu____12976)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____13011 ->
                 let encode_valid uu____13035 =
                   let uu____13036 = encode_term phi1 env in
                   match uu____13036 with
                   | (tt, decls) ->
                       let tt1 =
                         let uu____13048 =
                           let uu____13050 =
                             FStar_Range.use_range
                               tt.FStar_SMTEncoding_Term.rng in
                           let uu____13051 =
                             FStar_Range.use_range
                               phi1.FStar_Syntax_Syntax.pos in
                           FStar_Range.rng_included uu____13050 uu____13051 in
                         if uu____13048
                         then tt
                         else
                           (let uu___1687_13055 = tt in
                            {
                              FStar_SMTEncoding_Term.tm =
                                (uu___1687_13055.FStar_SMTEncoding_Term.tm);
                              FStar_SMTEncoding_Term.freevars =
                                (uu___1687_13055.FStar_SMTEncoding_Term.freevars);
                              FStar_SMTEncoding_Term.rng =
                                (phi1.FStar_Syntax_Syntax.pos)
                            }) in
                       let uu____13056 = FStar_SMTEncoding_Term.mk_Valid tt1 in
                       (uu____13056, decls) in
                 let uu____13057 = head_redex env head2 in
                 if uu____13057
                 then
                   let uu____13064 = maybe_whnf env head2 in
                   (match uu____13064 with
                    | FStar_Pervasives_Native.None -> encode_valid ()
                    | FStar_Pervasives_Native.Some phi2 ->
                        encode_formula phi2 env)
                 else encode_valid ())
        | uu____13074 ->
            let uu____13075 = encode_term phi1 env in
            (match uu____13075 with
             | (tt, decls) ->
                 let tt1 =
                   let uu____13087 =
                     let uu____13089 =
                       FStar_Range.use_range tt.FStar_SMTEncoding_Term.rng in
                     let uu____13090 =
                       FStar_Range.use_range phi1.FStar_Syntax_Syntax.pos in
                     FStar_Range.rng_included uu____13089 uu____13090 in
                   if uu____13087
                   then tt
                   else
                     (let uu___1699_13094 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___1699_13094.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___1699_13094.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 let uu____13095 = FStar_SMTEncoding_Term.mk_Valid tt1 in
                 (uu____13095, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____13139 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____13139 with
        | (vars, guards, env2, decls, uu____13178) ->
            let uu____13191 = encode_smt_patterns ps env2 in
            (match uu____13191 with
             | (pats, decls') ->
                 let uu____13228 = encode_formula body env2 in
                 (match uu____13228 with
                  | (body1, decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf, p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____13260;
                             FStar_SMTEncoding_Term.rng = uu____13261;_}::[])::[]
                            when
                            let uu____13281 =
                              FStar_Ident.text_of_lid
                                FStar_Parser_Const.guard_free in
                            uu____13281 = gf -> []
                        | uu____13284 -> guards in
                      let uu____13289 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____13289, body1,
                        (FStar_List.append decls
                           (FStar_List.append decls' decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let uu____13300 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____13300 with
       | FStar_Pervasives_Native.None -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op, arms))
           ->
           let uu____13309 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____13415 ->
                     match uu____13415 with
                     | (l, uu____13440) -> FStar_Ident.lid_equals op l)) in
           (match uu____13309 with
            | FStar_Pervasives_Native.None -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____13509, f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars, pats, body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____13601 = encode_q_body env vars pats body in
             match uu____13601 with
             | (vars1, pats1, guard, body1, decls) ->
                 let tm =
                   let uu____13646 =
                     let uu____13657 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____13657) in
                   FStar_SMTEncoding_Term.mkForall
                     phi1.FStar_Syntax_Syntax.pos uu____13646 in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars, pats, body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____13688 = encode_q_body env vars pats body in
             match uu____13688 with
             | (vars1, pats1, guard, body1, decls) ->
                 let uu____13732 =
                   let uu____13733 =
                     let uu____13744 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____13744) in
                   FStar_SMTEncoding_Term.mkExists
                     phi1.FStar_Syntax_Syntax.pos uu____13733 in
                 (uu____13732, decls))))