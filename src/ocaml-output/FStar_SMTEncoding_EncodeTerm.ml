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
  = fun mname -> fun r -> mkForall_fuel' mname r (Prims.parse_int "1")
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
let (trivial_post : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let uu____460 =
      let uu____461 = FStar_Syntax_Syntax.null_binder t in [uu____461] in
    let uu____480 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
    FStar_Syntax_Util.abs uu____460 uu____480 FStar_Pervasives_Native.None
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
                let uu____502 = FStar_SMTEncoding_Term.fv_sort var in
                match uu____502 with
                | FStar_SMTEncoding_Term.Fuel_sort ->
                    let uu____503 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____503
                | s ->
                    let uu____506 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____506) e)
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
          let uu____562 =
            let uu____568 =
              let uu____570 = FStar_Util.string_of_int arity in
              let uu____572 = FStar_Util.string_of_int n_args in
              FStar_Util.format3
                "Head symbol %s expects at least %s arguments; got only %s"
                head1 uu____570 uu____572 in
            (FStar_Errors.Fatal_SMTEncodingArityMismatch, uu____568) in
          FStar_Errors.raise_error uu____562 rng
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
              | uu____660 ->
                  FStar_SMTEncoding_Term.mkForall pos (pat, vars1, body) in
            let rec is_tot_fun_axioms ctx ctx_guard head2 vars1 guards1 =
              match (vars1, guards1) with
              | ([], []) -> FStar_SMTEncoding_Util.mkTrue
              | (uu____777::[], uu____778) ->
                  if is_pure
                  then
                    let uu____818 =
                      let uu____819 =
                        let uu____824 =
                          FStar_SMTEncoding_Term.mk_IsTotFun head2 in
                        (ctx_guard, uu____824) in
                      FStar_SMTEncoding_Util.mkImp uu____819 in
                    maybe_mkForall [[head2]] ctx uu____818
                  else FStar_SMTEncoding_Util.mkTrue
              | (x::vars2, g_x::guards2) ->
                  let is_tot_fun_head =
                    let uu____876 =
                      let uu____877 =
                        let uu____882 =
                          FStar_SMTEncoding_Term.mk_IsTotFun head2 in
                        (ctx_guard, uu____882) in
                      FStar_SMTEncoding_Util.mkImp uu____877 in
                    maybe_mkForall [[head2]] ctx uu____876 in
                  let app = mk_Apply head2 [x] in
                  let ctx1 = FStar_List.append ctx [x] in
                  let ctx_guard1 =
                    FStar_SMTEncoding_Util.mkAnd (ctx_guard, g_x) in
                  let rest =
                    is_tot_fun_axioms ctx1 ctx_guard1 app vars2 guards2 in
                  FStar_SMTEncoding_Util.mkAnd (is_tot_fun_head, rest)
              | uu____941 -> failwith "impossible: isTotFun_axioms" in
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
                  (let uu____1012 = FStar_Util.first_N arity args in
                   match uu____1012 with
                   | (args1, rest) ->
                       let head3 =
                         FStar_SMTEncoding_Util.mkApp' (head2, args1) in
                       mk_Apply_args head3 rest)
                else
                  (let uu____1036 = FStar_SMTEncoding_Term.op_to_string head2 in
                   raise_arity_mismatch uu____1036 arity n_args rng)
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
          let uu____1059 = FStar_SMTEncoding_Env.force_thunk fvb in
          mk_Apply_args uu____1059 args
        else
          maybe_curry_app rng
            (FStar_Util.Inl
               (FStar_SMTEncoding_Term.Var (fvb.FStar_SMTEncoding_Env.smt_id)))
            fvb.FStar_SMTEncoding_Env.smt_arity args
let (is_app : FStar_SMTEncoding_Term.op -> Prims.bool) =
  fun uu___1_1068 ->
    match uu___1_1068 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____1074 -> false
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
                   FStar_SMTEncoding_Term.freevars = uu____1122;
                   FStar_SMTEncoding_Term.rng = uu____1123;_}::[]),
             x::xs1) when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)
              -> check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var f, args),
             uu____1154) ->
              let uu____1164 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a ->
                        fun v1 ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____1181 -> false) args (FStar_List.rev xs)) in
              if uu____1164
              then
                let n1 = FStar_SMTEncoding_Env.tok_of_name env f in
                ((let uu____1190 =
                    FStar_All.pipe_left
                      (FStar_TypeChecker_Env.debug
                         env.FStar_SMTEncoding_Env.tcenv)
                      (FStar_Options.Other "PartialApp") in
                  if uu____1190
                  then
                    let uu____1195 = FStar_SMTEncoding_Term.print_smt_term t in
                    let uu____1197 =
                      match n1 with
                      | FStar_Pervasives_Native.None -> "None"
                      | FStar_Pervasives_Native.Some x ->
                          FStar_SMTEncoding_Term.print_smt_term x in
                    FStar_Util.print2
                      "is_eta_expansion %s  ... tok_of_name = %s\n"
                      uu____1195 uu____1197
                  else ());
                 n1)
              else FStar_Pervasives_Native.None
          | (uu____1207, []) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____1211 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv ->
                        let uu____1219 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____1219)) in
              if uu____1211
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____1226 -> FStar_Pervasives_Native.None in
        check_partial_applications body (FStar_List.rev vars)
let check_pattern_vars :
  'Auu____1244 'Auu____1245 .
    FStar_SMTEncoding_Env.env_t ->
      (FStar_Syntax_Syntax.bv * 'Auu____1244) Prims.list ->
        (FStar_Syntax_Syntax.term * 'Auu____1245) Prims.list -> unit
  =
  fun env ->
    fun vars ->
      fun pats ->
        let pats1 =
          FStar_All.pipe_right pats
            (FStar_List.map
               (fun uu____1303 ->
                  match uu____1303 with
                  | (x, uu____1309) ->
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.AllowUnboundUniverses;
                        FStar_TypeChecker_Env.EraseUniverses]
                        env.FStar_SMTEncoding_Env.tcenv x)) in
        match pats1 with
        | [] -> ()
        | hd1::tl1 ->
            let pat_vars =
              let uu____1317 = FStar_Syntax_Free.names hd1 in
              FStar_List.fold_left
                (fun out ->
                   fun x ->
                     let uu____1329 = FStar_Syntax_Free.names x in
                     FStar_Util.set_union out uu____1329) uu____1317 tl1 in
            let uu____1332 =
              FStar_All.pipe_right vars
                (FStar_Util.find_opt
                   (fun uu____1359 ->
                      match uu____1359 with
                      | (b, uu____1366) ->
                          let uu____1367 = FStar_Util.set_mem b pat_vars in
                          Prims.op_Negation uu____1367)) in
            (match uu____1332 with
             | FStar_Pervasives_Native.None -> ()
             | FStar_Pervasives_Native.Some (x, uu____1374) ->
                 let pos =
                   FStar_List.fold_left
                     (fun out ->
                        fun t ->
                          FStar_Range.union_ranges out
                            t.FStar_Syntax_Syntax.pos)
                     hd1.FStar_Syntax_Syntax.pos tl1 in
                 let uu____1388 =
                   let uu____1394 =
                     let uu____1396 = FStar_Syntax_Print.bv_to_string x in
                     FStar_Util.format1
                       "SMT pattern misses at least one bound variable: %s"
                       uu____1396 in
                   (FStar_Errors.Warning_SMTPatternIllFormed, uu____1394) in
                 FStar_Errors.log_issue pos uu____1388)
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
        | FStar_Syntax_Syntax.Tm_arrow uu____1682 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____1697 ->
            let uu____1704 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____1704
        | uu____1706 ->
            if norm1
            then let uu____1708 = whnf env t1 in aux false uu____1708
            else
              (let uu____1712 =
                 let uu____1714 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____1716 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____1714 uu____1716 in
               failwith uu____1712) in
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
    | FStar_Syntax_Syntax.Tm_refine (bv, uu____1758) ->
        let uu____1763 =
          curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort in
        (match uu____1763 with
         | (args, res) ->
             (match args with
              | [] ->
                  let uu____1784 = FStar_Syntax_Syntax.mk_Total k1 in
                  ([], uu____1784)
              | uu____1791 -> (args, res)))
    | uu____1792 ->
        let uu____1793 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____1793)
let is_arithmetic_primitive :
  'Auu____1807 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____1807 Prims.list -> Prims.bool
  =
  fun head1 ->
    fun args ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv, uu____1830::uu____1831::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv, uu____1835::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____1838 -> false
let (isInteger : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun tm ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1, FStar_Pervasives_Native.None)) -> true
    | uu____1869 -> false
let (getInteger : FStar_Syntax_Syntax.term' -> Prims.int) =
  fun tm ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1, FStar_Pervasives_Native.None)) -> FStar_Util.int_of_string n1
    | uu____1892 -> failwith "Expected an Integer term"
let is_BitVector_primitive :
  'Auu____1902 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____1902)
        Prims.list -> Prims.bool
  =
  fun head1 ->
    fun args ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,
         (sz_arg, uu____1944)::uu____1945::uu____1946::[]) ->
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
         (sz_arg, uu____1997)::uu____1998::[]) ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____2035 -> false
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
          let uu____2359 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue in
          (uu____2359, [])
      | FStar_Const.Const_bool (false) ->
          let uu____2361 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse in
          (uu____2361, [])
      | FStar_Const.Const_char c1 ->
          let uu____2364 =
            let uu____2365 =
              let uu____2373 =
                let uu____2376 =
                  let uu____2377 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1) in
                  FStar_SMTEncoding_Term.boxInt uu____2377 in
                [uu____2376] in
              ("FStar.Char.__char_of_int", uu____2373) in
            FStar_SMTEncoding_Util.mkApp uu____2365 in
          (uu____2364, [])
      | FStar_Const.Const_int (i, FStar_Pervasives_Native.None) ->
          let uu____2395 =
            let uu____2396 = FStar_SMTEncoding_Util.mkInteger i in
            FStar_SMTEncoding_Term.boxInt uu____2396 in
          (uu____2395, [])
      | FStar_Const.Const_int (repr, FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.FStar_SMTEncoding_Env.tcenv).FStar_TypeChecker_Env.dsenv
              repr sw FStar_Range.dummyRange in
          encode_term syntax_term env
      | FStar_Const.Const_string (s, uu____2417) ->
          let uu____2420 =
            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.string_const s in
          (uu____2420, [])
      | FStar_Const.Const_range uu____2421 ->
          let uu____2422 = FStar_SMTEncoding_Term.mk_Range_const () in
          (uu____2422, [])
      | FStar_Const.Const_effect -> (FStar_SMTEncoding_Term.mk_Term_type, [])
      | FStar_Const.Const_real r ->
          let uu____2425 =
            let uu____2426 = FStar_SMTEncoding_Util.mkReal r in
            FStar_SMTEncoding_Term.boxReal uu____2426 in
          (uu____2425, [])
      | c1 ->
          let uu____2428 =
            let uu____2430 = FStar_Syntax_Print.const_to_string c1 in
            FStar_Util.format1 "Unhandled constant: %s" uu____2430 in
          failwith uu____2428
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
        (let uu____2459 =
           FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
             FStar_Options.Medium in
         if uu____2459
         then
           let uu____2462 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____2462
         else ());
        (let uu____2468 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2550 ->
                   fun b ->
                     match uu____2550 with
                     | (vars, guards, env1, decls, names1) ->
                         let uu____2615 =
                           let x = FStar_Pervasives_Native.fst b in
                           let uu____2631 =
                             FStar_SMTEncoding_Env.gen_term_var env1 x in
                           match uu____2631 with
                           | (xxsym, xx, env') ->
                               let uu____2656 =
                                 let uu____2661 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____2661 env1 xx in
                               (match uu____2656 with
                                | (guard_x_t, decls') ->
                                    let uu____2676 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xxsym,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    (uu____2676, guard_x_t, env', decls', x)) in
                         (match uu____2615 with
                          | (v1, g, env2, decls', n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____2468 with
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
          let uu____2776 = encode_term t env in
          match uu____2776 with
          | (t1, decls) ->
              let uu____2787 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____2787, decls)
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
          let uu____2798 = encode_term t env in
          match uu____2798 with
          | (t1, decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None ->
                   let uu____2813 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____2813, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____2815 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____2815, decls))
and (encode_arith_term :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun env ->
    fun head1 ->
      fun args_e ->
        let uu____2821 = encode_args args_e env in
        match uu____2821 with
        | (arg_tms, decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____2840 -> failwith "Impossible" in
            let unary unbox arg_tms1 =
              let uu____2862 = FStar_List.hd arg_tms1 in unbox uu____2862 in
            let binary unbox arg_tms1 =
              let uu____2887 =
                let uu____2888 = FStar_List.hd arg_tms1 in unbox uu____2888 in
              let uu____2889 =
                let uu____2890 =
                  let uu____2891 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____2891 in
                unbox uu____2890 in
              (uu____2887, uu____2889) in
            let mk_default uu____2899 =
              let uu____2900 =
                FStar_SMTEncoding_Env.lookup_free_var_sym env
                  head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____2900 with
              | (fname, fuel_args, arity) ->
                  let args = FStar_List.append fuel_args arg_tms in
                  maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity
                    args in
            let mk_l box op mk_args ts =
              let uu____2989 = FStar_Options.smtencoding_l_arith_native () in
              if uu____2989
              then
                let uu____2992 = let uu____2993 = mk_args ts in op uu____2993 in
                FStar_All.pipe_right uu____2992 box
              else mk_default () in
            let mk_nl box unbox nm op ts =
              let uu____3051 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____3051
              then
                let uu____3054 = binary unbox ts in
                match uu____3054 with
                | (t1, t2) ->
                    let uu____3061 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____3061 box
              else
                (let uu____3067 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____3067
                 then
                   let uu____3070 =
                     let uu____3071 = binary unbox ts in op uu____3071 in
                   FStar_All.pipe_right uu____3070 box
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
            let uu____3506 =
              let uu____3516 =
                FStar_List.tryFind
                  (fun uu____3540 ->
                     match uu____3540 with
                     | (l, uu____3551) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____3516 FStar_Util.must in
            (match uu____3506 with
             | (uu____3595, op) ->
                 let uu____3607 = op arg_tms in (uu____3607, decls))
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
        let uu____3623 = FStar_List.hd args_e in
        match uu____3623 with
        | (tm_sz, uu____3639) ->
            let uu____3648 = uu____3623 in
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz) in
            let sz_decls =
              let t_decls1 = FStar_SMTEncoding_Term.mkBvConstructor sz in
              FStar_SMTEncoding_Term.mk_decls "" sz_key t_decls1 [] in
            let uu____3659 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar fv,
                 uu____3685::(sz_arg, uu____3687)::uu____3688::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____3755 =
                    let uu____3756 = FStar_List.tail args_e in
                    FStar_List.tail uu____3756 in
                  let uu____3783 =
                    let uu____3787 = getInteger sz_arg.FStar_Syntax_Syntax.n in
                    FStar_Pervasives_Native.Some uu____3787 in
                  (uu____3755, uu____3783)
              | (FStar_Syntax_Syntax.Tm_fvar fv,
                 uu____3794::(sz_arg, uu____3796)::uu____3797::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____3864 =
                    let uu____3866 = FStar_Syntax_Print.term_to_string sz_arg in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____3866 in
                  failwith uu____3864
              | uu____3876 ->
                  let uu____3891 = FStar_List.tail args_e in
                  (uu____3891, FStar_Pervasives_Native.None) in
            (match uu____3659 with
             | (arg_tms, ext_sz) ->
                 let uu____3918 = encode_args arg_tms env in
                 (match uu____3918 with
                  | (arg_tms1, decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____3939 -> failwith "Impossible" in
                      let unary arg_tms2 =
                        let uu____3951 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____3951 in
                      let unary_arith arg_tms2 =
                        let uu____3962 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxInt uu____3962 in
                      let binary arg_tms2 =
                        let uu____3977 =
                          let uu____3978 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3978 in
                        let uu____3979 =
                          let uu____3980 =
                            let uu____3981 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____3981 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3980 in
                        (uu____3977, uu____3979) in
                      let binary_arith arg_tms2 =
                        let uu____3998 =
                          let uu____3999 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3999 in
                        let uu____4000 =
                          let uu____4001 =
                            let uu____4002 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____4002 in
                          FStar_SMTEncoding_Term.unboxInt uu____4001 in
                        (uu____3998, uu____4000) in
                      let mk_bv op mk_args resBox ts =
                        let uu____4060 =
                          let uu____4061 = mk_args ts in op uu____4061 in
                        FStar_All.pipe_right uu____4060 resBox in
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
                        let uu____4193 =
                          let uu____4198 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None ->
                                failwith "impossible" in
                          FStar_SMTEncoding_Util.mkBvUext uu____4198 in
                        let uu____4207 =
                          let uu____4212 =
                            let uu____4214 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None ->
                                  failwith "impossible" in
                            sz + uu____4214 in
                          FStar_SMTEncoding_Term.boxBitVec uu____4212 in
                        mk_bv uu____4193 unary uu____4207 arg_tms2 in
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
                      let uu____4454 =
                        let uu____4464 =
                          FStar_List.tryFind
                            (fun uu____4488 ->
                               match uu____4488 with
                               | (l, uu____4499) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops in
                        FStar_All.pipe_right uu____4464 FStar_Util.must in
                      (match uu____4454 with
                       | (uu____4545, op) ->
                           let uu____4557 = op arg_tms1 in
                           (uu____4557, (FStar_List.append sz_decls decls)))))
and (encode_deeply_embedded_quantifier :
  FStar_Syntax_Syntax.term ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t ->
    fun env ->
      let env1 =
        let uu___587_4567 = env in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___587_4567.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___587_4567.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___587_4567.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___587_4567.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___587_4567.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___587_4567.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name =
            (uu___587_4567.FStar_SMTEncoding_Env.use_zfuel_name);
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___587_4567.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___587_4567.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier = true;
          FStar_SMTEncoding_Env.global_cache =
            (uu___587_4567.FStar_SMTEncoding_Env.global_cache)
        } in
      let uu____4569 = encode_term t env1 in
      match uu____4569 with
      | (tm, decls) ->
          let vars = FStar_SMTEncoding_Term.free_variables tm in
          let valid_tm = FStar_SMTEncoding_Term.mk_Valid tm in
          let key =
            FStar_SMTEncoding_Term.mkForall t.FStar_Syntax_Syntax.pos
              ([], vars, valid_tm) in
          let tkey_hash = FStar_SMTEncoding_Term.hash_of_term key in
          (match tm.FStar_SMTEncoding_Term.tm with
           | FStar_SMTEncoding_Term.App
               (uu____4595,
                {
                  FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV
                    uu____4596;
                  FStar_SMTEncoding_Term.freevars = uu____4597;
                  FStar_SMTEncoding_Term.rng = uu____4598;_}::{
                                                                FStar_SMTEncoding_Term.tm
                                                                  =
                                                                  FStar_SMTEncoding_Term.FreeV
                                                                  uu____4599;
                                                                FStar_SMTEncoding_Term.freevars
                                                                  =
                                                                  uu____4600;
                                                                FStar_SMTEncoding_Term.rng
                                                                  =
                                                                  uu____4601;_}::[])
               ->
               (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                  (FStar_Errors.Warning_QuantifierWithoutPattern,
                    "Not encoding deeply embedded, unguarded quantifier to SMT");
                (tm, decls))
           | uu____4647 ->
               let uu____4648 = encode_formula t env1 in
               (match uu____4648 with
                | (phi, decls') ->
                    let interp =
                      match vars with
                      | [] ->
                          let uu____4668 =
                            let uu____4673 =
                              FStar_SMTEncoding_Term.mk_Valid tm in
                            (uu____4673, phi) in
                          FStar_SMTEncoding_Util.mkIff uu____4668
                      | uu____4674 ->
                          let uu____4675 =
                            let uu____4686 =
                              let uu____4687 =
                                let uu____4692 =
                                  FStar_SMTEncoding_Term.mk_Valid tm in
                                (uu____4692, phi) in
                              FStar_SMTEncoding_Util.mkIff uu____4687 in
                            ([[valid_tm]], vars, uu____4686) in
                          FStar_SMTEncoding_Term.mkForall
                            t.FStar_Syntax_Syntax.pos uu____4675 in
                    let ax =
                      let uu____4702 =
                        let uu____4710 =
                          let uu____4712 =
                            FStar_Util.digest_of_string tkey_hash in
                          Prims.op_Hat "l_quant_interp_" uu____4712 in
                        (interp,
                          (FStar_Pervasives_Native.Some
                             "Interpretation of deeply embedded quantifier"),
                          uu____4710) in
                      FStar_SMTEncoding_Util.mkAssume uu____4702 in
                    let uu____4718 =
                      let uu____4719 =
                        let uu____4722 =
                          FStar_SMTEncoding_Term.mk_decls "" tkey_hash 
                            [ax] (FStar_List.append decls decls') in
                        FStar_List.append decls' uu____4722 in
                      FStar_List.append decls uu____4719 in
                    (tm, uu____4718)))
and (encode_term :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t ->
    fun env ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____4734 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____4734
       then
         let uu____4739 = FStar_Syntax_Print.tag_of_term t in
         let uu____4741 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____4743 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____4739 uu____4741
           uu____4743
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____4752 ->
           let uu____4775 =
             let uu____4777 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____4780 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____4782 = FStar_Syntax_Print.term_to_string t0 in
             let uu____4784 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____4777
               uu____4780 uu____4782 uu____4784 in
           failwith uu____4775
       | FStar_Syntax_Syntax.Tm_unknown ->
           let uu____4791 =
             let uu____4793 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____4796 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____4798 = FStar_Syntax_Print.term_to_string t0 in
             let uu____4800 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____4793
               uu____4796 uu____4798 uu____4800 in
           failwith uu____4791
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let e = FStar_Syntax_Util.unfold_lazy i in
           ((let uu____4810 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding") in
             if uu____4810
             then
               let uu____4815 = FStar_Syntax_Print.term_to_string t0 in
               let uu____4817 = FStar_Syntax_Print.term_to_string e in
               FStar_Util.print2 ">> Unfolded (%s) ~> (%s)\n" uu____4815
                 uu____4817
             else ());
            encode_term e env)
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____4823 =
             let uu____4825 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____4825 in
           failwith uu____4823
       | FStar_Syntax_Syntax.Tm_ascribed (t1, (k, uu____4834), uu____4835) ->
           let uu____4884 =
             match k with
             | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
             | uu____4894 -> false in
           if uu____4884
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t1 env
       | FStar_Syntax_Syntax.Tm_quoted (qt, uu____4912) ->
           let tv =
             let uu____4918 =
               let uu____4925 = FStar_Reflection_Basic.inspect_ln qt in
               FStar_Syntax_Embeddings.embed
                 FStar_Reflection_Embeddings.e_term_view uu____4925 in
             uu____4918 t.FStar_Syntax_Syntax.pos
               FStar_Pervasives_Native.None
               FStar_Syntax_Embeddings.id_norm_cb in
           ((let uu____4929 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding") in
             if uu____4929
             then
               let uu____4934 = FStar_Syntax_Print.term_to_string t0 in
               let uu____4936 = FStar_Syntax_Print.term_to_string tv in
               FStar_Util.print2 ">> Inspected (%s) ~> (%s)\n" uu____4934
                 uu____4936
             else ());
            (let t1 =
               let uu____4944 =
                 let uu____4955 = FStar_Syntax_Syntax.as_arg tv in
                 [uu____4955] in
               FStar_Syntax_Util.mk_app
                 (FStar_Reflection_Data.refl_constant_term
                    FStar_Reflection_Data.fstar_refl_pack_ln) uu____4944 in
             encode_term t1 env))
       | FStar_Syntax_Syntax.Tm_meta
           (t1, FStar_Syntax_Syntax.Meta_pattern uu____4981) ->
           encode_term t1
             (let uu___659_5007 = env in
              {
                FStar_SMTEncoding_Env.bvar_bindings =
                  (uu___659_5007.FStar_SMTEncoding_Env.bvar_bindings);
                FStar_SMTEncoding_Env.fvar_bindings =
                  (uu___659_5007.FStar_SMTEncoding_Env.fvar_bindings);
                FStar_SMTEncoding_Env.depth =
                  (uu___659_5007.FStar_SMTEncoding_Env.depth);
                FStar_SMTEncoding_Env.tcenv =
                  (uu___659_5007.FStar_SMTEncoding_Env.tcenv);
                FStar_SMTEncoding_Env.warn =
                  (uu___659_5007.FStar_SMTEncoding_Env.warn);
                FStar_SMTEncoding_Env.nolabels =
                  (uu___659_5007.FStar_SMTEncoding_Env.nolabels);
                FStar_SMTEncoding_Env.use_zfuel_name =
                  (uu___659_5007.FStar_SMTEncoding_Env.use_zfuel_name);
                FStar_SMTEncoding_Env.encode_non_total_function_typ =
                  (uu___659_5007.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                FStar_SMTEncoding_Env.current_module_name =
                  (uu___659_5007.FStar_SMTEncoding_Env.current_module_name);
                FStar_SMTEncoding_Env.encoding_quantifier = false;
                FStar_SMTEncoding_Env.global_cache =
                  (uu___659_5007.FStar_SMTEncoding_Env.global_cache)
              })
       | FStar_Syntax_Syntax.Tm_meta (t1, uu____5010) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = FStar_SMTEncoding_Env.lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____5018 = head_redex env t in
           if uu____5018
           then let uu____5025 = whnf env t in encode_term uu____5025 env
           else
             (let fvb =
                FStar_SMTEncoding_Env.lookup_free_var_name env
                  v1.FStar_Syntax_Syntax.fv_name in
              let tok =
                FStar_SMTEncoding_Env.lookup_free_var env
                  v1.FStar_Syntax_Syntax.fv_name in
              let tkey_hash = FStar_SMTEncoding_Term.hash_of_term tok in
              let uu____5032 =
                if
                  fvb.FStar_SMTEncoding_Env.smt_arity > (Prims.parse_int "0")
                then
                  match tok.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.FreeV uu____5056 ->
                      let sym_name =
                        let uu____5067 =
                          FStar_Util.digest_of_string tkey_hash in
                        Prims.op_Hat "@kick_partial_app_" uu____5067 in
                      let uu____5070 =
                        let uu____5073 =
                          let uu____5074 =
                            let uu____5082 =
                              FStar_SMTEncoding_Term.kick_partial_app tok in
                            (uu____5082,
                              (FStar_Pervasives_Native.Some
                                 "kick_partial_app"), sym_name) in
                          FStar_SMTEncoding_Util.mkAssume uu____5074 in
                        [uu____5073] in
                      (uu____5070, sym_name)
                  | FStar_SMTEncoding_Term.App (uu____5089, []) ->
                      let sym_name =
                        let uu____5094 =
                          FStar_Util.digest_of_string tkey_hash in
                        Prims.op_Hat "@kick_partial_app_" uu____5094 in
                      let uu____5097 =
                        let uu____5100 =
                          let uu____5101 =
                            let uu____5109 =
                              FStar_SMTEncoding_Term.kick_partial_app tok in
                            (uu____5109,
                              (FStar_Pervasives_Native.Some
                                 "kick_partial_app"), sym_name) in
                          FStar_SMTEncoding_Util.mkAssume uu____5101 in
                        [uu____5100] in
                      (uu____5097, sym_name)
                  | uu____5116 -> ([], "")
                else ([], "") in
              match uu____5032 with
              | (aux_decls, sym_name) ->
                  let uu____5139 =
                    if aux_decls = []
                    then
                      FStar_All.pipe_right []
                        FStar_SMTEncoding_Term.mk_decls_trivial
                    else
                      FStar_SMTEncoding_Term.mk_decls sym_name tkey_hash
                        aux_decls [] in
                  (tok, uu____5139))
       | FStar_Syntax_Syntax.Tm_type uu____5147 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1, uu____5149) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders, c) ->
           let module_name = env.FStar_SMTEncoding_Env.current_module_name in
           let uu____5179 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____5179 with
            | (binders1, res) ->
                let uu____5190 =
                  (env.FStar_SMTEncoding_Env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____5190
                then
                  let uu____5197 =
                    encode_binders FStar_Pervasives_Native.None binders1 env in
                  (match uu____5197 with
                   | (vars, guards_l, env', decls, uu____5222) ->
                       let fsym =
                         let uu____5236 =
                           let uu____5242 =
                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                               module_name "f" in
                           (uu____5242, FStar_SMTEncoding_Term.Term_sort) in
                         FStar_SMTEncoding_Term.mk_fv uu____5236 in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____5248 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___713_5257 =
                              env.FStar_SMTEncoding_Env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___713_5257.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___713_5257.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___713_5257.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___713_5257.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___713_5257.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___713_5257.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___713_5257.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___713_5257.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___713_5257.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___713_5257.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___713_5257.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___713_5257.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___713_5257.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___713_5257.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___713_5257.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___713_5257.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___713_5257.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___713_5257.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___713_5257.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___713_5257.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___713_5257.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___713_5257.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___713_5257.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___713_5257.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___713_5257.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___713_5257.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___713_5257.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___713_5257.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___713_5257.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___713_5257.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___713_5257.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___713_5257.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___713_5257.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___713_5257.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___713_5257.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___713_5257.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___713_5257.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___713_5257.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___713_5257.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___713_5257.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___713_5257.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___713_5257.FStar_TypeChecker_Env.nbe)
                            }) res in
                       (match uu____5248 with
                        | (pre_opt, res_t) ->
                            let uu____5269 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app in
                            (match uu____5269 with
                             | (res_pred, decls') ->
                                 let uu____5280 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None ->
                                       let uu____5293 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards_l in
                                       (uu____5293, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____5297 =
                                         encode_formula pre env' in
                                       (match uu____5297 with
                                        | (guard, decls0) ->
                                            let uu____5310 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards_l) in
                                            (uu____5310, decls0)) in
                                 (match uu____5280 with
                                  | (guards, guard_decls) ->
                                      let is_pure =
                                        let uu____5325 =
                                          FStar_All.pipe_right res
                                            (FStar_TypeChecker_Normalize.ghost_to_pure
                                               env.FStar_SMTEncoding_Env.tcenv) in
                                        FStar_All.pipe_right uu____5325
                                          FStar_Syntax_Util.is_pure_comp in
                                      let t_interp =
                                        let uu____5334 =
                                          let uu____5345 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards, res_pred) in
                                          ([[app]], vars, uu____5345) in
                                        FStar_SMTEncoding_Term.mkForall
                                          t.FStar_Syntax_Syntax.pos
                                          uu____5334 in
                                      let t_interp1 =
                                        let tot_fun_axioms =
                                          isTotFun_axioms
                                            t.FStar_Syntax_Syntax.pos f vars
                                            guards_l is_pure in
                                        FStar_SMTEncoding_Util.mkAnd
                                          (t_interp, tot_fun_axioms) in
                                      let cvars =
                                        let uu____5367 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp1 in
                                        FStar_All.pipe_right uu____5367
                                          (FStar_List.filter
                                             (fun x ->
                                                let uu____5386 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    x in
                                                let uu____5388 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    fsym in
                                                uu____5386 <> uu____5388)) in
                                      let tkey =
                                        FStar_SMTEncoding_Term.mkForall
                                          t.FStar_Syntax_Syntax.pos
                                          ([], (fsym :: cvars), t_interp1) in
                                      let prefix1 =
                                        if is_pure
                                        then "Tm_arrow_"
                                        else "Tm_ghost_arrow_" in
                                      let tkey_hash =
                                        let uu____5416 =
                                          FStar_SMTEncoding_Term.hash_of_term
                                            tkey in
                                        Prims.op_Hat prefix1 uu____5416 in
                                      let tsym =
                                        let uu____5420 =
                                          FStar_Util.digest_of_string
                                            tkey_hash in
                                        Prims.op_Hat prefix1 uu____5420 in
                                      let cvar_sorts =
                                        FStar_List.map
                                          FStar_SMTEncoding_Term.fv_sort
                                          cvars in
                                      let caption =
                                        let uu____5434 =
                                          FStar_Options.log_queries () in
                                        if uu____5434
                                        then
                                          let uu____5437 =
                                            let uu____5439 =
                                              FStar_TypeChecker_Normalize.term_to_string
                                                env.FStar_SMTEncoding_Env.tcenv
                                                t0 in
                                            FStar_Util.replace_char
                                              uu____5439 10 32 in
                                          FStar_Pervasives_Native.Some
                                            uu____5437
                                        else FStar_Pervasives_Native.None in
                                      let tdecl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (tsym, cvar_sorts,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            caption) in
                                      let t1 =
                                        let uu____5452 =
                                          let uu____5460 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              cvars in
                                          (tsym, uu____5460) in
                                        FStar_SMTEncoding_Util.mkApp
                                          uu____5452 in
                                      let t_has_kind =
                                        FStar_SMTEncoding_Term.mk_HasType t1
                                          FStar_SMTEncoding_Term.mk_Term_type in
                                      let k_assumption =
                                        let a_name =
                                          Prims.op_Hat "kinding_" tsym in
                                        let uu____5479 =
                                          let uu____5487 =
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              ([[t_has_kind]], cvars,
                                                t_has_kind) in
                                          (uu____5487,
                                            (FStar_Pervasives_Native.Some
                                               a_name), a_name) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____5479 in
                                      let f_has_t =
                                        FStar_SMTEncoding_Term.mk_HasType f
                                          t1 in
                                      let f_has_t_z =
                                        FStar_SMTEncoding_Term.mk_HasTypeZ f
                                          t1 in
                                      let pre_typing =
                                        let a_name =
                                          Prims.op_Hat "pre_typing_" tsym in
                                        let uu____5504 =
                                          let uu____5512 =
                                            let uu____5513 =
                                              let uu____5524 =
                                                let uu____5525 =
                                                  let uu____5530 =
                                                    let uu____5531 =
                                                      FStar_SMTEncoding_Term.mk_PreType
                                                        f in
                                                    FStar_SMTEncoding_Term.mk_tester
                                                      "Tm_arrow" uu____5531 in
                                                  (f_has_t, uu____5530) in
                                                FStar_SMTEncoding_Util.mkImp
                                                  uu____5525 in
                                              ([[f_has_t]], (fsym :: cvars),
                                                uu____5524) in
                                            let uu____5549 =
                                              mkForall_fuel module_name
                                                t0.FStar_Syntax_Syntax.pos in
                                            uu____5549 uu____5513 in
                                          (uu____5512,
                                            (FStar_Pervasives_Native.Some
                                               "pre-typing for functions"),
                                            (Prims.op_Hat module_name
                                               (Prims.op_Hat "_" a_name))) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____5504 in
                                      let t_interp2 =
                                        let a_name =
                                          Prims.op_Hat "interpretation_" tsym in
                                        let uu____5572 =
                                          let uu____5580 =
                                            let uu____5581 =
                                              let uu____5592 =
                                                FStar_SMTEncoding_Util.mkIff
                                                  (f_has_t_z, t_interp1) in
                                              ([[f_has_t_z]], (fsym ::
                                                cvars), uu____5592) in
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              uu____5581 in
                                          (uu____5580,
                                            (FStar_Pervasives_Native.Some
                                               a_name),
                                            (Prims.op_Hat module_name
                                               (Prims.op_Hat "_" a_name))) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____5572 in
                                      let t_decls1 =
                                        [tdecl;
                                        k_assumption;
                                        pre_typing;
                                        t_interp2] in
                                      let uu____5615 =
                                        let uu____5616 =
                                          let uu____5619 =
                                            let uu____5622 =
                                              FStar_SMTEncoding_Term.mk_decls
                                                tsym tkey_hash t_decls1
                                                (FStar_List.append decls
                                                   (FStar_List.append decls'
                                                      guard_decls)) in
                                            FStar_List.append guard_decls
                                              uu____5622 in
                                          FStar_List.append decls' uu____5619 in
                                        FStar_List.append decls uu____5616 in
                                      (t1, uu____5615)))))
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
                     let uu____5643 =
                       let uu____5651 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____5651,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"), a_name) in
                     FStar_SMTEncoding_Util.mkAssume uu____5643 in
                   let fsym =
                     FStar_SMTEncoding_Term.mk_fv
                       ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.op_Hat "pre_typing_" tsym in
                     let uu____5664 =
                       let uu____5672 =
                         let uu____5673 =
                           let uu____5684 =
                             let uu____5685 =
                               let uu____5690 =
                                 let uu____5691 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____5691 in
                               (f_has_t, uu____5690) in
                             FStar_SMTEncoding_Util.mkImp uu____5685 in
                           ([[f_has_t]], [fsym], uu____5684) in
                         let uu____5717 =
                           mkForall_fuel module_name
                             t0.FStar_Syntax_Syntax.pos in
                         uu____5717 uu____5673 in
                       (uu____5672, (FStar_Pervasives_Native.Some a_name),
                         a_name) in
                     FStar_SMTEncoding_Util.mkAssume uu____5664 in
                   let uu____5734 =
                     FStar_All.pipe_right [tdecl; t_kinding; t_interp]
                       FStar_SMTEncoding_Term.mk_decls_trivial in
                   (t1, uu____5734)))
       | FStar_Syntax_Syntax.Tm_refine uu____5737 ->
           let uu____5744 =
             let steps =
               [FStar_TypeChecker_Env.Weak;
               FStar_TypeChecker_Env.HNF;
               FStar_TypeChecker_Env.EraseUniverses] in
             let uu____5754 =
               FStar_TypeChecker_Normalize.normalize_refinement steps
                 env.FStar_SMTEncoding_Env.tcenv t0 in
             match uu____5754 with
             | {
                 FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f);
                 FStar_Syntax_Syntax.pos = uu____5763;
                 FStar_Syntax_Syntax.vars = uu____5764;_} ->
                 let uu____5771 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f in
                 (match uu____5771 with
                  | (b, f1) ->
                      let uu____5798 =
                        let uu____5799 = FStar_List.hd b in
                        FStar_Pervasives_Native.fst uu____5799 in
                      (uu____5798, f1))
             | uu____5816 -> failwith "impossible" in
           (match uu____5744 with
            | (x, f) ->
                let uu____5834 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____5834 with
                 | (base_t, decls) ->
                     let uu____5845 =
                       FStar_SMTEncoding_Env.gen_term_var env x in
                     (match uu____5845 with
                      | (x1, xtm, env') ->
                          let uu____5862 = encode_formula f env' in
                          (match uu____5862 with
                           | (refinement, decls') ->
                               let uu____5873 =
                                 FStar_SMTEncoding_Env.fresh_fvar
                                   env.FStar_SMTEncoding_Env.current_module_name
                                   "f" FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____5873 with
                                | (fsym, fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____5901 =
                                        let uu____5912 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____5923 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____5912
                                          uu____5923 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____5901 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun y ->
                                              (let uu____5977 =
                                                 FStar_SMTEncoding_Term.fv_name
                                                   y in
                                               uu____5977 <> x1) &&
                                                (let uu____5981 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     y in
                                                 uu____5981 <> fsym))) in
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
                                    ((let uu____6014 =
                                        FStar_TypeChecker_Env.debug
                                          env.FStar_SMTEncoding_Env.tcenv
                                          (FStar_Options.Other "SMTEncoding") in
                                      if uu____6014
                                      then
                                        let uu____6018 =
                                          FStar_Syntax_Print.term_to_string f in
                                        let uu____6020 =
                                          FStar_Util.digest_of_string
                                            tkey_hash in
                                        FStar_Util.print3
                                          "Encoding Tm_refine %s with tkey_hash %s and digest %s\n"
                                          uu____6018 tkey_hash uu____6020
                                      else ());
                                     (let tsym =
                                        let uu____6027 =
                                          FStar_Util.digest_of_string
                                            tkey_hash in
                                        Prims.op_Hat "Tm_refine_" uu____6027 in
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
                                        let uu____6047 =
                                          let uu____6055 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              cvars1 in
                                          (tsym, uu____6055) in
                                        FStar_SMTEncoding_Util.mkApp
                                          uu____6047 in
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
                                        let uu____6075 =
                                          let uu____6083 =
                                            let uu____6084 =
                                              let uu____6095 =
                                                FStar_SMTEncoding_Util.mkIff
                                                  (t_haseq_ref, t_haseq_base) in
                                              ([[t_haseq_ref]], cvars1,
                                                uu____6095) in
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              uu____6084 in
                                          (uu____6083,
                                            (FStar_Pervasives_Native.Some
                                               (Prims.op_Hat "haseq for "
                                                  tsym)),
                                            (Prims.op_Hat "haseq" tsym)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____6075 in
                                      let t_kinding =
                                        let uu____6109 =
                                          let uu____6117 =
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              ([[t_has_kind]], cvars1,
                                                t_has_kind) in
                                          (uu____6117,
                                            (FStar_Pervasives_Native.Some
                                               "refinement kinding"),
                                            (Prims.op_Hat
                                               "refinement_kinding_" tsym)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____6109 in
                                      let t_interp =
                                        let uu____6131 =
                                          let uu____6139 =
                                            let uu____6140 =
                                              let uu____6151 =
                                                FStar_SMTEncoding_Util.mkIff
                                                  (x_has_t, encoding) in
                                              ([[x_has_t]], (ffv :: xfv ::
                                                cvars1), uu____6151) in
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              uu____6140 in
                                          (uu____6139,
                                            (FStar_Pervasives_Native.Some
                                               "refinement_interpretation"),
                                            (Prims.op_Hat
                                               "refinement_interpretation_"
                                               tsym)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____6131 in
                                      let t_decls1 =
                                        [tdecl;
                                        t_kinding;
                                        t_interp;
                                        t_haseq1] in
                                      let uu____6183 =
                                        let uu____6184 =
                                          let uu____6187 =
                                            FStar_SMTEncoding_Term.mk_decls
                                              tsym tkey_hash t_decls1
                                              (FStar_List.append decls decls') in
                                          FStar_List.append decls' uu____6187 in
                                        FStar_List.append decls uu____6184 in
                                      (t1, uu____6183))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv, uu____6191) ->
           let ttm =
             let uu____6209 =
               FStar_Syntax_Unionfind.uvar_id
                 uv.FStar_Syntax_Syntax.ctx_uvar_head in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____6209 in
           let uu____6211 =
             encode_term_pred FStar_Pervasives_Native.None
               uv.FStar_Syntax_Syntax.ctx_uvar_typ env ttm in
           (match uu____6211 with
            | (t_has_k, decls) ->
                let d =
                  let uu____6223 =
                    let uu____6231 =
                      let uu____6233 =
                        let uu____6235 =
                          let uu____6237 =
                            FStar_Syntax_Unionfind.uvar_id
                              uv.FStar_Syntax_Syntax.ctx_uvar_head in
                          FStar_Util.string_of_int uu____6237 in
                        FStar_Util.format1 "uvar_typing_%s" uu____6235 in
                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                        uu____6233 in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____6231) in
                  FStar_SMTEncoding_Util.mkAssume uu____6223 in
                let uu____6243 =
                  let uu____6244 =
                    FStar_All.pipe_right [d]
                      FStar_SMTEncoding_Term.mk_decls_trivial in
                  FStar_List.append decls uu____6244 in
                (ttm, uu____6243))
       | FStar_Syntax_Syntax.Tm_app uu____6251 ->
           let uu____6268 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____6268 with
            | (head1, args_e) ->
                let uu____6315 =
                  let uu____6330 =
                    let uu____6331 = FStar_Syntax_Subst.compress head1 in
                    uu____6331.FStar_Syntax_Syntax.n in
                  (uu____6330, args_e) in
                (match uu____6315 with
                 | uu____6348 when head_redex env head1 ->
                     let uu____6363 = whnf env t in
                     encode_term uu____6363 env
                 | uu____6364 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____6387 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_fvar fv, uu____6405) when
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
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____6427;
                       FStar_Syntax_Syntax.vars = uu____6428;_},
                     uu____6429),
                    uu____6430) when
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
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____6456;
                       FStar_Syntax_Syntax.vars = uu____6457;_},
                     uu____6458),
                    (v0, uu____6460)::(v1, uu____6462)::(v2, uu____6464)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____6535 = encode_term v0 env in
                     (match uu____6535 with
                      | (v01, decls0) ->
                          let uu____6546 = encode_term v1 env in
                          (match uu____6546 with
                           | (v11, decls1) ->
                               let uu____6557 = encode_term v2 env in
                               (match uu____6557 with
                                | (v21, decls2) ->
                                    let uu____6568 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21 in
                                    (uu____6568,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_fvar fv,
                    (v0, uu____6571)::(v1, uu____6573)::(v2, uu____6575)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____6642 = encode_term v0 env in
                     (match uu____6642 with
                      | (v01, decls0) ->
                          let uu____6653 = encode_term v1 env in
                          (match uu____6653 with
                           | (v11, decls1) ->
                               let uu____6664 = encode_term v2 env in
                               (match uu____6664 with
                                | (v21, decls2) ->
                                    let uu____6675 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21 in
                                    (uu____6675,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of), (arg, uu____6677)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of),
                    (arg, uu____6713)::(rng, uu____6715)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify), uu____6766) ->
                     let e0 =
                       let uu____6788 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg
                         env.FStar_SMTEncoding_Env.tcenv head1 uu____6788 in
                     ((let uu____6798 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug
                              env.FStar_SMTEncoding_Env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____6798
                       then
                         let uu____6803 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____6803
                       else ());
                      (let e =
                         let uu____6811 =
                           let uu____6816 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____6817 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____6816
                             uu____6817 in
                         uu____6811 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect uu____6826),
                    (arg, uu____6828)::[]) -> encode_term arg env
                 | uu____6863 ->
                     let uu____6878 = encode_args args_e env in
                     (match uu____6878 with
                      | (args, decls) ->
                          let encode_partial_app ht_opt =
                            let uu____6947 = encode_term head1 env in
                            match uu____6947 with
                            | (smt_head, decls') ->
                                let app_tm = mk_Apply_args smt_head args in
                                (match ht_opt with
                                 | uu____6967 ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some
                                     (head_type, formals, c) ->
                                     ((let uu____7036 =
                                         FStar_TypeChecker_Env.debug
                                           env.FStar_SMTEncoding_Env.tcenv
                                           (FStar_Options.Other "PartialApp") in
                                       if uu____7036
                                       then
                                         let uu____7040 =
                                           FStar_Syntax_Print.term_to_string
                                             head1 in
                                         let uu____7042 =
                                           FStar_Syntax_Print.term_to_string
                                             head_type in
                                         let uu____7044 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", " formals in
                                         let uu____7047 =
                                           FStar_Syntax_Print.comp_to_string
                                             c in
                                         let uu____7049 =
                                           FStar_Syntax_Print.args_to_string
                                             args_e in
                                         FStar_Util.print5
                                           "Encoding partial application:\n\thead=%s\n\thead_type=%s\n\tformals=%s\n\tcomp=%s\n\tactual args=%s\n"
                                           uu____7040 uu____7042 uu____7044
                                           uu____7047 uu____7049
                                       else ());
                                      (let uu____7054 =
                                         FStar_Util.first_N
                                           (FStar_List.length args_e) formals in
                                       match uu____7054 with
                                       | (formals1, rest) ->
                                           let subst1 =
                                             FStar_List.map2
                                               (fun uu____7152 ->
                                                  fun uu____7153 ->
                                                    match (uu____7152,
                                                            uu____7153)
                                                    with
                                                    | ((bv, uu____7183),
                                                       (a, uu____7185)) ->
                                                        FStar_Syntax_Syntax.NT
                                                          (bv, a)) formals1
                                               args_e in
                                           let ty =
                                             let uu____7217 =
                                               FStar_Syntax_Util.arrow rest c in
                                             FStar_All.pipe_right uu____7217
                                               (FStar_Syntax_Subst.subst
                                                  subst1) in
                                           ((let uu____7221 =
                                               FStar_TypeChecker_Env.debug
                                                 env.FStar_SMTEncoding_Env.tcenv
                                                 (FStar_Options.Other
                                                    "PartialApp") in
                                             if uu____7221
                                             then
                                               let uu____7225 =
                                                 FStar_Syntax_Print.term_to_string
                                                   ty in
                                               FStar_Util.print1
                                                 "Encoding partial application, after subst:\n\tty=%s\n"
                                                 uu____7225
                                             else ());
                                            (let uu____7230 =
                                               let uu____7243 =
                                                 FStar_List.fold_left2
                                                   (fun uu____7278 ->
                                                      fun uu____7279 ->
                                                        fun e ->
                                                          match (uu____7278,
                                                                  uu____7279)
                                                          with
                                                          | ((t_hyps, decls1),
                                                             (bv, uu____7320))
                                                              ->
                                                              let t1 =
                                                                FStar_Syntax_Subst.subst
                                                                  subst1
                                                                  bv.FStar_Syntax_Syntax.sort in
                                                              let uu____7348
                                                                =
                                                                encode_term_pred
                                                                  FStar_Pervasives_Native.None
                                                                  t1 env e in
                                                              (match uu____7348
                                                               with
                                                               | (t_hyp,
                                                                  decls'1) ->
                                                                   ((
                                                                    let uu____7364
                                                                    =
                                                                    FStar_TypeChecker_Env.debug
                                                                    env.FStar_SMTEncoding_Env.tcenv
                                                                    (FStar_Options.Other
                                                                    "PartialApp") in
                                                                    if
                                                                    uu____7364
                                                                    then
                                                                    let uu____7368
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1 in
                                                                    let uu____7370
                                                                    =
                                                                    FStar_SMTEncoding_Term.print_smt_term
                                                                    t_hyp in
                                                                    FStar_Util.print2
                                                                    "Encoded typing hypothesis for %s ... got %s\n"
                                                                    uu____7368
                                                                    uu____7370
                                                                    else ());
                                                                    ((t_hyp
                                                                    ::
                                                                    t_hyps),
                                                                    (FStar_List.append
                                                                    decls1
                                                                    decls'1)))))
                                                   ([], []) formals1 args in
                                               match uu____7243 with
                                               | (t_hyps, decls1) ->
                                                   let uu____7405 =
                                                     match smt_head.FStar_SMTEncoding_Term.tm
                                                     with
                                                     | FStar_SMTEncoding_Term.FreeV
                                                         uu____7414 ->
                                                         encode_term_pred
                                                           FStar_Pervasives_Native.None
                                                           head_type env
                                                           smt_head
                                                     | uu____7423 ->
                                                         (FStar_SMTEncoding_Util.mkTrue,
                                                           []) in
                                                   (match uu____7405 with
                                                    | (t_head_hyp, decls'1)
                                                        ->
                                                        let hyp =
                                                          FStar_SMTEncoding_Term.mk_and_l
                                                            (t_head_hyp ::
                                                            t_hyps)
                                                            FStar_Range.dummyRange in
                                                        let uu____7439 =
                                                          encode_term_pred
                                                            FStar_Pervasives_Native.None
                                                            ty env app_tm in
                                                        (match uu____7439
                                                         with
                                                         | (has_type_conclusion,
                                                            decls'') ->
                                                             let has_type =
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
                                                             let uu____7461 =
                                                               let uu____7468
                                                                 =
                                                                 FStar_SMTEncoding_Term.fvs_subset_of
                                                                   cvars
                                                                   app_tm_vars in
                                                               if uu____7468
                                                               then
                                                                 ([app_tm],
                                                                   app_tm_vars)
                                                               else
                                                                 (let uu____7481
                                                                    =
                                                                    let uu____7483
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    has_type_conclusion in
                                                                    FStar_SMTEncoding_Term.fvs_subset_of
                                                                    cvars
                                                                    uu____7483 in
                                                                  if
                                                                    uu____7481
                                                                  then
                                                                    ([has_type_conclusion],
                                                                    cvars)
                                                                  else
                                                                    (
                                                                    (
                                                                    let uu____7496
                                                                    =
                                                                    let uu____7502
                                                                    =
                                                                    let uu____7504
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t0 in
                                                                    FStar_Util.format1
                                                                    "No SMT pattern for partial application %s"
                                                                    uu____7504 in
                                                                    (FStar_Errors.Warning_SMTPatternIllFormed,
                                                                    uu____7502) in
                                                                    FStar_Errors.log_issue
                                                                    t0.FStar_Syntax_Syntax.pos
                                                                    uu____7496);
                                                                    ([],
                                                                    cvars))) in
                                                             (match uu____7461
                                                              with
                                                              | (pattern,
                                                                 vars) ->
                                                                  (vars,
                                                                    pattern,
                                                                    has_type,
                                                                    (
                                                                    FStar_List.append
                                                                    decls1
                                                                    (FStar_List.append
                                                                    decls'1
                                                                    decls'')))))) in
                                             match uu____7230 with
                                             | (vars, pattern, has_type,
                                                decls'') ->
                                                 ((let uu____7551 =
                                                     FStar_TypeChecker_Env.debug
                                                       env.FStar_SMTEncoding_Env.tcenv
                                                       (FStar_Options.Other
                                                          "PartialApp") in
                                                   if uu____7551
                                                   then
                                                     let uu____7555 =
                                                       FStar_SMTEncoding_Term.print_smt_term
                                                         has_type in
                                                     FStar_Util.print1
                                                       "Encoding partial application, after SMT encoded predicate:\n\t=%s\n"
                                                       uu____7555
                                                   else ());
                                                  (let tkey_hash =
                                                     FStar_SMTEncoding_Term.hash_of_term
                                                       app_tm in
                                                   let e_typing =
                                                     let uu____7563 =
                                                       let uu____7571 =
                                                         FStar_SMTEncoding_Term.mkForall
                                                           t0.FStar_Syntax_Syntax.pos
                                                           ([pattern], vars,
                                                             has_type) in
                                                       let uu____7580 =
                                                         let uu____7582 =
                                                           let uu____7584 =
                                                             FStar_SMTEncoding_Term.hash_of_term
                                                               app_tm in
                                                           FStar_Util.digest_of_string
                                                             uu____7584 in
                                                         Prims.op_Hat
                                                           "partial_app_typing_"
                                                           uu____7582 in
                                                       (uu____7571,
                                                         (FStar_Pervasives_Native.Some
                                                            "Partial app typing"),
                                                         uu____7580) in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____7563 in
                                                   let uu____7590 =
                                                     let uu____7593 =
                                                       let uu____7596 =
                                                         let uu____7599 =
                                                           FStar_SMTEncoding_Term.mk_decls
                                                             "" tkey_hash
                                                             [e_typing]
                                                             (FStar_List.append
                                                                decls
                                                                (FStar_List.append
                                                                   decls'
                                                                   decls'')) in
                                                         FStar_List.append
                                                           decls'' uu____7599 in
                                                       FStar_List.append
                                                         decls' uu____7596 in
                                                     FStar_List.append decls
                                                       uu____7593 in
                                                   (app_tm, uu____7590)))))))) in
                          let encode_full_app fv =
                            let uu____7619 =
                              FStar_SMTEncoding_Env.lookup_free_var_sym env
                                fv in
                            match uu____7619 with
                            | (fname, fuel_args, arity) ->
                                let tm =
                                  maybe_curry_app t0.FStar_Syntax_Syntax.pos
                                    fname arity
                                    (FStar_List.append fuel_args args) in
                                (tm, decls) in
                          let head2 = FStar_Syntax_Subst.compress head1 in
                          let head_type =
                            match head2.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_uinst
                                ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_name x;
                                   FStar_Syntax_Syntax.pos = uu____7662;
                                   FStar_Syntax_Syntax.vars = uu____7663;_},
                                 uu____7664)
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
                                   FStar_Syntax_Syntax.pos = uu____7671;
                                   FStar_Syntax_Syntax.vars = uu____7672;_},
                                 uu____7673)
                                ->
                                let uu____7678 =
                                  let uu____7679 =
                                    let uu____7684 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____7684
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____7679
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____7678
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____7714 =
                                  let uu____7715 =
                                    let uu____7720 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____7720
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____7715
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____7714
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____7749, (FStar_Util.Inl t1, uu____7751),
                                 uu____7752)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____7799, (FStar_Util.Inr c, uu____7801),
                                 uu____7802)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____7849 -> FStar_Pervasives_Native.None in
                          (match head_type with
                           | FStar_Pervasives_Native.None ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let uu____7873 =
                                 let head_type2 =
                                   let uu____7895 =
                                     FStar_TypeChecker_Normalize.normalize_refinement
                                       [FStar_TypeChecker_Env.Weak;
                                       FStar_TypeChecker_Env.HNF;
                                       FStar_TypeChecker_Env.EraseUniverses]
                                       env.FStar_SMTEncoding_Env.tcenv
                                       head_type1 in
                                   FStar_All.pipe_left
                                     FStar_Syntax_Util.unrefine uu____7895 in
                                 let uu____7898 =
                                   curried_arrow_formals_comp head_type2 in
                                 match uu____7898 with
                                 | (formals, c) ->
                                     if
                                       (FStar_List.length formals) <
                                         (FStar_List.length args)
                                     then
                                       let head_type3 =
                                         let uu____7949 =
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
                                           uu____7949 in
                                       let uu____7950 =
                                         curried_arrow_formals_comp
                                           head_type3 in
                                       (match uu____7950 with
                                        | (formals1, c1) ->
                                            (head_type3, formals1, c1))
                                     else (head_type2, formals, c) in
                               (match uu____7873 with
                                | (head_type2, formals, c) ->
                                    ((let uu____8033 =
                                        FStar_TypeChecker_Env.debug
                                          env.FStar_SMTEncoding_Env.tcenv
                                          (FStar_Options.Other "PartialApp") in
                                      if uu____8033
                                      then
                                        let uu____8037 =
                                          FStar_Syntax_Print.term_to_string
                                            head_type2 in
                                        let uu____8039 =
                                          FStar_Syntax_Print.binders_to_string
                                            ", " formals in
                                        let uu____8042 =
                                          FStar_Syntax_Print.args_to_string
                                            args_e in
                                        FStar_Util.print3
                                          "Encoding partial application, head_type = %s, formals = %s, args = %s\n"
                                          uu____8037 uu____8039 uu____8042
                                      else ());
                                     (match head2.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          ({
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_fvar fv;
                                             FStar_Syntax_Syntax.pos =
                                               uu____8052;
                                             FStar_Syntax_Syntax.vars =
                                               uu____8053;_},
                                           uu____8054)
                                          when
                                          (FStar_List.length formals) =
                                            (FStar_List.length args)
                                          ->
                                          encode_full_app
                                            fv.FStar_Syntax_Syntax.fv_name
                                      | FStar_Syntax_Syntax.Tm_fvar fv when
                                          (FStar_List.length formals) =
                                            (FStar_List.length args)
                                          ->
                                          encode_full_app
                                            fv.FStar_Syntax_Syntax.fv_name
                                      | uu____8072 ->
                                          if
                                            (FStar_List.length formals) >
                                              (FStar_List.length args)
                                          then
                                            encode_partial_app
                                              (FStar_Pervasives_Native.Some
                                                 (head_type2, formals, c))
                                          else
                                            encode_partial_app
                                              FStar_Pervasives_Native.None)))))))
       | FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) ->
           let uu____8161 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____8161 with
            | (bs1, body1, opening) ->
                let fallback uu____8184 =
                  let f =
                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                      env.FStar_SMTEncoding_Env.current_module_name "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding")) in
                  let uu____8194 =
                    let uu____8195 =
                      FStar_SMTEncoding_Term.mk_fv
                        (f, FStar_SMTEncoding_Term.Term_sort) in
                    FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV
                      uu____8195 in
                  let uu____8197 =
                    FStar_All.pipe_right [decl]
                      FStar_SMTEncoding_Term.mk_decls_trivial in
                  (uu____8194, uu____8197) in
                let is_impure rc =
                  let uu____8207 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                      env.FStar_SMTEncoding_Env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect in
                  FStar_All.pipe_right uu____8207 Prims.op_Negation in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None ->
                        let uu____8222 =
                          let uu____8235 =
                            FStar_TypeChecker_Env.get_range
                              env.FStar_SMTEncoding_Env.tcenv in
                          FStar_TypeChecker_Util.new_implicit_var
                            "SMTEncoding codomain" uu____8235
                            env.FStar_SMTEncoding_Env.tcenv
                            FStar_Syntax_Util.ktype0 in
                        (match uu____8222 with
                         | (t1, uu____8238, uu____8239) -> t1)
                    | FStar_Pervasives_Native.Some t1 -> t1 in
                  let uu____8257 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid in
                  if uu____8257
                  then
                    let uu____8262 = FStar_Syntax_Syntax.mk_Total res_typ in
                    FStar_Pervasives_Native.Some uu____8262
                  else
                    (let uu____8265 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid in
                     if uu____8265
                     then
                       let uu____8270 = FStar_Syntax_Syntax.mk_GTotal res_typ in
                       FStar_Pervasives_Native.Some uu____8270
                     else FStar_Pervasives_Native.None) in
                (match lopt with
                 | FStar_Pervasives_Native.None ->
                     ((let uu____8278 =
                         let uu____8284 =
                           let uu____8286 =
                             FStar_Syntax_Print.term_to_string t0 in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____8286 in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____8284) in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____8278);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8291 =
                       (is_impure rc) &&
                         (let uu____8294 =
                            FStar_TypeChecker_Env.is_reifiable_rc
                              env.FStar_SMTEncoding_Env.tcenv rc in
                          Prims.op_Negation uu____8294) in
                     if uu____8291
                     then fallback ()
                     else
                       (let uu____8303 =
                          encode_binders FStar_Pervasives_Native.None bs1 env in
                        match uu____8303 with
                        | (vars, guards, envbody, decls, uu____8328) ->
                            let body2 =
                              let uu____8342 =
                                FStar_TypeChecker_Env.is_reifiable_rc
                                  env.FStar_SMTEncoding_Env.tcenv rc in
                              if uu____8342
                              then
                                FStar_TypeChecker_Util.reify_body
                                  env.FStar_SMTEncoding_Env.tcenv body1
                              else body1 in
                            let uu____8347 = encode_term body2 envbody in
                            (match uu____8347 with
                             | (body3, decls') ->
                                 let is_pure =
                                   FStar_Syntax_Util.is_pure_effect
                                     rc.FStar_Syntax_Syntax.residual_effect in
                                 let uu____8360 =
                                   let uu____8369 = codomain_eff rc in
                                   match uu____8369 with
                                   | FStar_Pervasives_Native.None ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c in
                                       let uu____8388 = encode_term tfun env in
                                       (match uu____8388 with
                                        | (t1, decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1)) in
                                 (match uu____8360 with
                                  | (arrow_t_opt, decls'') ->
                                      let key_body =
                                        let uu____8422 =
                                          let uu____8433 =
                                            let uu____8434 =
                                              let uu____8439 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____8439, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8434 in
                                          ([], vars, uu____8433) in
                                        FStar_SMTEncoding_Term.mkForall
                                          t0.FStar_Syntax_Syntax.pos
                                          uu____8422 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let uu____8447 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None ->
                                            (cvars, key_body)
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____8463 =
                                              let uu____8466 =
                                                let uu____8477 =
                                                  FStar_SMTEncoding_Term.free_variables
                                                    t1 in
                                                FStar_List.append uu____8477
                                                  cvars in
                                              FStar_Util.remove_dups
                                                FStar_SMTEncoding_Term.fv_eq
                                                uu____8466 in
                                            let uu____8504 =
                                              FStar_SMTEncoding_Util.mkAnd
                                                (key_body, t1) in
                                            (uu____8463, uu____8504) in
                                      (match uu____8447 with
                                       | (cvars1, key_body1) ->
                                           let tkey =
                                             FStar_SMTEncoding_Term.mkForall
                                               t0.FStar_Syntax_Syntax.pos
                                               ([], cvars1, key_body1) in
                                           let tkey_hash =
                                             FStar_SMTEncoding_Term.hash_of_term
                                               tkey in
                                           ((let uu____8527 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env.FStar_SMTEncoding_Env.tcenv)
                                                 (FStar_Options.Other
                                                    "PartialApp") in
                                             if uu____8527
                                             then
                                               let uu____8532 =
                                                 let uu____8534 =
                                                   FStar_List.map
                                                     FStar_SMTEncoding_Term.fv_name
                                                     vars in
                                                 FStar_All.pipe_right
                                                   uu____8534
                                                   (FStar_String.concat ", ") in
                                               let uu____8544 =
                                                 FStar_SMTEncoding_Term.print_smt_term
                                                   body3 in
                                               FStar_Util.print2
                                                 "Checking eta expansion of\n\tvars={%s}\n\tbody=%s\n"
                                                 uu____8532 uu____8544
                                             else ());
                                            (let uu____8549 =
                                               is_an_eta_expansion env vars
                                                 body3 in
                                             match uu____8549 with
                                             | FStar_Pervasives_Native.Some
                                                 t1 ->
                                                 ((let uu____8558 =
                                                     FStar_All.pipe_left
                                                       (FStar_TypeChecker_Env.debug
                                                          env.FStar_SMTEncoding_Env.tcenv)
                                                       (FStar_Options.Other
                                                          "PartialApp") in
                                                   if uu____8558
                                                   then
                                                     let uu____8563 =
                                                       FStar_SMTEncoding_Term.print_smt_term
                                                         t1 in
                                                     FStar_Util.print1
                                                       "Yes, is an eta expansion of\n\tcore=%s\n"
                                                       uu____8563
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
                                                   let uu____8576 =
                                                     FStar_Util.digest_of_string
                                                       tkey_hash in
                                                   Prims.op_Hat "Tm_abs_"
                                                     uu____8576 in
                                                 let fdecl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (fsym, cvar_sorts,
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       FStar_Pervasives_Native.None) in
                                                 let f =
                                                   let uu____8585 =
                                                     let uu____8593 =
                                                       FStar_List.map
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                         cvars1 in
                                                     (fsym, uu____8593) in
                                                   FStar_SMTEncoding_Util.mkApp
                                                     uu____8585 in
                                                 let app = mk_Apply f vars in
                                                 let typing_f =
                                                   match arrow_t_opt with
                                                   | FStar_Pervasives_Native.None
                                                       ->
                                                       let tot_fun_ax =
                                                         let ax =
                                                           let uu____8607 =
                                                             FStar_All.pipe_right
                                                               vars
                                                               (FStar_List.map
                                                                  (fun
                                                                    uu____8615
                                                                    ->
                                                                    FStar_SMTEncoding_Util.mkTrue)) in
                                                           isTotFun_axioms
                                                             t0.FStar_Syntax_Syntax.pos
                                                             f vars
                                                             uu____8607
                                                             is_pure in
                                                         match cvars1 with
                                                         | [] -> ax
                                                         | uu____8616 ->
                                                             FStar_SMTEncoding_Term.mkForall
                                                               t0.FStar_Syntax_Syntax.pos
                                                               ([[f]],
                                                                 cvars1, ax) in
                                                       let a_name =
                                                         Prims.op_Hat
                                                           "tot_fun_" fsym in
                                                       let uu____8630 =
                                                         FStar_SMTEncoding_Util.mkAssume
                                                           (tot_fun_ax,
                                                             (FStar_Pervasives_Native.Some
                                                                a_name),
                                                             a_name) in
                                                       [uu____8630]
                                                   | FStar_Pervasives_Native.Some
                                                       t1 ->
                                                       let f_has_t =
                                                         FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                           FStar_Pervasives_Native.None
                                                           f t1 in
                                                       let a_name =
                                                         Prims.op_Hat
                                                           "typing_" fsym in
                                                       let uu____8638 =
                                                         let uu____8639 =
                                                           let uu____8647 =
                                                             FStar_SMTEncoding_Term.mkForall
                                                               t0.FStar_Syntax_Syntax.pos
                                                               ([[f]],
                                                                 cvars1,
                                                                 f_has_t) in
                                                           (uu____8647,
                                                             (FStar_Pervasives_Native.Some
                                                                a_name),
                                                             a_name) in
                                                         FStar_SMTEncoding_Util.mkAssume
                                                           uu____8639 in
                                                       [uu____8638] in
                                                 let interp_f =
                                                   let a_name =
                                                     Prims.op_Hat
                                                       "interpretation_" fsym in
                                                   let uu____8662 =
                                                     let uu____8670 =
                                                       let uu____8671 =
                                                         let uu____8682 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app, body3) in
                                                         ([[app]],
                                                           (FStar_List.append
                                                              vars cvars1),
                                                           uu____8682) in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         t0.FStar_Syntax_Syntax.pos
                                                         uu____8671 in
                                                     (uu____8670,
                                                       (FStar_Pervasives_Native.Some
                                                          a_name), a_name) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____8662 in
                                                 let f_decls =
                                                   FStar_List.append (fdecl
                                                     :: typing_f) [interp_f] in
                                                 let uu____8696 =
                                                   let uu____8697 =
                                                     let uu____8700 =
                                                       let uu____8703 =
                                                         FStar_SMTEncoding_Term.mk_decls
                                                           fsym tkey_hash
                                                           f_decls
                                                           (FStar_List.append
                                                              decls
                                                              (FStar_List.append
                                                                 decls'
                                                                 decls'')) in
                                                       FStar_List.append
                                                         decls'' uu____8703 in
                                                     FStar_List.append decls'
                                                       uu____8700 in
                                                   FStar_List.append decls
                                                     uu____8697 in
                                                 (f, uu____8696)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8706,
             { FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____8707;
               FStar_Syntax_Syntax.lbunivs = uu____8708;
               FStar_Syntax_Syntax.lbtyp = uu____8709;
               FStar_Syntax_Syntax.lbeff = uu____8710;
               FStar_Syntax_Syntax.lbdef = uu____8711;
               FStar_Syntax_Syntax.lbattrs = uu____8712;
               FStar_Syntax_Syntax.lbpos = uu____8713;_}::uu____8714),
            uu____8715)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false,
             { FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
               FStar_Syntax_Syntax.lbunivs = uu____8749;
               FStar_Syntax_Syntax.lbtyp = t1;
               FStar_Syntax_Syntax.lbeff = uu____8751;
               FStar_Syntax_Syntax.lbdef = e1;
               FStar_Syntax_Syntax.lbattrs = uu____8753;
               FStar_Syntax_Syntax.lbpos = uu____8754;_}::[]),
            e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let
           ((false, uu____8781::uu____8782), uu____8783) ->
           failwith "Impossible: non-recursive let with multiple bindings"
       | FStar_Syntax_Syntax.Tm_let ((uu____8806, lbs), uu____8808) ->
           let names1 =
             FStar_All.pipe_right lbs
               (FStar_List.map
                  (fun lb ->
                     let uu____8861 = lb in
                     match uu____8861 with
                     | { FStar_Syntax_Syntax.lbname = lbname;
                         FStar_Syntax_Syntax.lbunivs = uu____8868;
                         FStar_Syntax_Syntax.lbtyp = uu____8869;
                         FStar_Syntax_Syntax.lbeff = uu____8870;
                         FStar_Syntax_Syntax.lbdef = uu____8871;
                         FStar_Syntax_Syntax.lbattrs = uu____8872;
                         FStar_Syntax_Syntax.lbpos = uu____8873;_} ->
                         let x = FStar_Util.left lbname in
                         let uu____8889 =
                           FStar_Ident.text_of_id
                             x.FStar_Syntax_Syntax.ppname in
                         let uu____8891 = FStar_Syntax_Syntax.range_of_bv x in
                         (uu____8889, uu____8891))) in
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
              let uu____8949 =
                let uu____8954 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None) in
                encode_term uu____8954 env in
              match uu____8949 with
              | (ee1, decls1) ->
                  let uu____8979 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2 in
                  (match uu____8979 with
                   | (xs, e21) ->
                       let uu____9004 = FStar_List.hd xs in
                       (match uu____9004 with
                        | (x1, uu____9022) ->
                            let env' =
                              FStar_SMTEncoding_Env.push_term_var env x1 ee1 in
                            let uu____9028 = encode_body e21 env' in
                            (match uu____9028 with
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
            let uu____9058 =
              let uu____9066 =
                let uu____9067 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____9067 in
              FStar_SMTEncoding_Env.gen_term_var env uu____9066 in
            match uu____9058 with
            | (scrsym, scr', env1) ->
                let uu____9077 = encode_term e env1 in
                (match uu____9077 with
                 | (scr, decls) ->
                     let uu____9088 =
                       let encode_branch b uu____9117 =
                         match uu____9117 with
                         | (else_case, decls1) ->
                             let uu____9136 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____9136 with
                              | (p, w, br) ->
                                  let uu____9162 = encode_pat env1 p in
                                  (match uu____9162 with
                                   | (env0, pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2 ->
                                                 fun uu____9199 ->
                                                   match uu____9199 with
                                                   | (x, t) ->
                                                       FStar_SMTEncoding_Env.push_term_var
                                                         env2 x t) env1) in
                                       let uu____9206 =
                                         match w with
                                         | FStar_Pervasives_Native.None ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____9228 =
                                               encode_term w1 env2 in
                                             (match uu____9228 with
                                              | (w2, decls2) ->
                                                  let uu____9241 =
                                                    let uu____9242 =
                                                      let uu____9247 =
                                                        let uu____9248 =
                                                          let uu____9253 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____9253) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____9248 in
                                                      (guard, uu____9247) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____9242 in
                                                  (uu____9241, decls2)) in
                                       (match uu____9206 with
                                        | (guard1, decls2) ->
                                            let uu____9268 =
                                              encode_br br env2 in
                                            (match uu____9268 with
                                             | (br1, decls3) ->
                                                 let uu____9281 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____9281,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____9088 with
                      | (match_tm, decls1) ->
                          let uu____9302 =
                            let uu____9303 =
                              let uu____9314 =
                                let uu____9321 =
                                  let uu____9326 =
                                    FStar_SMTEncoding_Term.mk_fv
                                      (scrsym,
                                        FStar_SMTEncoding_Term.Term_sort) in
                                  (uu____9326, scr) in
                                [uu____9321] in
                              (uu____9314, match_tm) in
                            FStar_SMTEncoding_Term.mkLet' uu____9303
                              FStar_Range.dummyRange in
                          (uu____9302, decls1)))
and (encode_pat :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.pat -> (FStar_SMTEncoding_Env.env_t * pattern))
  =
  fun env ->
    fun pat ->
      (let uu____9349 =
         FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
           FStar_Options.Medium in
       if uu____9349
       then
         let uu____9352 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____9352
       else ());
      (let uu____9357 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____9357 with
       | (vars, pat_term) ->
           let uu____9374 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____9416 ->
                     fun v1 ->
                       match uu____9416 with
                       | (env1, vars1) ->
                           let uu____9452 =
                             FStar_SMTEncoding_Env.gen_term_var env1 v1 in
                           (match uu____9452 with
                            | (xx, uu____9471, env2) ->
                                let uu____9475 =
                                  let uu____9482 =
                                    let uu____9487 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xx,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    (v1, uu____9487) in
                                  uu____9482 :: vars1 in
                                (env2, uu____9475))) (env, [])) in
           (match uu____9374 with
            | (env1, vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9542 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9543 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9544 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9552 = encode_const c env1 in
                      (match uu____9552 with
                       | (tm, decls) ->
                           ((match decls with
                             | uu____9560::uu____9561 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____9565 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f, args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon
                            env1.FStar_SMTEncoding_Env.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____9588 =
                          FStar_TypeChecker_Env.datacons_of_typ
                            env1.FStar_SMTEncoding_Env.tcenv tc_name in
                        match uu____9588 with
                        | (uu____9596, uu____9597::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9602 ->
                            FStar_SMTEncoding_Env.mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i ->
                                fun uu____9638 ->
                                  match uu____9638 with
                                  | (arg, uu____9648) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9657 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____9657)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x, uu____9689) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9720 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f, args) ->
                      let uu____9745 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i ->
                                fun uu____9791 ->
                                  match uu____9791 with
                                  | (arg, uu____9807) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9816 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____9816)) in
                      FStar_All.pipe_right uu____9745 FStar_List.flatten in
                let pat_term1 uu____9847 = encode_term pat_term env1 in
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
      let uu____9857 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9905 ->
                fun uu____9906 ->
                  match (uu____9905, uu____9906) with
                  | ((tms, decls), (t, uu____9946)) ->
                      let uu____9973 = encode_term t env in
                      (match uu____9973 with
                       | (t1, decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____9857 with | (l1, decls) -> ((FStar_List.rev l1), decls)
and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t ->
    fun env ->
      let universe_of_binders binders =
        FStar_List.map (fun uu____10051 -> FStar_Syntax_Syntax.U_zero)
          binders in
      let quant = FStar_Syntax_Util.smt_lemma_as_forall t universe_of_binders in
      let env1 =
        let uu___1382_10060 = env in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___1382_10060.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___1382_10060.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___1382_10060.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___1382_10060.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___1382_10060.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___1382_10060.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___1382_10060.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___1382_10060.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___1382_10060.FStar_SMTEncoding_Env.encoding_quantifier);
          FStar_SMTEncoding_Env.global_cache =
            (uu___1382_10060.FStar_SMTEncoding_Env.global_cache)
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
        let uu___1387_10077 = env in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___1387_10077.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___1387_10077.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___1387_10077.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___1387_10077.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___1387_10077.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___1387_10077.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___1387_10077.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___1387_10077.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___1387_10077.FStar_SMTEncoding_Env.encoding_quantifier);
          FStar_SMTEncoding_Env.global_cache =
            (uu___1387_10077.FStar_SMTEncoding_Env.global_cache)
        } in
      let encode_smt_pattern t =
        let uu____10093 = FStar_Syntax_Util.head_and_args t in
        match uu____10093 with
        | (head1, args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                uu____10156::(x, uu____10158)::(t1, uu____10160)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____10227 = encode_term x env1 in
                 (match uu____10227 with
                  | (x1, decls) ->
                      let uu____10238 = encode_term t1 env1 in
                      (match uu____10238 with
                       | (t2, decls') ->
                           let uu____10249 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t2 in
                           (uu____10249, (FStar_List.append decls decls'))))
             | uu____10250 -> encode_term t env1) in
      FStar_List.fold_right
        (fun pats ->
           fun uu____10293 ->
             match uu____10293 with
             | (pats_l1, decls) ->
                 let uu____10338 =
                   FStar_List.fold_right
                     (fun uu____10373 ->
                        fun uu____10374 ->
                          match (uu____10373, uu____10374) with
                          | ((p, uu____10416), (pats1, decls1)) ->
                              let uu____10451 = encode_smt_pattern p in
                              (match uu____10451 with
                               | (t, d) ->
                                   let uu____10466 =
                                     FStar_SMTEncoding_Term.check_pattern_ok
                                       t in
                                   (match uu____10466 with
                                    | FStar_Pervasives_Native.None ->
                                        ((t :: pats1),
                                          (FStar_List.append d decls1))
                                    | FStar_Pervasives_Native.Some
                                        illegal_subterm ->
                                        ((let uu____10483 =
                                            let uu____10489 =
                                              let uu____10491 =
                                                FStar_Syntax_Print.term_to_string
                                                  p in
                                              let uu____10493 =
                                                FStar_SMTEncoding_Term.print_smt_term
                                                  illegal_subterm in
                                              FStar_Util.format2
                                                "Pattern %s contains illegal sub-term (%s); dropping it"
                                                uu____10491 uu____10493 in
                                            (FStar_Errors.Warning_SMTPatternIllFormed,
                                              uu____10489) in
                                          FStar_Errors.log_issue
                                            p.FStar_Syntax_Syntax.pos
                                            uu____10483);
                                         (pats1,
                                           (FStar_List.append d decls1))))))
                     pats ([], decls) in
                 (match uu____10338 with
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
        let uu____10553 =
          FStar_All.pipe_left
            (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____10553
        then
          let uu____10558 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____10560 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10558 uu____10560
        else () in
      let enc f r l =
        let uu____10602 =
          FStar_Util.fold_map
            (fun decls ->
               fun x ->
                 let uu____10634 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____10634 with
                 | (t, decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____10602 with
        | (decls, args) ->
            let uu____10665 =
              let uu___1451_10666 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___1451_10666.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___1451_10666.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____10665, decls) in
      let const_op f r uu____10701 =
        let uu____10714 = f r in (uu____10714, []) in
      let un_op f l =
        let uu____10737 = FStar_List.hd l in
        FStar_All.pipe_left f uu____10737 in
      let bin_op f uu___2_10757 =
        match uu___2_10757 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10768 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____10809 =
          FStar_Util.fold_map
            (fun decls ->
               fun uu____10834 ->
                 match uu____10834 with
                 | (t, uu____10850) ->
                     let uu____10855 = encode_formula t env in
                     (match uu____10855 with
                      | (phi1, decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____10809 with
        | (decls, phis) ->
            let uu____10884 =
              let uu___1481_10885 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___1481_10885.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___1481_10885.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____10884, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____10948 ->
               match uu____10948 with
               | (a, q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____10969) -> false
                    | uu____10972 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____10991 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____10991
        else
          (let uu____11008 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____11008 r rf) in
      let eq3_op r args =
        let n1 = FStar_List.length args in
        if n1 = (Prims.parse_int "4")
        then
          let uu____11076 =
            enc
              (fun terms ->
                 match terms with
                 | t0::t1::v0::v1::[] ->
                     let uu____11108 =
                       let uu____11113 = FStar_SMTEncoding_Util.mkEq (t0, t1) in
                       let uu____11114 = FStar_SMTEncoding_Util.mkEq (v0, v1) in
                       (uu____11113, uu____11114) in
                     FStar_SMTEncoding_Util.mkAnd uu____11108
                 | uu____11115 -> failwith "Impossible") in
          uu____11076 r args
        else
          (let uu____11121 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1) in
           failwith uu____11121) in
      let h_equals_op r args =
        let n1 = FStar_List.length args in
        if n1 = (Prims.parse_int "4")
        then
          let uu____11183 =
            enc
              (fun terms ->
                 match terms with
                 | t0::v0::t1::v1::[] ->
                     let uu____11215 =
                       let uu____11220 = FStar_SMTEncoding_Util.mkEq (t0, t1) in
                       let uu____11221 = FStar_SMTEncoding_Util.mkEq (v0, v1) in
                       (uu____11220, uu____11221) in
                     FStar_SMTEncoding_Util.mkAnd uu____11215
                 | uu____11222 -> failwith "Impossible") in
          uu____11183 r args
        else
          (let uu____11228 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1) in
           failwith uu____11228) in
      let mk_imp1 r uu___3_11257 =
        match uu___3_11257 with
        | (lhs, uu____11263)::(rhs, uu____11265)::[] ->
            let uu____11306 = encode_formula rhs env in
            (match uu____11306 with
             | (l1, decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp, uu____11321) ->
                      (l1, decls1)
                  | uu____11326 ->
                      let uu____11327 = encode_formula lhs env in
                      (match uu____11327 with
                       | (l2, decls2) ->
                           let uu____11338 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____11338, (FStar_List.append decls1 decls2)))))
        | uu____11339 -> failwith "impossible" in
      let mk_ite r uu___4_11367 =
        match uu___4_11367 with
        | (guard, uu____11373)::(_then, uu____11375)::(_else, uu____11377)::[]
            ->
            let uu____11434 = encode_formula guard env in
            (match uu____11434 with
             | (g, decls1) ->
                 let uu____11445 = encode_formula _then env in
                 (match uu____11445 with
                  | (t, decls2) ->
                      let uu____11456 = encode_formula _else env in
                      (match uu____11456 with
                       | (e, decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11468 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____11498 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____11498 in
      let connectives =
        let uu____11528 =
          let uu____11553 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____11553) in
        let uu____11596 =
          let uu____11623 =
            let uu____11648 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____11648) in
          let uu____11691 =
            let uu____11718 =
              let uu____11745 =
                let uu____11770 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____11770) in
              let uu____11813 =
                let uu____11840 =
                  let uu____11867 =
                    let uu____11892 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____11892) in
                  [uu____11867;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.c_eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq3_op);
                  (FStar_Parser_Const.c_eq3_lid, h_equals_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11840 in
              uu____11745 :: uu____11813 in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11718 in
          uu____11623 :: uu____11691 in
        uu____11528 :: uu____11596 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) ->
            let uu____12437 = encode_formula phi' env in
            (match uu____12437 with
             | (phi2, decls) ->
                 let uu____12448 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____12448, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____12450 ->
            let uu____12457 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____12457 env
        | FStar_Syntax_Syntax.Tm_match (e, pats) ->
            let uu____12496 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____12496 with | (t, decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false,
              { FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____12508;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____12510;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____12512;
                FStar_Syntax_Syntax.lbpos = uu____12513;_}::[]),
             e2)
            ->
            let uu____12540 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____12540 with | (t, decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1, args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                uu____12593::(x, uu____12595)::(t, uu____12597)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12664 = encode_term x env in
                 (match uu____12664 with
                  | (x1, decls) ->
                      let uu____12675 = encode_term t env in
                      (match uu____12675 with
                       | (t1, decls') ->
                           let uu____12686 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____12686, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                (r, uu____12689)::(msg, uu____12691)::(phi2, uu____12693)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12760 =
                   let uu____12765 =
                     let uu____12766 = FStar_Syntax_Subst.compress r in
                     uu____12766.FStar_Syntax_Syntax.n in
                   let uu____12769 =
                     let uu____12770 = FStar_Syntax_Subst.compress msg in
                     uu____12770.FStar_Syntax_Syntax.n in
                   (uu____12765, uu____12769) in
                 (match uu____12760 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1), FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s, uu____12779))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1 in
                      fallback phi3
                  | uu____12790 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv, (t, uu____12797)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____12832 when head_redex env head2 ->
                 let uu____12847 = whnf env phi1 in
                 encode_formula uu____12847 env
             | uu____12848 ->
                 let uu____12863 = encode_term phi1 env in
                 (match uu____12863 with
                  | (tt, decls) ->
                      let tt1 =
                        let uu____12875 =
                          let uu____12877 =
                            FStar_Range.use_range
                              tt.FStar_SMTEncoding_Term.rng in
                          let uu____12878 =
                            FStar_Range.use_range
                              phi1.FStar_Syntax_Syntax.pos in
                          FStar_Range.rng_included uu____12877 uu____12878 in
                        if uu____12875
                        then tt
                        else
                          (let uu___1668_12882 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___1668_12882.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___1668_12882.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      let uu____12883 = FStar_SMTEncoding_Term.mk_Valid tt1 in
                      (uu____12883, decls)))
        | uu____12884 ->
            let uu____12885 = encode_term phi1 env in
            (match uu____12885 with
             | (tt, decls) ->
                 let tt1 =
                   let uu____12897 =
                     let uu____12899 =
                       FStar_Range.use_range tt.FStar_SMTEncoding_Term.rng in
                     let uu____12900 =
                       FStar_Range.use_range phi1.FStar_Syntax_Syntax.pos in
                     FStar_Range.rng_included uu____12899 uu____12900 in
                   if uu____12897
                   then tt
                   else
                     (let uu___1676_12904 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___1676_12904.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___1676_12904.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 let uu____12905 = FStar_SMTEncoding_Term.mk_Valid tt1 in
                 (uu____12905, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____12949 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____12949 with
        | (vars, guards, env2, decls, uu____12988) ->
            let uu____13001 = encode_smt_patterns ps env2 in
            (match uu____13001 with
             | (pats, decls') ->
                 let uu____13038 = encode_formula body env2 in
                 (match uu____13038 with
                  | (body1, decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf, p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____13070;
                             FStar_SMTEncoding_Term.rng = uu____13071;_}::[])::[]
                            when
                            let uu____13091 =
                              FStar_Ident.text_of_lid
                                FStar_Parser_Const.guard_free in
                            uu____13091 = gf -> []
                        | uu____13094 -> guards in
                      let uu____13099 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____13099, body1,
                        (FStar_List.append decls
                           (FStar_List.append decls' decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let uu____13110 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____13110 with
       | FStar_Pervasives_Native.None -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op, arms))
           ->
           let uu____13119 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____13225 ->
                     match uu____13225 with
                     | (l, uu____13250) -> FStar_Ident.lid_equals op l)) in
           (match uu____13119 with
            | FStar_Pervasives_Native.None -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____13319, f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars, pats, body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____13411 = encode_q_body env vars pats body in
             match uu____13411 with
             | (vars1, pats1, guard, body1, decls) ->
                 let tm =
                   let uu____13456 =
                     let uu____13467 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____13467) in
                   FStar_SMTEncoding_Term.mkForall
                     phi1.FStar_Syntax_Syntax.pos uu____13456 in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars, pats, body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____13498 = encode_q_body env vars pats body in
             match uu____13498 with
             | (vars1, pats1, guard, body1, decls) ->
                 let uu____13542 =
                   let uu____13543 =
                     let uu____13554 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____13554) in
                   FStar_SMTEncoding_Term.mkExists
                     phi1.FStar_Syntax_Syntax.pos uu____13543 in
                 (uu____13542, decls))))