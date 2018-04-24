open Prims
let mkForall_fuel' :
  'Auu____7 .
    'Auu____7 ->
      (FStar_SMTEncoding_Term.pat Prims.list Prims.list,
        FStar_SMTEncoding_Term.fvs, FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple3 -> FStar_SMTEncoding_Term.term
  =
  fun n1 ->
    fun uu____27 ->
      match uu____27 with
      | (pats, vars, body) ->
          let fallback uu____54 =
            FStar_SMTEncoding_Util.mkForall (pats, vars, body) in
          let uu____59 = FStar_Options.unthrottle_inductives () in
          if uu____59
          then fallback ()
          else
            (let uu____61 =
               FStar_SMTEncoding_Env.fresh_fvar "f"
                 FStar_SMTEncoding_Term.Fuel_sort in
             match uu____61 with
             | (fsym, fterm) ->
                 let add_fuel1 tms =
                   FStar_All.pipe_right tms
                     (FStar_List.map
                        (fun p ->
                           match p.FStar_SMTEncoding_Term.tm with
                           | FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var "HasType", args)
                               ->
                               FStar_SMTEncoding_Util.mkApp
                                 ("HasTypeFuel", (fterm :: args))
                           | uu____94 -> p)) in
                 let pats1 = FStar_List.map add_fuel1 pats in
                 let body1 =
                   match body.FStar_SMTEncoding_Term.tm with
                   | FStar_SMTEncoding_Term.App
                       (FStar_SMTEncoding_Term.Imp, guard::body'::[]) ->
                       let guard1 =
                         match guard.FStar_SMTEncoding_Term.tm with
                         | FStar_SMTEncoding_Term.App
                             (FStar_SMTEncoding_Term.And, guards) ->
                             let uu____115 = add_fuel1 guards in
                             FStar_SMTEncoding_Util.mk_and_l uu____115
                         | uu____118 ->
                             let uu____119 = add_fuel1 [guard] in
                             FStar_All.pipe_right uu____119 FStar_List.hd in
                       FStar_SMTEncoding_Util.mkImp (guard1, body')
                   | uu____124 -> body in
                 let vars1 = (fsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars in
                 FStar_SMTEncoding_Util.mkForall (pats1, vars1, body1))
let (mkForall_fuel :
  (FStar_SMTEncoding_Term.pat Prims.list Prims.list,
    FStar_SMTEncoding_Term.fvs, FStar_SMTEncoding_Term.term)
    FStar_Pervasives_Native.tuple3 -> FStar_SMTEncoding_Term.term)
  = mkForall_fuel' (Prims.parse_int "1")
let (head_normal :
  FStar_SMTEncoding_Env.env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env ->
    fun t ->
      let t1 = FStar_Syntax_Util.unmeta t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow uu____171 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____184 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____191 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____192 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____209 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____226 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____228 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____228 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____246;
             FStar_Syntax_Syntax.vars = uu____247;_},
           uu____248)
          ->
          let uu____269 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____269 FStar_Option.isNone
      | uu____286 -> false
let (head_redex :
  FStar_SMTEncoding_Env.env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env ->
    fun t ->
      let uu____297 =
        let uu____298 = FStar_Syntax_Util.un_uinst t in
        uu____298.FStar_Syntax_Syntax.n in
      match uu____297 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____301, uu____302, FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___68_323 ->
                  match uu___68_323 with
                  | FStar_Syntax_Syntax.TOTAL -> true
                  | uu____324 -> false) rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____326 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____326 FStar_Option.isSome
      | uu____343 -> false
let (whnf :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun t ->
      let uu____354 = head_normal env t in
      if uu____354
      then t
      else
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Weak;
          FStar_TypeChecker_Normalize.HNF;
          FStar_TypeChecker_Normalize.Exclude
            FStar_TypeChecker_Normalize.Zeta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses]
          env.FStar_SMTEncoding_Env.tcenv t
let (norm :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun t ->
      FStar_TypeChecker_Normalize.normalize
        [FStar_TypeChecker_Normalize.Beta;
        FStar_TypeChecker_Normalize.Exclude FStar_TypeChecker_Normalize.Zeta;
        FStar_TypeChecker_Normalize.Eager_unfolding;
        FStar_TypeChecker_Normalize.EraseUniverses]
        env.FStar_SMTEncoding_Env.tcenv t
let (trivial_post : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let uu____371 =
      let uu____372 = FStar_Syntax_Syntax.null_binder t in [uu____372] in
    let uu____373 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
    FStar_Syntax_Util.abs uu____371 uu____373 FStar_Pervasives_Native.None
let (mk_Apply :
  FStar_SMTEncoding_Term.term ->
    (Prims.string, FStar_SMTEncoding_Term.sort)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_SMTEncoding_Term.term)
  =
  fun e ->
    fun vars ->
      FStar_All.pipe_right vars
        (FStar_List.fold_left
           (fun out ->
              fun var ->
                match FStar_Pervasives_Native.snd var with
                | FStar_SMTEncoding_Term.Fuel_sort ->
                    let uu____415 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____415
                | s ->
                    let uu____418 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____418) e)
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
          let uu____466 =
            let uu____471 =
              let uu____472 = FStar_Util.string_of_int arity in
              let uu____473 = FStar_Util.string_of_int n_args in
              FStar_Util.format3
                "Head symbol %s expects at least %s arguments; got only %s"
                head1 uu____472 uu____473 in
            (FStar_Errors.Fatal_SMTEncodingArityMismatch, uu____471) in
          FStar_Errors.raise_error uu____466 rng
let (maybe_curry_app :
  FStar_Range.range ->
    FStar_SMTEncoding_Term.op ->
      Prims.int ->
        FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term)
  =
  fun rng ->
    fun head1 ->
      fun arity ->
        fun args ->
          let n_args = FStar_List.length args in
          if n_args = arity
          then FStar_SMTEncoding_Util.mkApp' (head1, args)
          else
            if n_args > arity
            then
              (let uu____512 = FStar_Util.first_N arity args in
               match uu____512 with
               | (args1, rest) ->
                   let head2 = FStar_SMTEncoding_Util.mkApp' (head1, args1) in
                   mk_Apply_args head2 rest)
            else
              (let uu____535 = FStar_SMTEncoding_Term.op_to_string head1 in
               raise_arity_mismatch uu____535 arity n_args rng)
let (is_app : FStar_SMTEncoding_Term.op -> Prims.bool) =
  fun uu___69_544 ->
    match uu___69_544 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____545 -> false
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
                   FStar_SMTEncoding_Term.freevars = uu____591;
                   FStar_SMTEncoding_Term.rng = uu____592;_}::[]),
             x::xs1) when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)
              -> check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var f, args),
             uu____615) ->
              let uu____624 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a ->
                        fun v1 ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____635 -> false) args (FStar_List.rev xs)) in
              if uu____624
              then FStar_SMTEncoding_Env.tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____639, []) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____643 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv ->
                        let uu____647 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____647)) in
              if uu____643
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____651 -> FStar_Pervasives_Native.None in
        check_partial_applications body (FStar_List.rev vars)
let check_pattern_vars :
  'Auu____668 'Auu____669 .
    FStar_SMTEncoding_Env.env_t ->
      (FStar_Syntax_Syntax.bv, 'Auu____668) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term, 'Auu____669)
          FStar_Pervasives_Native.tuple2 Prims.list -> unit
  =
  fun env ->
    fun vars ->
      fun pats ->
        let pats1 =
          FStar_All.pipe_right pats
            (FStar_List.map
               (fun uu____727 ->
                  match uu____727 with
                  | (x, uu____733) ->
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                        FStar_TypeChecker_Normalize.EraseUniverses]
                        env.FStar_SMTEncoding_Env.tcenv x)) in
        match pats1 with
        | [] -> ()
        | hd1::tl1 ->
            let pat_vars =
              let uu____741 = FStar_Syntax_Free.names hd1 in
              FStar_List.fold_left
                (fun out ->
                   fun x ->
                     let uu____753 = FStar_Syntax_Free.names x in
                     FStar_Util.set_union out uu____753) uu____741 tl1 in
            let uu____756 =
              FStar_All.pipe_right vars
                (FStar_Util.find_opt
                   (fun uu____783 ->
                      match uu____783 with
                      | (b, uu____789) ->
                          let uu____790 = FStar_Util.set_mem b pat_vars in
                          Prims.op_Negation uu____790)) in
            (match uu____756 with
             | FStar_Pervasives_Native.None -> ()
             | FStar_Pervasives_Native.Some (x, uu____796) ->
                 let pos =
                   FStar_List.fold_left
                     (fun out ->
                        fun t ->
                          FStar_Range.union_ranges out
                            t.FStar_Syntax_Syntax.pos)
                     hd1.FStar_Syntax_Syntax.pos tl1 in
                 let uu____810 =
                   let uu____815 =
                     let uu____816 = FStar_Syntax_Print.bv_to_string x in
                     FStar_Util.format1
                       "SMT pattern misses at least one bound variable: %s"
                       uu____816 in
                   (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                     uu____815) in
                 FStar_Errors.log_issue pos uu____810)
type label =
  (FStar_SMTEncoding_Term.fv, Prims.string, FStar_Range.range)
    FStar_Pervasives_Native.tuple3[@@deriving show]
type labels = label Prims.list[@@deriving show]
type pattern =
  {
  pat_vars:
    (FStar_Syntax_Syntax.bv, FStar_SMTEncoding_Term.fv)
      FStar_Pervasives_Native.tuple2 Prims.list
    ;
  pat_term:
    unit ->
      (FStar_SMTEncoding_Term.term, FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
    ;
  guard: FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term ;
  projections:
    FStar_SMTEncoding_Term.term ->
      (FStar_Syntax_Syntax.bv, FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2 Prims.list
    }[@@deriving show]
let (__proj__Mkpattern__item__pat_vars :
  pattern ->
    (FStar_Syntax_Syntax.bv, FStar_SMTEncoding_Term.fv)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun projectee ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__pat_vars
let (__proj__Mkpattern__item__pat_term :
  pattern ->
    unit ->
      (FStar_SMTEncoding_Term.term, FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun projectee ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__pat_term
let (__proj__Mkpattern__item__guard :
  pattern -> FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term) =
  fun projectee ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__guard
let (__proj__Mkpattern__item__projections :
  pattern ->
    FStar_SMTEncoding_Term.term ->
      (FStar_Syntax_Syntax.bv, FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun projectee ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__projections
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
        | FStar_Syntax_Syntax.Tm_arrow uu____1091 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____1104 ->
            let uu____1111 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____1111
        | uu____1112 ->
            if norm1
            then let uu____1113 = whnf env t1 in aux false uu____1113
            else
              (let uu____1115 =
                 let uu____1116 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____1117 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____1116 uu____1117 in
               failwith uu____1115) in
      aux true t0
let rec (curried_arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders, FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2)
  =
  fun k ->
    let k1 = FStar_Syntax_Subst.compress k in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
        FStar_Syntax_Subst.open_comp bs c
    | FStar_Syntax_Syntax.Tm_refine (bv, uu____1151) ->
        curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort
    | uu____1156 ->
        let uu____1157 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____1157)
let is_arithmetic_primitive :
  'Auu____1174 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____1174 Prims.list -> Prims.bool
  =
  fun head1 ->
    fun args ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv, uu____1196::uu____1197::[]) ->
          ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Addition)
               ||
               (FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.op_Subtraction))
              ||
              (FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.op_Multiply))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Division))
            ||
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Modulus)
      | (FStar_Syntax_Syntax.Tm_fvar fv, uu____1201::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____1204 -> false
let (isInteger : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun tm ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1, FStar_Pervasives_Native.None)) -> true
    | uu____1227 -> false
let (getInteger : FStar_Syntax_Syntax.term' -> Prims.int) =
  fun tm ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1, FStar_Pervasives_Native.None)) -> FStar_Util.int_of_string n1
    | uu____1244 -> failwith "Expected an Integer term"
let is_BitVector_primitive :
  'Auu____1251 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax, 'Auu____1251)
        FStar_Pervasives_Native.tuple2 Prims.list -> Prims.bool
  =
  fun head1 ->
    fun args ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,
         (sz_arg, uu____1292)::uu____1293::uu____1294::[]) ->
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
         (sz_arg, uu____1345)::uu____1346::[]) ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____1383 -> false
let rec (encode_const :
  FStar_Const.sconst ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term, FStar_SMTEncoding_Term.decl Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun c ->
    fun env ->
      match c with
      | FStar_Const.Const_unit -> (FStar_SMTEncoding_Term.mk_Term_unit, [])
      | FStar_Const.Const_bool (true) ->
          let uu____1704 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue in
          (uu____1704, [])
      | FStar_Const.Const_bool (false) ->
          let uu____1707 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse in
          (uu____1707, [])
      | FStar_Const.Const_char c1 ->
          let uu____1711 =
            let uu____1712 =
              let uu____1719 =
                let uu____1722 =
                  let uu____1723 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1) in
                  FStar_SMTEncoding_Term.boxInt uu____1723 in
                [uu____1722] in
              ("FStar.Char.__char_of_int", uu____1719) in
            FStar_SMTEncoding_Util.mkApp uu____1712 in
          (uu____1711, [])
      | FStar_Const.Const_int (i, FStar_Pervasives_Native.None) ->
          let uu____1739 =
            let uu____1740 = FStar_SMTEncoding_Util.mkInteger i in
            FStar_SMTEncoding_Term.boxInt uu____1740 in
          (uu____1739, [])
      | FStar_Const.Const_int (repr, FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.FStar_SMTEncoding_Env.tcenv).FStar_TypeChecker_Env.dsenv
              repr sw FStar_Range.dummyRange in
          encode_term syntax_term env
      | FStar_Const.Const_string (s, uu____1761) ->
          let uu____1762 =
            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.string_const s in
          (uu____1762, [])
      | FStar_Const.Const_range uu____1765 ->
          let uu____1766 = FStar_SMTEncoding_Term.mk_Range_const () in
          (uu____1766, [])
      | FStar_Const.Const_effect -> (FStar_SMTEncoding_Term.mk_Term_type, [])
      | c1 ->
          let uu____1772 =
            let uu____1773 = FStar_Syntax_Print.const_to_string c1 in
            FStar_Util.format1 "Unhandled constant: %s" uu____1773 in
          failwith uu____1772
and (encode_binders :
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.binders ->
      FStar_SMTEncoding_Env.env_t ->
        (FStar_SMTEncoding_Term.fv Prims.list,
          FStar_SMTEncoding_Term.term Prims.list,
          FStar_SMTEncoding_Env.env_t, FStar_SMTEncoding_Term.decls_t,
          FStar_Syntax_Syntax.bv Prims.list) FStar_Pervasives_Native.tuple5)
  =
  fun fuel_opt ->
    fun bs ->
      fun env ->
        (let uu____1802 =
           FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
             FStar_Options.Low in
         if uu____1802
         then
           let uu____1803 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____1803
         else ());
        (let uu____1805 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____1889 ->
                   fun b ->
                     match uu____1889 with
                     | (vars, guards, env1, decls, names1) ->
                         let uu____1968 =
                           let x =
                             FStar_SMTEncoding_Env.unmangle
                               (FStar_Pervasives_Native.fst b) in
                           let uu____1984 =
                             FStar_SMTEncoding_Env.gen_term_var env1 x in
                           match uu____1984 with
                           | (xxsym, xx, env') ->
                               let uu____2008 =
                                 let uu____2013 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____2013 env1 xx in
                               (match uu____2008 with
                                | (guard_x_t, decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____1968 with
                          | (v1, g, env2, decls', n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____1805 with
         | (vars, guards, env1, decls, names1) ->
             ((FStar_List.rev vars), (FStar_List.rev guards), env1, decls,
               (FStar_List.rev names1)))
and (encode_term_pred :
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.typ ->
      FStar_SMTEncoding_Env.env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term, FStar_SMTEncoding_Term.decls_t)
            FStar_Pervasives_Native.tuple2)
  =
  fun fuel_opt ->
    fun t ->
      fun env ->
        fun e ->
          let uu____2172 = encode_term t env in
          match uu____2172 with
          | (t1, decls) ->
              let uu____2183 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____2183, decls)
and (encode_term_pred' :
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.typ ->
      FStar_SMTEncoding_Env.env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term, FStar_SMTEncoding_Term.decls_t)
            FStar_Pervasives_Native.tuple2)
  =
  fun fuel_opt ->
    fun t ->
      fun env ->
        fun e ->
          let uu____2194 = encode_term t env in
          match uu____2194 with
          | (t1, decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None ->
                   let uu____2209 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____2209, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____2211 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____2211, decls))
and (encode_arith_term :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term, FStar_SMTEncoding_Term.decls_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun head1 ->
      fun args_e ->
        let uu____2217 = encode_args args_e env in
        match uu____2217 with
        | (arg_tms, decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____2236 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____2247 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____2247 in
            let binary arg_tms1 =
              let uu____2262 =
                let uu____2263 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____2263 in
              let uu____2264 =
                let uu____2265 =
                  let uu____2266 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____2266 in
                FStar_SMTEncoding_Term.unboxInt uu____2265 in
              (uu____2262, uu____2264) in
            let mk_default uu____2274 =
              let uu____2275 =
                FStar_SMTEncoding_Env.lookup_free_var_sym env
                  head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____2275 with
              | (fname, fuel_args, arity) ->
                  let args = FStar_List.append fuel_args arg_tms in
                  maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity
                    args in
            let mk_l op mk_args ts =
              let uu____2337 = FStar_Options.smtencoding_l_arith_native () in
              if uu____2337
              then
                let uu____2338 = let uu____2339 = mk_args ts in op uu____2339 in
                FStar_All.pipe_right uu____2338 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____2374 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____2374
              then
                let uu____2375 = binary ts in
                match uu____2375 with
                | (t1, t2) ->
                    let uu____2382 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____2382
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____2386 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____2386
                 then
                   let uu____2387 =
                     let uu____2388 = binary ts in op uu____2388 in
                   FStar_All.pipe_right uu____2387
                     FStar_SMTEncoding_Term.boxInt
                 else mk_default ()) in
            let add1 = mk_l FStar_SMTEncoding_Util.mkAdd binary in
            let sub1 = mk_l FStar_SMTEncoding_Util.mkSub binary in
            let minus = mk_l FStar_SMTEncoding_Util.mkMinus unary in
            let mul1 = mk_nl "_mul" FStar_SMTEncoding_Util.mkMul in
            let div1 = mk_nl "_div" FStar_SMTEncoding_Util.mkDiv in
            let modulus = mk_nl "_mod" FStar_SMTEncoding_Util.mkMod in
            let ops =
              [(FStar_Parser_Const.op_Addition, add1);
              (FStar_Parser_Const.op_Subtraction, sub1);
              (FStar_Parser_Const.op_Multiply, mul1);
              (FStar_Parser_Const.op_Division, div1);
              (FStar_Parser_Const.op_Modulus, modulus);
              (FStar_Parser_Const.op_Minus, minus)] in
            let uu____2549 =
              let uu____2559 =
                FStar_List.tryFind
                  (fun uu____2583 ->
                     match uu____2583 with
                     | (l, uu____2593) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____2559 FStar_Util.must in
            (match uu____2549 with
             | (uu____2637, op) ->
                 let uu____2649 = op arg_tms in (uu____2649, decls))
and (encode_BitVector_term :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.arg Prims.list ->
        (FStar_SMTEncoding_Term.term, FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun head1 ->
      fun args_e ->
        let uu____2657 = FStar_List.hd args_e in
        match uu____2657 with
        | (tm_sz, uu____2665) ->
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz) in
            let sz_decls =
              let uu____2675 =
                FStar_Util.smap_try_find env.FStar_SMTEncoding_Env.cache
                  sz_key in
              match uu____2675 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None ->
                  let t_decls1 = FStar_SMTEncoding_Term.mkBvConstructor sz in
                  ((let uu____2683 =
                      FStar_SMTEncoding_Env.mk_cache_entry env "" [] [] in
                    FStar_Util.smap_add env.FStar_SMTEncoding_Env.cache
                      sz_key uu____2683);
                   t_decls1) in
            let uu____2684 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar fv,
                 uu____2704::(sz_arg, uu____2706)::uu____2707::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____2756 =
                    let uu____2759 = FStar_List.tail args_e in
                    FStar_List.tail uu____2759 in
                  let uu____2762 =
                    let uu____2765 = getInteger sz_arg.FStar_Syntax_Syntax.n in
                    FStar_Pervasives_Native.Some uu____2765 in
                  (uu____2756, uu____2762)
              | (FStar_Syntax_Syntax.Tm_fvar fv,
                 uu____2771::(sz_arg, uu____2773)::uu____2774::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____2823 =
                    let uu____2824 = FStar_Syntax_Print.term_to_string sz_arg in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____2824 in
                  failwith uu____2823
              | uu____2833 ->
                  let uu____2840 = FStar_List.tail args_e in
                  (uu____2840, FStar_Pervasives_Native.None) in
            (match uu____2684 with
             | (arg_tms, ext_sz) ->
                 let uu____2863 = encode_args arg_tms env in
                 (match uu____2863 with
                  | (arg_tms1, decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____2884 -> failwith "Impossible" in
                      let unary arg_tms2 =
                        let uu____2895 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____2895 in
                      let unary_arith arg_tms2 =
                        let uu____2906 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxInt uu____2906 in
                      let binary arg_tms2 =
                        let uu____2921 =
                          let uu____2922 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____2922 in
                        let uu____2923 =
                          let uu____2924 =
                            let uu____2925 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____2925 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____2924 in
                        (uu____2921, uu____2923) in
                      let binary_arith arg_tms2 =
                        let uu____2942 =
                          let uu____2943 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____2943 in
                        let uu____2944 =
                          let uu____2945 =
                            let uu____2946 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____2946 in
                          FStar_SMTEncoding_Term.unboxInt uu____2945 in
                        (uu____2942, uu____2944) in
                      let mk_bv op mk_args resBox ts =
                        let uu____3004 =
                          let uu____3005 = mk_args ts in op uu____3005 in
                        FStar_All.pipe_right uu____3004 resBox in
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
                        let uu____3137 =
                          let uu____3142 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None ->
                                failwith "impossible" in
                          FStar_SMTEncoding_Util.mkBvUext uu____3142 in
                        let uu____3144 =
                          let uu____3149 =
                            let uu____3150 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None ->
                                  failwith "impossible" in
                            sz + uu____3150 in
                          FStar_SMTEncoding_Term.boxBitVec uu____3149 in
                        mk_bv uu____3137 unary uu____3144 arg_tms2 in
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
                      let uu____3383 =
                        let uu____3393 =
                          FStar_List.tryFind
                            (fun uu____3417 ->
                               match uu____3417 with
                               | (l, uu____3427) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops in
                        FStar_All.pipe_right uu____3393 FStar_Util.must in
                      (match uu____3383 with
                       | (uu____3473, op) ->
                           let uu____3485 = op arg_tms1 in
                           (uu____3485, (FStar_List.append sz_decls decls)))))
and (encode_deeply_embedded_quantifier :
  FStar_Syntax_Syntax.term ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term, FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t ->
    fun env ->
      let env1 =
        let uu___73_3495 = env in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___73_3495.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___73_3495.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___73_3495.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___73_3495.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___73_3495.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.cache =
            (uu___73_3495.FStar_SMTEncoding_Env.cache);
          FStar_SMTEncoding_Env.nolabels =
            (uu___73_3495.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name =
            (uu___73_3495.FStar_SMTEncoding_Env.use_zfuel_name);
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___73_3495.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___73_3495.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier = true
        } in
      let uu____3496 = encode_term t env1 in
      match uu____3496 with
      | (tm, decls) ->
          let vars = FStar_SMTEncoding_Term.free_variables tm in
          let valid_tm = FStar_SMTEncoding_Term.mk_Valid tm in
          let key = FStar_SMTEncoding_Util.mkForall ([], vars, valid_tm) in
          let tkey_hash = FStar_SMTEncoding_Term.hash_of_term key in
          let uu____3517 =
            FStar_Util.smap_try_find env1.FStar_SMTEncoding_Env.cache
              tkey_hash in
          (match uu____3517 with
           | FStar_Pervasives_Native.Some uu____3524 -> (tm, decls)
           | uu____3525 ->
               (match tm.FStar_SMTEncoding_Term.tm with
                | FStar_SMTEncoding_Term.App
                    (uu____3532,
                     {
                       FStar_SMTEncoding_Term.tm =
                         FStar_SMTEncoding_Term.FreeV uu____3533;
                       FStar_SMTEncoding_Term.freevars = uu____3534;
                       FStar_SMTEncoding_Term.rng = uu____3535;_}::{
                                                                    FStar_SMTEncoding_Term.tm
                                                                    =
                                                                    FStar_SMTEncoding_Term.FreeV
                                                                    uu____3536;
                                                                    FStar_SMTEncoding_Term.freevars
                                                                    =
                                                                    uu____3537;
                                                                    FStar_SMTEncoding_Term.rng
                                                                    =
                                                                    uu____3538;_}::[])
                    ->
                    (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                       (FStar_Errors.Warning_QuantifierWithoutPattern,
                         "Not encoding deeply embedded, unguarded quantifier to SMT");
                     (tm, decls))
                | uu____3566 ->
                    let uu____3567 = encode_formula t env1 in
                    (match uu____3567 with
                     | (phi, decls') ->
                         let interp =
                           match vars with
                           | [] ->
                               let uu____3583 =
                                 let uu____3588 =
                                   FStar_SMTEncoding_Term.mk_Valid tm in
                                 (uu____3588, phi) in
                               FStar_SMTEncoding_Util.mkIff uu____3583
                           | uu____3589 ->
                               let uu____3590 =
                                 let uu____3601 =
                                   let uu____3602 =
                                     let uu____3607 =
                                       FStar_SMTEncoding_Term.mk_Valid tm in
                                     (uu____3607, phi) in
                                   FStar_SMTEncoding_Util.mkIff uu____3602 in
                                 ([[valid_tm]], vars, uu____3601) in
                               FStar_SMTEncoding_Util.mkForall uu____3590 in
                         let ax =
                           let uu____3617 =
                             let uu____3624 =
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 "l_quant_interp" in
                             (interp,
                               (FStar_Pervasives_Native.Some
                                  "Interpretation of deeply embedded quantifier"),
                               uu____3624) in
                           FStar_SMTEncoding_Util.mkAssume uu____3617 in
                         ((let uu____3628 =
                             FStar_SMTEncoding_Env.mk_cache_entry env1 "" []
                               [ax] in
                           FStar_Util.smap_add
                             env1.FStar_SMTEncoding_Env.cache tkey_hash
                             uu____3628);
                          (tm,
                            (FStar_List.append decls
                               (FStar_List.append decls' [ax])))))))
and (encode_term :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term, FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t ->
    fun env ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____3639 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____3639
       then
         let uu____3640 = FStar_Syntax_Print.tag_of_term t in
         let uu____3641 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____3642 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____3640 uu____3641
           uu____3642
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____3648 ->
           let uu____3673 =
             let uu____3674 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____3675 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____3676 = FStar_Syntax_Print.term_to_string t0 in
             let uu____3677 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____3674
               uu____3675 uu____3676 uu____3677 in
           failwith uu____3673
       | FStar_Syntax_Syntax.Tm_unknown ->
           let uu____3682 =
             let uu____3683 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____3684 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____3685 = FStar_Syntax_Print.term_to_string t0 in
             let uu____3686 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____3683
               uu____3684 uu____3685 uu____3686 in
           failwith uu____3682
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____3692 = FStar_Syntax_Util.unfold_lazy i in
           encode_term uu____3692 env
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____3694 =
             let uu____3695 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____3695 in
           failwith uu____3694
       | FStar_Syntax_Syntax.Tm_ascribed (t1, (k, uu____3702), uu____3703) ->
           let uu____3752 =
             match k with
             | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
             | uu____3760 -> false in
           if uu____3752
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t1 env
       | FStar_Syntax_Syntax.Tm_quoted (qt, uu____3777) ->
           let tv =
             let uu____3783 = FStar_Reflection_Basic.inspect_ln qt in
             FStar_Syntax_Embeddings.embed
               FStar_Reflection_Embeddings.e_term_view
               t.FStar_Syntax_Syntax.pos uu____3783 in
           let t1 =
             let uu____3787 =
               let uu____3796 = FStar_Syntax_Syntax.as_arg tv in [uu____3796] in
             FStar_Syntax_Util.mk_app
               (FStar_Reflection_Data.refl_constant_term
                  FStar_Reflection_Data.fstar_refl_pack_ln) uu____3787 in
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta
           (t1, FStar_Syntax_Syntax.Meta_pattern uu____3798) ->
           encode_term t1
             (let uu___74_3814 = env in
              {
                FStar_SMTEncoding_Env.bvar_bindings =
                  (uu___74_3814.FStar_SMTEncoding_Env.bvar_bindings);
                FStar_SMTEncoding_Env.fvar_bindings =
                  (uu___74_3814.FStar_SMTEncoding_Env.fvar_bindings);
                FStar_SMTEncoding_Env.depth =
                  (uu___74_3814.FStar_SMTEncoding_Env.depth);
                FStar_SMTEncoding_Env.tcenv =
                  (uu___74_3814.FStar_SMTEncoding_Env.tcenv);
                FStar_SMTEncoding_Env.warn =
                  (uu___74_3814.FStar_SMTEncoding_Env.warn);
                FStar_SMTEncoding_Env.cache =
                  (uu___74_3814.FStar_SMTEncoding_Env.cache);
                FStar_SMTEncoding_Env.nolabels =
                  (uu___74_3814.FStar_SMTEncoding_Env.nolabels);
                FStar_SMTEncoding_Env.use_zfuel_name =
                  (uu___74_3814.FStar_SMTEncoding_Env.use_zfuel_name);
                FStar_SMTEncoding_Env.encode_non_total_function_typ =
                  (uu___74_3814.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                FStar_SMTEncoding_Env.current_module_name =
                  (uu___74_3814.FStar_SMTEncoding_Env.current_module_name);
                FStar_SMTEncoding_Env.encoding_quantifier = false
              })
       | FStar_Syntax_Syntax.Tm_meta (t1, uu____3816) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = FStar_SMTEncoding_Env.lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____3826 = head_redex env t in
           if uu____3826
           then let uu____3831 = whnf env t in encode_term uu____3831 env
           else
             (let uu____3833 =
                FStar_SMTEncoding_Env.lookup_free_var_name env
                  v1.FStar_Syntax_Syntax.fv_name in
              match uu____3833 with
              | (uu____3842, arity) ->
                  let tok =
                    FStar_SMTEncoding_Env.lookup_free_var env
                      v1.FStar_Syntax_Syntax.fv_name in
                  let aux_decls =
                    if arity > (Prims.parse_int "0")
                    then
                      match tok.FStar_SMTEncoding_Term.tm with
                      | FStar_SMTEncoding_Term.FreeV uu____3852 ->
                          let uu____3857 =
                            let uu____3858 =
                              let uu____3865 =
                                FStar_SMTEncoding_Term.kick_partial_app tok in
                              let uu____3866 =
                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                  "@kick_partial_app" in
                              (uu____3865,
                                (FStar_Pervasives_Native.Some
                                   "kick_partial_app"), uu____3866) in
                            FStar_SMTEncoding_Util.mkAssume uu____3858 in
                          [uu____3857]
                      | FStar_SMTEncoding_Term.App (uu____3869, []) ->
                          let uu____3872 =
                            let uu____3873 =
                              let uu____3880 =
                                FStar_SMTEncoding_Term.kick_partial_app tok in
                              let uu____3881 =
                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                  "@kick_partial_app" in
                              (uu____3880,
                                (FStar_Pervasives_Native.Some
                                   "kick_partial_app"), uu____3881) in
                            FStar_SMTEncoding_Util.mkAssume uu____3873 in
                          [uu____3872]
                      | uu____3884 -> []
                    else [] in
                  (tok, aux_decls))
       | FStar_Syntax_Syntax.Tm_type uu____3888 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1, uu____3892) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders, c) ->
           let module_name = env.FStar_SMTEncoding_Env.current_module_name in
           let uu____3917 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____3917 with
            | (binders1, res) ->
                let uu____3928 =
                  (env.FStar_SMTEncoding_Env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____3928
                then
                  let uu____3933 =
                    encode_binders FStar_Pervasives_Native.None binders1 env in
                  (match uu____3933 with
                   | (vars, guards, env', decls, uu____3958) ->
                       let fsym =
                         let uu____3976 =
                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                             "f" in
                         (uu____3976, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____3979 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___75_3988 =
                              env.FStar_SMTEncoding_Env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___75_3988.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___75_3988.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___75_3988.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___75_3988.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___75_3988.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___75_3988.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___75_3988.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___75_3988.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___75_3988.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___75_3988.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___75_3988.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___75_3988.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___75_3988.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___75_3988.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___75_3988.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___75_3988.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___75_3988.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___75_3988.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___75_3988.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___75_3988.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___75_3988.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___75_3988.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___75_3988.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___75_3988.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___75_3988.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___75_3988.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___75_3988.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___75_3988.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___75_3988.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___75_3988.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___75_3988.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___75_3988.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___75_3988.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___75_3988.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___75_3988.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___75_3988.FStar_TypeChecker_Env.dep_graph)
                            }) res in
                       (match uu____3979 with
                        | (pre_opt, res_t) ->
                            let uu____3999 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app in
                            (match uu____3999 with
                             | (res_pred, decls') ->
                                 let uu____4010 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None ->
                                       let uu____4023 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____4023, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____4027 =
                                         encode_formula pre env' in
                                       (match uu____4027 with
                                        | (guard, decls0) ->
                                            let uu____4040 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____4040, decls0)) in
                                 (match uu____4010 with
                                  | (guards1, guard_decls) ->
                                      let t_interp =
                                        let uu____4052 =
                                          let uu____4063 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____4063) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____4052 in
                                      let cvars =
                                        let uu____4081 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____4081
                                          (FStar_List.filter
                                             (fun uu____4095 ->
                                                match uu____4095 with
                                                | (x, uu____4101) ->
                                                    x <>
                                                      (FStar_Pervasives_Native.fst
                                                         fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____4120 =
                                        FStar_Util.smap_try_find
                                          env.FStar_SMTEncoding_Env.cache
                                          tkey_hash in
                                      (match uu____4120 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____4128 =
                                             let uu____4129 =
                                               let uu____4136 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                                 uu____4136) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4129 in
                                           (uu____4128,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (FStar_SMTEncoding_Env.use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None ->
                                           let tsym =
                                             let uu____4156 =
                                               let uu____4157 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____4157 in
                                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                               uu____4156 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars in
                                           let caption =
                                             let uu____4168 =
                                               FStar_Options.log_queries () in
                                             if uu____4168
                                             then
                                               let uu____4171 =
                                                 let uu____4172 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env.FStar_SMTEncoding_Env.tcenv
                                                     t0 in
                                                 FStar_Util.replace_char
                                                   uu____4172 10 32 in
                                               FStar_Pervasives_Native.Some
                                                 uu____4171
                                             else
                                               FStar_Pervasives_Native.None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____4182 =
                                               let uu____4189 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____4189) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4182 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____4201 =
                                               let uu____4208 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____4208,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4201 in
                                           let f_has_t =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               f t1 in
                                           let f_has_t_z =
                                             FStar_SMTEncoding_Term.mk_HasTypeZ
                                               f t1 in
                                           let pre_typing =
                                             let a_name =
                                               Prims.strcat "pre_typing_"
                                                 tsym in
                                             let uu____4229 =
                                               let uu____4236 =
                                                 let uu____4237 =
                                                   let uu____4248 =
                                                     let uu____4249 =
                                                       let uu____4254 =
                                                         let uu____4255 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____4255 in
                                                       (f_has_t, uu____4254) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____4249 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____4248) in
                                                 mkForall_fuel uu____4237 in
                                               (uu____4236,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4229 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____4278 =
                                               let uu____4285 =
                                                 let uu____4286 =
                                                   let uu____4297 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____4297) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____4286 in
                                               (uu____4285,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4278 in
                                           let t_decls1 =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____4322 =
                                               FStar_SMTEncoding_Env.mk_cache_entry
                                                 env tsym cvar_sorts t_decls1 in
                                             FStar_Util.smap_add
                                               env.FStar_SMTEncoding_Env.cache
                                               tkey_hash uu____4322);
                                            (t1, t_decls1)))))))
                else
                  (let tsym =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                       "Non_total_Tm_arrow" in
                   let tdecl =
                     FStar_SMTEncoding_Term.DeclFun
                       (tsym, [], FStar_SMTEncoding_Term.Term_sort,
                         FStar_Pervasives_Native.None) in
                   let t1 = FStar_SMTEncoding_Util.mkApp (tsym, []) in
                   let t_kinding =
                     let a_name =
                       Prims.strcat "non_total_function_typing_" tsym in
                     let uu____4337 =
                       let uu____4344 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____4344,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____4337 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____4356 =
                       let uu____4363 =
                         let uu____4364 =
                           let uu____4375 =
                             let uu____4376 =
                               let uu____4381 =
                                 let uu____4382 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____4382 in
                               (f_has_t, uu____4381) in
                             FStar_SMTEncoding_Util.mkImp uu____4376 in
                           ([[f_has_t]], [fsym], uu____4375) in
                         mkForall_fuel uu____4364 in
                       (uu____4363, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____4356 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____4409 ->
           let uu____4416 =
             let uu____4421 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.Weak;
                 FStar_TypeChecker_Normalize.HNF;
                 FStar_TypeChecker_Normalize.EraseUniverses]
                 env.FStar_SMTEncoding_Env.tcenv t0 in
             match uu____4421 with
             | {
                 FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f);
                 FStar_Syntax_Syntax.pos = uu____4428;
                 FStar_Syntax_Syntax.vars = uu____4429;_} ->
                 let uu____4436 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f in
                 (match uu____4436 with
                  | (b, f1) ->
                      let uu____4461 =
                        let uu____4462 = FStar_List.hd b in
                        FStar_Pervasives_Native.fst uu____4462 in
                      (uu____4461, f1))
             | uu____4471 -> failwith "impossible" in
           (match uu____4416 with
            | (x, f) ->
                let uu____4482 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____4482 with
                 | (base_t, decls) ->
                     let uu____4493 =
                       FStar_SMTEncoding_Env.gen_term_var env x in
                     (match uu____4493 with
                      | (x1, xtm, env') ->
                          let uu____4507 = encode_formula f env' in
                          (match uu____4507 with
                           | (refinement, decls') ->
                               let uu____4518 =
                                 FStar_SMTEncoding_Env.fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____4518 with
                                | (fsym, fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____4534 =
                                        let uu____4537 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____4544 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____4537
                                          uu____4544 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____4534 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____4577 ->
                                              match uu____4577 with
                                              | (y, uu____4583) ->
                                                  (y <> x1) && (y <> fsym))) in
                                    let xfv =
                                      (x1, FStar_SMTEncoding_Term.Term_sort) in
                                    let ffv =
                                      (fsym,
                                        FStar_SMTEncoding_Term.Fuel_sort) in
                                    let tkey =
                                      FStar_SMTEncoding_Util.mkForall
                                        ([], (ffv :: xfv :: cvars1),
                                          encoding) in
                                    let tkey_hash =
                                      FStar_SMTEncoding_Term.hash_of_term
                                        tkey in
                                    let uu____4616 =
                                      FStar_Util.smap_try_find
                                        env.FStar_SMTEncoding_Env.cache
                                        tkey_hash in
                                    (match uu____4616 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____4624 =
                                           let uu____4625 =
                                             let uu____4632 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                               uu____4632) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____4625 in
                                         (uu____4624,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (FStar_SMTEncoding_Env.use_cache_entry
                                                    cache_entry))))
                                     | FStar_Pervasives_Native.None ->
                                         let module_name =
                                           env.FStar_SMTEncoding_Env.current_module_name in
                                         let tsym =
                                           let uu____4653 =
                                             let uu____4654 =
                                               let uu____4655 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____4655 in
                                             Prims.strcat module_name
                                               uu____4654 in
                                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                             uu____4653 in
                                         let cvar_sorts =
                                           FStar_List.map
                                             FStar_Pervasives_Native.snd
                                             cvars1 in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None) in
                                         let t1 =
                                           let uu____4669 =
                                             let uu____4676 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____4676) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____4669 in
                                         let x_has_base_t =
                                           FStar_SMTEncoding_Term.mk_HasType
                                             xtm base_t in
                                         let x_has_t =
                                           FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                             (FStar_Pervasives_Native.Some
                                                fterm) xtm t1 in
                                         let t_has_kind =
                                           FStar_SMTEncoding_Term.mk_HasType
                                             t1
                                             FStar_SMTEncoding_Term.mk_Term_type in
                                         let t_haseq_base =
                                           FStar_SMTEncoding_Term.mk_haseq
                                             base_t in
                                         let t_haseq_ref =
                                           FStar_SMTEncoding_Term.mk_haseq t1 in
                                         let t_haseq1 =
                                           let uu____4691 =
                                             let uu____4698 =
                                               let uu____4699 =
                                                 let uu____4710 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____4710) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____4699 in
                                             (uu____4698,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4691 in
                                         let t_kinding =
                                           let uu____4728 =
                                             let uu____4735 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____4735,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4728 in
                                         let t_interp =
                                           let uu____4753 =
                                             let uu____4760 =
                                               let uu____4761 =
                                                 let uu____4772 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____4772) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____4761 in
                                             (uu____4760,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement_interpretation"),
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4753 in
                                         let t_decls1 =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____4801 =
                                             FStar_SMTEncoding_Env.mk_cache_entry
                                               env tsym cvar_sorts t_decls1 in
                                           FStar_Util.smap_add
                                             env.FStar_SMTEncoding_Env.cache
                                             tkey_hash uu____4801);
                                          (t1, t_decls1))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv, k) ->
           let ttm =
             let uu____4831 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____4831 in
           let uu____4832 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm in
           (match uu____4832 with
            | (t_has_k, decls) ->
                let d =
                  let uu____4844 =
                    let uu____4851 =
                      let uu____4852 =
                        let uu____4853 =
                          let uu____4854 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____4854 in
                        FStar_Util.format1 "uvar_typing_%s" uu____4853 in
                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                        uu____4852 in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____4851) in
                  FStar_SMTEncoding_Util.mkAssume uu____4844 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____4859 ->
           let uu____4874 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____4874 with
            | (head1, args_e) ->
                let uu____4915 =
                  let uu____4928 =
                    let uu____4929 = FStar_Syntax_Subst.compress head1 in
                    uu____4929.FStar_Syntax_Syntax.n in
                  (uu____4928, args_e) in
                (match uu____4915 with
                 | uu____4944 when head_redex env head1 ->
                     let uu____4957 = whnf env t in
                     encode_term uu____4957 env
                 | uu____4958 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____4977 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_fvar fv, uu____4991) when
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
                       FStar_Syntax_Syntax.pos = uu____5009;
                       FStar_Syntax_Syntax.vars = uu____5010;_},
                     uu____5011),
                    uu____5012) when
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
                       FStar_Syntax_Syntax.pos = uu____5034;
                       FStar_Syntax_Syntax.vars = uu____5035;_},
                     uu____5036),
                    uu____5037::(v1, uu____5039)::(v2, uu____5041)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____5092 = encode_term v1 env in
                     (match uu____5092 with
                      | (v11, decls1) ->
                          let uu____5103 = encode_term v2 env in
                          (match uu____5103 with
                           | (v21, decls2) ->
                               let uu____5114 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____5114,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar fv,
                    uu____5118::(v1, uu____5120)::(v2, uu____5122)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____5169 = encode_term v1 env in
                     (match uu____5169 with
                      | (v11, decls1) ->
                          let uu____5180 = encode_term v2 env in
                          (match uu____5180 with
                           | (v21, decls2) ->
                               let uu____5191 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____5191,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of), (arg, uu____5195)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of),
                    (arg, uu____5221)::(rng, uu____5223)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reify), uu____5258) ->
                     let e0 =
                       let uu____5276 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg
                         env.FStar_SMTEncoding_Env.tcenv head1 uu____5276 in
                     ((let uu____5284 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug
                              env.FStar_SMTEncoding_Env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____5284
                       then
                         let uu____5285 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____5285
                       else ());
                      (let e =
                         let uu____5290 =
                           let uu____5295 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____5296 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____5295
                             uu____5296 in
                         uu____5290 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect uu____5305),
                    (arg, uu____5307)::[]) -> encode_term arg env
                 | uu____5332 ->
                     let uu____5345 = encode_args args_e env in
                     (match uu____5345 with
                      | (args, decls) ->
                          let encode_partial_app ht_opt =
                            let uu____5402 = encode_term head1 env in
                            match uu____5402 with
                            | (head2, decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals, c)
                                     ->
                                     let uu____5466 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____5466 with
                                      | (formals1, rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____5544 ->
                                                 fun uu____5545 ->
                                                   match (uu____5544,
                                                           uu____5545)
                                                   with
                                                   | ((bv, uu____5567),
                                                      (a, uu____5569)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____5587 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____5587
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____5592 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm in
                                          (match uu____5592 with
                                           | (has_type, decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____5607 =
                                                   let uu____5614 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____5623 =
                                                     let uu____5624 =
                                                       let uu____5625 =
                                                         let uu____5626 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____5626 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____5625 in
                                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                       uu____5624 in
                                                   (uu____5614,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____5623) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____5607 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____5645 =
                              FStar_SMTEncoding_Env.lookup_free_var_sym env
                                fv in
                            match uu____5645 with
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
                                   FStar_Syntax_Syntax.pos = uu____5677;
                                   FStar_Syntax_Syntax.vars = uu____5678;_},
                                 uu____5679)
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
                                   FStar_Syntax_Syntax.pos = uu____5690;
                                   FStar_Syntax_Syntax.vars = uu____5691;_},
                                 uu____5692)
                                ->
                                let uu____5697 =
                                  let uu____5698 =
                                    let uu____5703 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____5703
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____5698
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____5697
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____5733 =
                                  let uu____5734 =
                                    let uu____5739 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____5739
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____5734
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____5733
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____5768, (FStar_Util.Inl t1, uu____5770),
                                 uu____5771)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____5820, (FStar_Util.Inr c, uu____5822),
                                 uu____5823)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____5872 -> FStar_Pervasives_Native.None in
                          (match head_type with
                           | FStar_Pervasives_Native.None ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____5899 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.Weak;
                                     FStar_TypeChecker_Normalize.HNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.FStar_SMTEncoding_Env.tcenv
                                     head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____5899 in
                               let uu____5900 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____5900 with
                                | (formals, c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____5916;
                                            FStar_Syntax_Syntax.vars =
                                              uu____5917;_},
                                          uu____5918)
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
                                     | uu____5932 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (FStar_Pervasives_Native.Some
                                                (formals, c))
                                         else
                                           encode_partial_app
                                             FStar_Pervasives_Native.None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) ->
           let uu____5981 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____5981 with
            | (bs1, body1, opening) ->
                let fallback uu____6006 =
                  let f =
                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                      "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding")) in
                  let uu____6013 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____6013, [decl]) in
                let is_impure rc =
                  let uu____6022 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                      env.FStar_SMTEncoding_Env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect in
                  FStar_All.pipe_right uu____6022 Prims.op_Negation in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None ->
                        let uu____6034 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____6034
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1 in
                  let uu____6052 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid in
                  if uu____6052
                  then
                    let uu____6055 = FStar_Syntax_Syntax.mk_Total res_typ in
                    FStar_Pervasives_Native.Some uu____6055
                  else
                    (let uu____6057 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid in
                     if uu____6057
                     then
                       let uu____6060 = FStar_Syntax_Syntax.mk_GTotal res_typ in
                       FStar_Pervasives_Native.Some uu____6060
                     else FStar_Pervasives_Native.None) in
                (match lopt with
                 | FStar_Pervasives_Native.None ->
                     ((let uu____6067 =
                         let uu____6072 =
                           let uu____6073 =
                             FStar_Syntax_Print.term_to_string t0 in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____6073 in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____6072) in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____6067);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____6075 =
                       (is_impure rc) &&
                         (let uu____6077 =
                            FStar_TypeChecker_Env.is_reifiable
                              env.FStar_SMTEncoding_Env.tcenv rc in
                          Prims.op_Negation uu____6077) in
                     if uu____6075
                     then fallback ()
                     else
                       (let cache_size =
                          FStar_Util.smap_size
                            env.FStar_SMTEncoding_Env.cache in
                        let uu____6084 =
                          encode_binders FStar_Pervasives_Native.None bs1 env in
                        match uu____6084 with
                        | (vars, guards, envbody, decls, uu____6109) ->
                            let body2 =
                              let uu____6123 =
                                FStar_TypeChecker_Env.is_reifiable
                                  env.FStar_SMTEncoding_Env.tcenv rc in
                              if uu____6123
                              then
                                FStar_TypeChecker_Util.reify_body
                                  env.FStar_SMTEncoding_Env.tcenv body1
                              else body1 in
                            let uu____6125 = encode_term body2 envbody in
                            (match uu____6125 with
                             | (body3, decls') ->
                                 let uu____6136 =
                                   let uu____6145 = codomain_eff rc in
                                   match uu____6145 with
                                   | FStar_Pervasives_Native.None ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c in
                                       let uu____6164 = encode_term tfun env in
                                       (match uu____6164 with
                                        | (t1, decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1)) in
                                 (match uu____6136 with
                                  | (arrow_t_opt, decls'') ->
                                      let key_body =
                                        let uu____6196 =
                                          let uu____6207 =
                                            let uu____6208 =
                                              let uu____6213 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____6213, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____6208 in
                                          ([], vars, uu____6207) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____6196 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None ->
                                            cvars
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____6225 =
                                              let uu____6228 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1 in
                                              FStar_List.append uu____6228
                                                cvars in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____6225 in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____6247 =
                                        FStar_Util.smap_try_find
                                          env.FStar_SMTEncoding_Env.cache
                                          tkey_hash in
                                      (match uu____6247 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____6255 =
                                             let uu____6256 =
                                               let uu____6263 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1 in
                                               ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                                 uu____6263) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6256 in
                                           (uu____6255,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (FStar_SMTEncoding_Env.use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None ->
                                           let uu____6274 =
                                             is_an_eta_expansion env vars
                                               body3 in
                                           (match uu____6274 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____6285 =
                                                    let uu____6286 =
                                                      FStar_Util.smap_size
                                                        env.FStar_SMTEncoding_Env.cache in
                                                    uu____6286 = cache_size in
                                                  if uu____6285
                                                  then []
                                                  else
                                                    FStar_List.append decls
                                                      (FStar_List.append
                                                         decls' decls'') in
                                                (t1, decls1)
                                            | FStar_Pervasives_Native.None ->
                                                let cvar_sorts =
                                                  FStar_List.map
                                                    FStar_Pervasives_Native.snd
                                                    cvars1 in
                                                let fsym =
                                                  let module_name =
                                                    env.FStar_SMTEncoding_Env.current_module_name in
                                                  let fsym =
                                                    let uu____6302 =
                                                      let uu____6303 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____6303 in
                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                      uu____6302 in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym) in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None) in
                                                let f =
                                                  let uu____6310 =
                                                    let uu____6317 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    (fsym, uu____6317) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____6310 in
                                                let app = mk_Apply f vars in
                                                let typing_f =
                                                  match arrow_t_opt with
                                                  | FStar_Pervasives_Native.None
                                                      -> []
                                                  | FStar_Pervasives_Native.Some
                                                      t1 ->
                                                      let f_has_t =
                                                        FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                          FStar_Pervasives_Native.None
                                                          f t1 in
                                                      let a_name =
                                                        Prims.strcat
                                                          "typing_" fsym in
                                                      let uu____6335 =
                                                        let uu____6336 =
                                                          let uu____6343 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t) in
                                                          (uu____6343,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name) in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____6336 in
                                                      [uu____6335] in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____6356 =
                                                    let uu____6363 =
                                                      let uu____6364 =
                                                        let uu____6375 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____6375) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____6364 in
                                                    (uu____6363,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____6356 in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f]))) in
                                                ((let uu____6392 =
                                                    FStar_SMTEncoding_Env.mk_cache_entry
                                                      env fsym cvar_sorts
                                                      f_decls in
                                                  FStar_Util.smap_add
                                                    env.FStar_SMTEncoding_Env.cache
                                                    tkey_hash uu____6392);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____6395,
             { FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____6396;
               FStar_Syntax_Syntax.lbunivs = uu____6397;
               FStar_Syntax_Syntax.lbtyp = uu____6398;
               FStar_Syntax_Syntax.lbeff = uu____6399;
               FStar_Syntax_Syntax.lbdef = uu____6400;
               FStar_Syntax_Syntax.lbattrs = uu____6401;
               FStar_Syntax_Syntax.lbpos = uu____6402;_}::uu____6403),
            uu____6404)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false,
             { FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
               FStar_Syntax_Syntax.lbunivs = uu____6434;
               FStar_Syntax_Syntax.lbtyp = t1;
               FStar_Syntax_Syntax.lbeff = uu____6436;
               FStar_Syntax_Syntax.lbdef = e1;
               FStar_Syntax_Syntax.lbattrs = uu____6438;
               FStar_Syntax_Syntax.lbpos = uu____6439;_}::[]),
            e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____6463 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions, and their enclosings let bindings (including the top-level let) are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            FStar_Exn.raise FStar_SMTEncoding_Env.Inner_let_rec)
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
                 (FStar_SMTEncoding_Term.term,
                   FStar_SMTEncoding_Term.decls_t)
                   FStar_Pervasives_Native.tuple2)
              ->
              (FStar_SMTEncoding_Term.term, FStar_SMTEncoding_Term.decls_t)
                FStar_Pervasives_Native.tuple2)
  =
  fun x ->
    fun t1 ->
      fun e1 ->
        fun e2 ->
          fun env ->
            fun encode_body ->
              let uu____6533 =
                let uu____6538 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None) in
                encode_term uu____6538 env in
              match uu____6533 with
              | (ee1, decls1) ->
                  let uu____6559 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2 in
                  (match uu____6559 with
                   | (xs, e21) ->
                       let uu____6584 = FStar_List.hd xs in
                       (match uu____6584 with
                        | (x1, uu____6598) ->
                            let env' =
                              FStar_SMTEncoding_Env.push_term_var env x1 ee1 in
                            let uu____6600 = encode_body e21 env' in
                            (match uu____6600 with
                             | (ee2, decls2) ->
                                 (ee2, (FStar_List.append decls1 decls2)))))
and (encode_match :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.branch Prims.list ->
      FStar_SMTEncoding_Term.term ->
        FStar_SMTEncoding_Env.env_t ->
          (FStar_Syntax_Syntax.term ->
             FStar_SMTEncoding_Env.env_t ->
               (FStar_SMTEncoding_Term.term, FStar_SMTEncoding_Term.decls_t)
                 FStar_Pervasives_Native.tuple2)
            ->
            (FStar_SMTEncoding_Term.term, FStar_SMTEncoding_Term.decls_t)
              FStar_Pervasives_Native.tuple2)
  =
  fun e ->
    fun pats ->
      fun default_case ->
        fun env ->
          fun encode_br ->
            let uu____6632 =
              let uu____6639 =
                let uu____6640 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____6640 in
              FStar_SMTEncoding_Env.gen_term_var env uu____6639 in
            match uu____6632 with
            | (scrsym, scr', env1) ->
                let uu____6648 = encode_term e env1 in
                (match uu____6648 with
                 | (scr, decls) ->
                     let uu____6659 =
                       let encode_branch b uu____6688 =
                         match uu____6688 with
                         | (else_case, decls1) ->
                             let uu____6707 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____6707 with
                              | (p, w, br) ->
                                  let uu____6733 = encode_pat env1 p in
                                  (match uu____6733 with
                                   | (env0, pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2 ->
                                                 fun uu____6770 ->
                                                   match uu____6770 with
                                                   | (x, t) ->
                                                       FStar_SMTEncoding_Env.push_term_var
                                                         env2 x t) env1) in
                                       let uu____6777 =
                                         match w with
                                         | FStar_Pervasives_Native.None ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____6799 =
                                               encode_term w1 env2 in
                                             (match uu____6799 with
                                              | (w2, decls2) ->
                                                  let uu____6812 =
                                                    let uu____6813 =
                                                      let uu____6818 =
                                                        let uu____6819 =
                                                          let uu____6824 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____6824) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____6819 in
                                                      (guard, uu____6818) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____6813 in
                                                  (uu____6812, decls2)) in
                                       (match uu____6777 with
                                        | (guard1, decls2) ->
                                            let uu____6837 =
                                              encode_br br env2 in
                                            (match uu____6837 with
                                             | (br1, decls3) ->
                                                 let uu____6850 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____6850,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____6659 with
                      | (match_tm, decls1) ->
                          let uu____6869 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____6869, decls1)))
and (encode_pat :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.pat ->
      (FStar_SMTEncoding_Env.env_t, pattern) FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun pat ->
      (let uu____6909 =
         FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
           FStar_Options.Low in
       if uu____6909
       then
         let uu____6910 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____6910
       else ());
      (let uu____6912 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____6912 with
       | (vars, pat_term) ->
           let uu____6929 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____6982 ->
                     fun v1 ->
                       match uu____6982 with
                       | (env1, vars1) ->
                           let uu____7034 =
                             FStar_SMTEncoding_Env.gen_term_var env1 v1 in
                           (match uu____7034 with
                            | (xx, uu____7056, env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____6929 with
            | (env1, vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____7139 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____7140 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____7141 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____7149 = encode_const c env1 in
                      (match uu____7149 with
                       | (tm, decls) ->
                           ((match decls with
                             | uu____7163::uu____7164 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____7167 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f, args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon
                            env1.FStar_SMTEncoding_Env.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____7190 =
                          FStar_TypeChecker_Env.datacons_of_typ
                            env1.FStar_SMTEncoding_Env.tcenv tc_name in
                        match uu____7190 with
                        | (uu____7197, uu____7198::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____7201 ->
                            FStar_SMTEncoding_Env.mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i ->
                                fun uu____7234 ->
                                  match uu____7234 with
                                  | (arg, uu____7242) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____7248 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____7248)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x, uu____7279) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____7310 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f, args) ->
                      let uu____7333 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i ->
                                fun uu____7377 ->
                                  match uu____7377 with
                                  | (arg, uu____7391) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____7397 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____7397)) in
                      FStar_All.pipe_right uu____7333 FStar_List.flatten in
                let pat_term1 uu____7427 = encode_term pat_term env1 in
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
      (FStar_SMTEncoding_Term.term Prims.list,
        FStar_SMTEncoding_Term.decls_t) FStar_Pervasives_Native.tuple2)
  =
  fun l ->
    fun env ->
      let uu____7437 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____7475 ->
                fun uu____7476 ->
                  match (uu____7475, uu____7476) with
                  | ((tms, decls), (t, uu____7512)) ->
                      let uu____7533 = encode_term t env in
                      (match uu____7533 with
                       | (t1, decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____7437 with | (l1, decls) -> ((FStar_List.rev l1), decls)
and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term, FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t ->
    fun env ->
      let list_elements1 e =
        let uu____7592 = FStar_Syntax_Util.list_elements e in
        match uu____7592 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             []) in
      let one_pat p =
        let uu____7619 =
          let uu____7634 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____7634 FStar_Syntax_Util.head_and_args in
        match uu____7619 with
        | (head1, args) ->
            let uu____7677 =
              let uu____7690 =
                let uu____7691 = FStar_Syntax_Util.un_uinst head1 in
                uu____7691.FStar_Syntax_Syntax.n in
              (uu____7690, args) in
            (match uu____7677 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                (uu____7709, uu____7710)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____7748 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or t1 =
          let uu____7796 =
            let uu____7811 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____7811 FStar_Syntax_Util.head_and_args in
          match uu____7796 with
          | (head1, args) ->
              let uu____7852 =
                let uu____7865 =
                  let uu____7866 = FStar_Syntax_Util.un_uinst head1 in
                  uu____7866.FStar_Syntax_Syntax.n in
                (uu____7865, args) in
              (match uu____7852 with
               | (FStar_Syntax_Syntax.Tm_fvar fv, (e, uu____7883)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____7910 -> FStar_Pervasives_Native.None) in
        match elts with
        | t1::[] ->
            let uu____7936 = smt_pat_or t1 in
            (match uu____7936 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____7956 = list_elements1 e in
                 FStar_All.pipe_right uu____7956
                   (FStar_List.map
                      (fun branch1 ->
                         let uu____7982 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____7982
                           (FStar_List.map one_pat)))
             | uu____8001 ->
                 let uu____8006 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____8006])
        | uu____8047 ->
            let uu____8050 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____8050] in
      let uu____8091 =
        let uu____8114 =
          let uu____8115 = FStar_Syntax_Subst.compress t in
          uu____8115.FStar_Syntax_Syntax.n in
        match uu____8114 with
        | FStar_Syntax_Syntax.Tm_arrow (binders, c) ->
            let uu____8158 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____8158 with
             | (binders1, c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____8209;
                        FStar_Syntax_Syntax.effect_name = uu____8210;
                        FStar_Syntax_Syntax.result_typ = uu____8211;
                        FStar_Syntax_Syntax.effect_args =
                          (pre, uu____8213)::(post, uu____8215)::(pats,
                                                                  uu____8217)::[];
                        FStar_Syntax_Syntax.flags = uu____8218;_}
                      ->
                      let uu____8259 = lemma_pats pats in
                      (binders1, pre, post, uu____8259)
                  | uu____8284 -> failwith "impos"))
        | uu____8307 -> failwith "Impos" in
      match uu____8091 with
      | (binders, pre, post, patterns) ->
          let env1 =
            let uu___76_8367 = env in
            {
              FStar_SMTEncoding_Env.bvar_bindings =
                (uu___76_8367.FStar_SMTEncoding_Env.bvar_bindings);
              FStar_SMTEncoding_Env.fvar_bindings =
                (uu___76_8367.FStar_SMTEncoding_Env.fvar_bindings);
              FStar_SMTEncoding_Env.depth =
                (uu___76_8367.FStar_SMTEncoding_Env.depth);
              FStar_SMTEncoding_Env.tcenv =
                (uu___76_8367.FStar_SMTEncoding_Env.tcenv);
              FStar_SMTEncoding_Env.warn =
                (uu___76_8367.FStar_SMTEncoding_Env.warn);
              FStar_SMTEncoding_Env.cache =
                (uu___76_8367.FStar_SMTEncoding_Env.cache);
              FStar_SMTEncoding_Env.nolabels =
                (uu___76_8367.FStar_SMTEncoding_Env.nolabels);
              FStar_SMTEncoding_Env.use_zfuel_name = true;
              FStar_SMTEncoding_Env.encode_non_total_function_typ =
                (uu___76_8367.FStar_SMTEncoding_Env.encode_non_total_function_typ);
              FStar_SMTEncoding_Env.current_module_name =
                (uu___76_8367.FStar_SMTEncoding_Env.current_module_name);
              FStar_SMTEncoding_Env.encoding_quantifier =
                (uu___76_8367.FStar_SMTEncoding_Env.encoding_quantifier)
            } in
          let uu____8368 =
            encode_binders FStar_Pervasives_Native.None binders env1 in
          (match uu____8368 with
           | (vars, guards, env2, decls, uu____8393) ->
               let uu____8406 = encode_smt_patterns patterns env2 in
               (match uu____8406 with
                | (pats, decls') ->
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post in
                    let env3 =
                      let uu___77_8439 = env2 in
                      {
                        FStar_SMTEncoding_Env.bvar_bindings =
                          (uu___77_8439.FStar_SMTEncoding_Env.bvar_bindings);
                        FStar_SMTEncoding_Env.fvar_bindings =
                          (uu___77_8439.FStar_SMTEncoding_Env.fvar_bindings);
                        FStar_SMTEncoding_Env.depth =
                          (uu___77_8439.FStar_SMTEncoding_Env.depth);
                        FStar_SMTEncoding_Env.tcenv =
                          (uu___77_8439.FStar_SMTEncoding_Env.tcenv);
                        FStar_SMTEncoding_Env.warn =
                          (uu___77_8439.FStar_SMTEncoding_Env.warn);
                        FStar_SMTEncoding_Env.cache =
                          (uu___77_8439.FStar_SMTEncoding_Env.cache);
                        FStar_SMTEncoding_Env.nolabels = true;
                        FStar_SMTEncoding_Env.use_zfuel_name =
                          (uu___77_8439.FStar_SMTEncoding_Env.use_zfuel_name);
                        FStar_SMTEncoding_Env.encode_non_total_function_typ =
                          (uu___77_8439.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                        FStar_SMTEncoding_Env.current_module_name =
                          (uu___77_8439.FStar_SMTEncoding_Env.current_module_name);
                        FStar_SMTEncoding_Env.encoding_quantifier =
                          (uu___77_8439.FStar_SMTEncoding_Env.encoding_quantifier)
                      } in
                    let uu____8440 =
                      let uu____8445 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____8445 env3 in
                    (match uu____8440 with
                     | (pre1, decls'') ->
                         let uu____8452 =
                           let uu____8457 = FStar_Syntax_Util.unmeta post1 in
                           encode_formula uu____8457 env3 in
                         (match uu____8452 with
                          | (post2, decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append decls'
                                     (FStar_List.append decls'' decls''')) in
                              let uu____8467 =
                                let uu____8468 =
                                  let uu____8479 =
                                    let uu____8480 =
                                      let uu____8485 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____8485, post2) in
                                    FStar_SMTEncoding_Util.mkImp uu____8480 in
                                  (pats, vars, uu____8479) in
                                FStar_SMTEncoding_Util.mkForall uu____8468 in
                              (uu____8467, decls1)))))
and (encode_smt_patterns :
  FStar_Syntax_Syntax.arg Prims.list Prims.list ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term Prims.list Prims.list,
        FStar_SMTEncoding_Term.decl Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun pats_l ->
    fun env ->
      let env1 =
        let uu___78_8511 = env in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___78_8511.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___78_8511.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___78_8511.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___78_8511.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___78_8511.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.cache =
            (uu___78_8511.FStar_SMTEncoding_Env.cache);
          FStar_SMTEncoding_Env.nolabels =
            (uu___78_8511.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___78_8511.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___78_8511.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___78_8511.FStar_SMTEncoding_Env.encoding_quantifier)
        } in
      let encode_smt_pattern t =
        let uu____8524 = FStar_Syntax_Util.head_and_args t in
        match uu____8524 with
        | (head1, args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                uu____8583::(x, uu____8585)::(t1, uu____8587)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____8634 = encode_term x env1 in
                 (match uu____8634 with
                  | (x1, decls) ->
                      let uu____8647 = encode_term t1 env1 in
                      (match uu____8647 with
                       | (t2, decls') ->
                           let uu____8660 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t2 in
                           (uu____8660, (FStar_List.append decls decls'))))
             | uu____8663 -> encode_term t env1) in
      FStar_List.fold_right
        (fun pats ->
           fun uu____8700 ->
             match uu____8700 with
             | (pats_l1, decls) ->
                 let uu____8741 =
                   FStar_List.fold_right
                     (fun uu____8771 ->
                        fun uu____8772 ->
                          match (uu____8771, uu____8772) with
                          | ((p, uu____8806), (pats1, decls1)) ->
                              let uu____8829 = encode_smt_pattern p in
                              (match uu____8829 with
                               | (t, d) ->
                                   ((t :: pats1),
                                     (FStar_List.append d decls1)))) pats
                     ([], decls) in
                 (match uu____8741 with
                  | (pats1, decls1) -> ((pats1 :: pats_l1), decls1))) pats_l
        ([], [])
and (encode_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term, FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun phi ->
    fun env ->
      let debug1 phi1 =
        let uu____8906 =
          FStar_All.pipe_left
            (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____8906
        then
          let uu____8907 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____8908 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____8907 uu____8908
        else () in
      let enc f r l =
        let uu____8947 =
          FStar_Util.fold_map
            (fun decls ->
               fun x ->
                 let uu____8975 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____8975 with
                 | (t, decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____8947 with
        | (decls, args) ->
            let uu____9004 =
              let uu___79_9005 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___79_9005.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___79_9005.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____9004, decls) in
      let const_op f r uu____9042 = let uu____9055 = f r in (uu____9055, []) in
      let un_op f l =
        let uu____9078 = FStar_List.hd l in FStar_All.pipe_left f uu____9078 in
      let bin_op f uu___70_9098 =
        match uu___70_9098 with
        | t1::t2::[] -> f (t1, t2)
        | uu____9109 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____9149 =
          FStar_Util.fold_map
            (fun decls ->
               fun uu____9172 ->
                 match uu____9172 with
                 | (t, uu____9186) ->
                     let uu____9187 = encode_formula t env in
                     (match uu____9187 with
                      | (phi1, decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____9149 with
        | (decls, phis) ->
            let uu____9216 =
              let uu___80_9217 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___80_9217.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___80_9217.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____9216, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____9282 ->
               match uu____9282 with
               | (a, q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____9301) -> false
                    | uu____9302 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____9317 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____9317
        else
          (let uu____9331 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____9331 r rf) in
      let mk_imp1 r uu___71_9366 =
        match uu___71_9366 with
        | (lhs, uu____9372)::(rhs, uu____9374)::[] ->
            let uu____9401 = encode_formula rhs env in
            (match uu____9401 with
             | (l1, decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp, uu____9416) ->
                      (l1, decls1)
                  | uu____9421 ->
                      let uu____9422 = encode_formula lhs env in
                      (match uu____9422 with
                       | (l2, decls2) ->
                           let uu____9433 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____9433, (FStar_List.append decls1 decls2)))))
        | uu____9436 -> failwith "impossible" in
      let mk_ite r uu___72_9463 =
        match uu___72_9463 with
        | (guard, uu____9469)::(_then, uu____9471)::(_else, uu____9473)::[]
            ->
            let uu____9510 = encode_formula guard env in
            (match uu____9510 with
             | (g, decls1) ->
                 let uu____9521 = encode_formula _then env in
                 (match uu____9521 with
                  | (t, decls2) ->
                      let uu____9532 = encode_formula _else env in
                      (match uu____9532 with
                       | (e, decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____9546 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____9575 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____9575 in
      let connectives =
        let uu____9595 =
          let uu____9610 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____9610) in
        let uu____9633 =
          let uu____9650 =
            let uu____9665 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____9665) in
          let uu____9688 =
            let uu____9705 =
              let uu____9723 =
                let uu____9738 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____9738) in
              let uu____9761 =
                let uu____9778 =
                  let uu____9796 =
                    let uu____9811 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____9811) in
                  [uu____9796;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____9778 in
              uu____9723 :: uu____9761 in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____9705 in
          uu____9650 :: uu____9688 in
        uu____9595 :: uu____9633 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) ->
            let uu____10178 = encode_formula phi' env in
            (match uu____10178 with
             | (phi2, decls) ->
                 let uu____10189 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____10189, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____10190 ->
            let uu____10197 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____10197 env
        | FStar_Syntax_Syntax.Tm_match (e, pats) ->
            let uu____10236 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____10236 with | (t, decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false,
              { FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____10248;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____10250;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____10252;
                FStar_Syntax_Syntax.lbpos = uu____10253;_}::[]),
             e2)
            ->
            let uu____10277 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____10277 with | (t, decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1, args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                uu____10324::(x, uu____10326)::(t, uu____10328)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____10375 = encode_term x env in
                 (match uu____10375 with
                  | (x1, decls) ->
                      let uu____10386 = encode_term t env in
                      (match uu____10386 with
                       | (t1, decls') ->
                           let uu____10397 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____10397, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                (r, uu____10402)::(msg, uu____10404)::(phi2, uu____10406)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____10451 =
                   let uu____10456 =
                     let uu____10457 = FStar_Syntax_Subst.compress r in
                     uu____10457.FStar_Syntax_Syntax.n in
                   let uu____10460 =
                     let uu____10461 = FStar_Syntax_Subst.compress msg in
                     uu____10461.FStar_Syntax_Syntax.n in
                   (uu____10456, uu____10460) in
                 (match uu____10451 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1), FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s, uu____10470))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1 in
                      fallback phi3
                  | uu____10476 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv, (t, uu____10483)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____10508 when head_redex env head2 ->
                 let uu____10521 = whnf env phi1 in
                 encode_formula uu____10521 env
             | uu____10522 ->
                 let uu____10535 = encode_term phi1 env in
                 (match uu____10535 with
                  | (tt, decls) ->
                      let uu____10546 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___81_10549 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___81_10549.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___81_10549.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____10546, decls)))
        | uu____10550 ->
            let uu____10551 = encode_term phi1 env in
            (match uu____10551 with
             | (tt, decls) ->
                 let uu____10562 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___82_10565 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___82_10565.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___82_10565.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____10562, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____10609 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____10609 with
        | (vars, guards, env2, decls, uu____10648) ->
            let uu____10661 = encode_smt_patterns ps env2 in
            (match uu____10661 with
             | (pats, decls') ->
                 let uu____10704 = encode_formula body env2 in
                 (match uu____10704 with
                  | (body1, decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf, p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____10736;
                             FStar_SMTEncoding_Term.rng = uu____10737;_}::[])::[]
                            when
                            let uu____10752 =
                              FStar_Ident.text_of_lid
                                FStar_Parser_Const.guard_free in
                            uu____10752 = gf -> []
                        | uu____10753 -> guards in
                      let uu____10758 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____10758, body1,
                        (FStar_List.append decls
                           (FStar_List.append decls' decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let uu____10769 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____10769 with
       | FStar_Pervasives_Native.None -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op, arms))
           ->
           let uu____10778 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____10844 ->
                     match uu____10844 with
                     | (l, uu____10858) -> FStar_Ident.lid_equals op l)) in
           (match uu____10778 with
            | FStar_Pervasives_Native.None -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____10897, f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars, pats, body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____10943 = encode_q_body env vars pats body in
             match uu____10943 with
             | (vars1, pats1, guard, body1, decls) ->
                 let tm =
                   let uu____10988 =
                     let uu____10999 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____10999) in
                   FStar_SMTEncoding_Term.mkForall uu____10988
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars, pats, body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____11018 = encode_q_body env vars pats body in
             match uu____11018 with
             | (vars1, pats1, guard, body1, decls) ->
                 let uu____11062 =
                   let uu____11063 =
                     let uu____11074 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____11074) in
                   FStar_SMTEncoding_Term.mkExists uu____11063
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____11062, decls))))