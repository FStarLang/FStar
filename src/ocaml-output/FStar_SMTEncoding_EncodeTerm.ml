open Prims
let mkForall_fuel' :
  'Auu____9 .
    FStar_Range.range ->
      'Auu____9 ->
        (FStar_SMTEncoding_Term.pat Prims.list Prims.list,FStar_SMTEncoding_Term.fvs,
          FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
          FStar_SMTEncoding_Term.term
  =
  fun r  ->
    fun n1  ->
      fun uu____34  ->
        match uu____34 with
        | (pats,vars,body) ->
            let fallback uu____61 =
              FStar_SMTEncoding_Term.mkForall r (pats, vars, body)  in
            let uu____66 = FStar_Options.unthrottle_inductives ()  in
            if uu____66
            then fallback ()
            else
              (let uu____68 =
                 FStar_SMTEncoding_Env.fresh_fvar "f"
                   FStar_SMTEncoding_Term.Fuel_sort
                  in
               match uu____68 with
               | (fsym,fterm) ->
                   let add_fuel1 tms =
                     FStar_All.pipe_right tms
                       (FStar_List.map
                          (fun p  ->
                             match p.FStar_SMTEncoding_Term.tm with
                             | FStar_SMTEncoding_Term.App
                                 (FStar_SMTEncoding_Term.Var "HasType",args)
                                 ->
                                 FStar_SMTEncoding_Util.mkApp
                                   ("HasTypeFuel", (fterm :: args))
                             | uu____101 -> p))
                      in
                   let pats1 = FStar_List.map add_fuel1 pats  in
                   let body1 =
                     match body.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App
                         (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                         let guard1 =
                           match guard.FStar_SMTEncoding_Term.tm with
                           | FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.And ,guards) ->
                               let uu____122 = add_fuel1 guards  in
                               FStar_SMTEncoding_Util.mk_and_l uu____122
                           | uu____125 ->
                               let uu____126 = add_fuel1 [guard]  in
                               FStar_All.pipe_right uu____126 FStar_List.hd
                            in
                         FStar_SMTEncoding_Util.mkImp (guard1, body')
                     | uu____131 -> body  in
                   let vars1 = (fsym, FStar_SMTEncoding_Term.Fuel_sort) ::
                     vars  in
                   FStar_SMTEncoding_Term.mkForall r (pats1, vars1, body1))
  
let (mkForall_fuel :
  FStar_Range.range ->
    (FStar_SMTEncoding_Term.pat Prims.list Prims.list,FStar_SMTEncoding_Term.fvs,
      FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
      FStar_SMTEncoding_Term.term)
  = fun r  -> mkForall_fuel' r (Prims.parse_int "1") 
let (head_normal :
  FStar_SMTEncoding_Env.env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow uu____176 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____191 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____198 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____199 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____212 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____231 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____233 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____233 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____251;
             FStar_Syntax_Syntax.vars = uu____252;_},uu____253)
          ->
          let uu____278 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____278 FStar_Option.isNone
      | uu____295 -> false
  
let (head_redex :
  FStar_SMTEncoding_Env.env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____306 =
        let uu____307 = FStar_Syntax_Util.un_uinst t  in
        uu____307.FStar_Syntax_Syntax.n  in
      match uu____306 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____310,uu____311,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___343_336  ->
                  match uu___343_336 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____337 -> false) rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____339 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____339 FStar_Option.isSome
      | uu____356 -> false
  
let (whnf :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____367 = head_normal env t  in
      if uu____367
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
  fun env  ->
    fun t  ->
      FStar_TypeChecker_Normalize.normalize
        [FStar_TypeChecker_Normalize.Beta;
        FStar_TypeChecker_Normalize.Exclude FStar_TypeChecker_Normalize.Zeta;
        FStar_TypeChecker_Normalize.Eager_unfolding;
        FStar_TypeChecker_Normalize.EraseUniverses]
        env.FStar_SMTEncoding_Env.tcenv t
  
let (trivial_post : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____384 =
      let uu____385 = FStar_Syntax_Syntax.null_binder t  in [uu____385]  in
    let uu____404 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    FStar_Syntax_Util.abs uu____384 uu____404 FStar_Pervasives_Native.None
  
let (mk_Apply :
  FStar_SMTEncoding_Term.term ->
    (Prims.string,FStar_SMTEncoding_Term.sort) FStar_Pervasives_Native.tuple2
      Prims.list -> FStar_SMTEncoding_Term.term)
  =
  fun e  ->
    fun vars  ->
      FStar_All.pipe_right vars
        (FStar_List.fold_left
           (fun out  ->
              fun var  ->
                match FStar_Pervasives_Native.snd var with
                | FStar_SMTEncoding_Term.Fuel_sort  ->
                    let uu____448 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____448
                | s ->
                    let uu____451 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____451) e)
  
let (mk_Apply_args :
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term)
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
  
let raise_arity_mismatch :
  'a . Prims.string -> Prims.int -> Prims.int -> FStar_Range.range -> 'a =
  fun head1  ->
    fun arity  ->
      fun n_args  ->
        fun rng  ->
          let uu____499 =
            let uu____504 =
              let uu____505 = FStar_Util.string_of_int arity  in
              let uu____506 = FStar_Util.string_of_int n_args  in
              FStar_Util.format3
                "Head symbol %s expects at least %s arguments; got only %s"
                head1 uu____505 uu____506
               in
            (FStar_Errors.Fatal_SMTEncodingArityMismatch, uu____504)  in
          FStar_Errors.raise_error uu____499 rng
  
let (maybe_curry_app :
  FStar_Range.range ->
    FStar_SMTEncoding_Term.op ->
      Prims.int ->
        FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term)
  =
  fun rng  ->
    fun head1  ->
      fun arity  ->
        fun args  ->
          let n_args = FStar_List.length args  in
          if n_args = arity
          then FStar_SMTEncoding_Util.mkApp' (head1, args)
          else
            if n_args > arity
            then
              (let uu____545 = FStar_Util.first_N arity args  in
               match uu____545 with
               | (args1,rest) ->
                   let head2 = FStar_SMTEncoding_Util.mkApp' (head1, args1)
                      in
                   mk_Apply_args head2 rest)
            else
              (let uu____568 = FStar_SMTEncoding_Term.op_to_string head1  in
               raise_arity_mismatch uu____568 arity n_args rng)
  
let (is_app : FStar_SMTEncoding_Term.op -> Prims.bool) =
  fun uu___344_577  ->
    match uu___344_577 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____578 -> false
  
let (is_an_eta_expansion :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fv Prims.list ->
      FStar_SMTEncoding_Term.term ->
        FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun vars  ->
      fun body  ->
        let rec check_partial_applications t xs =
          match ((t.FStar_SMTEncoding_Term.tm), xs) with
          | (FStar_SMTEncoding_Term.App
             (app,f::{
                       FStar_SMTEncoding_Term.tm =
                         FStar_SMTEncoding_Term.FreeV y;
                       FStar_SMTEncoding_Term.freevars = uu____624;
                       FStar_SMTEncoding_Term.rng = uu____625;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____648) ->
              let uu____657 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____668 -> false) args (FStar_List.rev xs))
                 in
              if uu____657
              then FStar_SMTEncoding_Env.tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____672,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t  in
              let uu____676 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____682 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars
                           in
                        Prims.op_Negation uu____682))
                 in
              if uu____676
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____686 -> FStar_Pervasives_Native.None  in
        check_partial_applications body (FStar_List.rev vars)
  
let check_pattern_vars :
  'Auu____703 'Auu____704 .
    FStar_SMTEncoding_Env.env_t ->
      (FStar_Syntax_Syntax.bv,'Auu____703) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____704) FStar_Pervasives_Native.tuple2
          Prims.list -> unit
  =
  fun env  ->
    fun vars  ->
      fun pats  ->
        let pats1 =
          FStar_All.pipe_right pats
            (FStar_List.map
               (fun uu____762  ->
                  match uu____762 with
                  | (x,uu____768) ->
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                        FStar_TypeChecker_Normalize.EraseUniverses]
                        env.FStar_SMTEncoding_Env.tcenv x))
           in
        match pats1 with
        | [] -> ()
        | hd1::tl1 ->
            let pat_vars =
              let uu____776 = FStar_Syntax_Free.names hd1  in
              FStar_List.fold_left
                (fun out  ->
                   fun x  ->
                     let uu____788 = FStar_Syntax_Free.names x  in
                     FStar_Util.set_union out uu____788) uu____776 tl1
               in
            let uu____791 =
              FStar_All.pipe_right vars
                (FStar_Util.find_opt
                   (fun uu____818  ->
                      match uu____818 with
                      | (b,uu____824) ->
                          let uu____825 = FStar_Util.set_mem b pat_vars  in
                          Prims.op_Negation uu____825))
               in
            (match uu____791 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some (x,uu____831) ->
                 let pos =
                   FStar_List.fold_left
                     (fun out  ->
                        fun t  ->
                          FStar_Range.union_ranges out
                            t.FStar_Syntax_Syntax.pos)
                     hd1.FStar_Syntax_Syntax.pos tl1
                    in
                 let uu____845 =
                   let uu____850 =
                     let uu____851 = FStar_Syntax_Print.bv_to_string x  in
                     FStar_Util.format1
                       "SMT pattern misses at least one bound variable: %s"
                       uu____851
                      in
                   (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                     uu____850)
                    in
                 FStar_Errors.log_issue pos uu____845)
  
type label =
  (FStar_SMTEncoding_Term.fv,Prims.string,FStar_Range.range)
    FStar_Pervasives_Native.tuple3
type labels = label Prims.list
type pattern =
  {
  pat_vars:
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.fv)
      FStar_Pervasives_Native.tuple2 Prims.list
    ;
  pat_term:
    unit ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
    ;
  guard: FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term ;
  projections:
    FStar_SMTEncoding_Term.term ->
      (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2 Prims.list
    }
let (__proj__Mkpattern__item__pat_vars :
  pattern ->
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.fv)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__pat_vars
  
let (__proj__Mkpattern__item__pat_term :
  pattern ->
    unit ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__pat_term
  
let (__proj__Mkpattern__item__guard :
  pattern -> FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term) =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__guard
  
let (__proj__Mkpattern__item__projections :
  pattern ->
    FStar_SMTEncoding_Term.term ->
      (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__projections
  
let (as_function_typ :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t0  ->
      let rec aux norm1 t =
        let t1 = FStar_Syntax_Subst.compress t  in
        match t1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow uu____1126 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____1141 ->
            let uu____1148 = FStar_Syntax_Util.unrefine t1  in
            aux true uu____1148
        | uu____1149 ->
            if norm1
            then let uu____1150 = whnf env t1  in aux false uu____1150
            else
              (let uu____1152 =
                 let uu____1153 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let uu____1154 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____1153 uu____1154
                  in
               failwith uu____1152)
         in
      aux true t0
  
let rec (curried_arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2)
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k  in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        FStar_Syntax_Subst.open_comp bs c
    | FStar_Syntax_Syntax.Tm_refine (bv,uu____1192) ->
        curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort
    | uu____1197 ->
        let uu____1198 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____1198)
  
let is_arithmetic_primitive :
  'Auu____1211 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____1211 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1233::uu____1234::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1238::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____1241 -> false
  
let (isInteger : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____1264 -> false
  
let (getInteger : FStar_Syntax_Syntax.term' -> Prims.int) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____1281 -> failwith "Expected an Integer term"
  
let is_BitVector_primitive :
  'Auu____1288 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1288)
        FStar_Pervasives_Native.tuple2 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____1329)::uu____1330::uu____1331::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____1382)::uu____1383::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____1420 -> false
  
let rec (encode_const :
  FStar_Const.sconst ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun c  ->
    fun env  ->
      match c with
      | FStar_Const.Const_unit  -> (FStar_SMTEncoding_Term.mk_Term_unit, [])
      | FStar_Const.Const_bool (true ) ->
          let uu____1735 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue  in
          (uu____1735, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____1736 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse  in
          (uu____1736, [])
      | FStar_Const.Const_char c1 ->
          let uu____1739 =
            let uu____1740 =
              let uu____1747 =
                let uu____1750 =
                  let uu____1751 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1)
                     in
                  FStar_SMTEncoding_Term.boxInt uu____1751  in
                [uu____1750]  in
              ("FStar.Char.__char_of_int", uu____1747)  in
            FStar_SMTEncoding_Util.mkApp uu____1740  in
          (uu____1739, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____1765 =
            let uu____1766 = FStar_SMTEncoding_Util.mkInteger i  in
            FStar_SMTEncoding_Term.boxInt uu____1766  in
          (uu____1765, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.FStar_SMTEncoding_Env.tcenv).FStar_TypeChecker_Env.dsenv
              repr sw FStar_Range.dummyRange
             in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____1785) ->
          let uu____1786 =
            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.string_const s
             in
          (uu____1786, [])
      | FStar_Const.Const_range uu____1787 ->
          let uu____1788 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          (uu____1788, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | c1 ->
          let uu____1790 =
            let uu____1791 = FStar_Syntax_Print.const_to_string c1  in
            FStar_Util.format1 "Unhandled constant: %s" uu____1791  in
          failwith uu____1790

and (encode_binders :
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.binders ->
      FStar_SMTEncoding_Env.env_t ->
        (FStar_SMTEncoding_Term.fv Prims.list,FStar_SMTEncoding_Term.term
                                                Prims.list,FStar_SMTEncoding_Env.env_t,
          FStar_SMTEncoding_Term.decls_t,FStar_Syntax_Syntax.bv Prims.list)
          FStar_Pervasives_Native.tuple5)
  =
  fun fuel_opt  ->
    fun bs  ->
      fun env  ->
        (let uu____1818 =
           FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
             FStar_Options.Low
            in
         if uu____1818
         then
           let uu____1819 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____1819
         else ());
        (let uu____1821 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____1915  ->
                   fun b  ->
                     match uu____1915 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____1996 =
                           let x =
                             FStar_SMTEncoding_Env.unmangle
                               (FStar_Pervasives_Native.fst b)
                              in
                           let uu____2016 =
                             FStar_SMTEncoding_Env.gen_term_var env1 x  in
                           match uu____2016 with
                           | (xxsym,xx,env') ->
                               let uu____2042 =
                                 let uu____2047 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____2047 env1 xx
                                  in
                               (match uu____2042 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x))
                            in
                         (match uu____1996 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____1821 with
         | (vars,guards,env1,decls,names1) ->
             ((FStar_List.rev vars), (FStar_List.rev guards), env1, decls,
               (FStar_List.rev names1)))

and (encode_term_pred :
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.typ ->
      FStar_SMTEncoding_Env.env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
            FStar_Pervasives_Native.tuple2)
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____2208 = encode_term t env  in
          match uu____2208 with
          | (t1,decls) ->
              let uu____2219 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____2219, decls)

and (encode_term_pred' :
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.typ ->
      FStar_SMTEncoding_Env.env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
            FStar_Pervasives_Native.tuple2)
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____2230 = encode_term t env  in
          match uu____2230 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____2245 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____2245, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____2247 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____2247, decls))

and (encode_arith_term :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____2253 = encode_args args_e env  in
        match uu____2253 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____2272 -> failwith "Impossible"  in
            let unary arg_tms1 =
              let uu____2283 = FStar_List.hd arg_tms1  in
              FStar_SMTEncoding_Term.unboxInt uu____2283  in
            let binary arg_tms1 =
              let uu____2298 =
                let uu____2299 = FStar_List.hd arg_tms1  in
                FStar_SMTEncoding_Term.unboxInt uu____2299  in
              let uu____2300 =
                let uu____2301 =
                  let uu____2302 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____2302  in
                FStar_SMTEncoding_Term.unboxInt uu____2301  in
              (uu____2298, uu____2300)  in
            let mk_default uu____2310 =
              let uu____2311 =
                FStar_SMTEncoding_Env.lookup_free_var_sym env
                  head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____2311 with
              | (fname,fuel_args,arity) ->
                  let args = FStar_List.append fuel_args arg_tms  in
                  maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity
                    args
               in
            let mk_l op mk_args ts =
              let uu____2373 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____2373
              then
                let uu____2374 =
                  let uu____2375 = mk_args ts  in op uu____2375  in
                FStar_All.pipe_right uu____2374 FStar_SMTEncoding_Term.boxInt
              else mk_default ()  in
            let mk_nl nm op ts =
              let uu____2410 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____2410
              then
                let uu____2411 = binary ts  in
                match uu____2411 with
                | (t1,t2) ->
                    let uu____2418 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____2418
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____2422 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____2422
                 then
                   let uu____2423 =
                     let uu____2424 = binary ts  in op uu____2424  in
                   FStar_All.pipe_right uu____2423
                     FStar_SMTEncoding_Term.boxInt
                 else mk_default ())
               in
            let add1 = mk_l FStar_SMTEncoding_Util.mkAdd binary  in
            let sub1 = mk_l FStar_SMTEncoding_Util.mkSub binary  in
            let minus = mk_l FStar_SMTEncoding_Util.mkMinus unary  in
            let mul1 = mk_nl "_mul" FStar_SMTEncoding_Util.mkMul  in
            let div1 = mk_nl "_div" FStar_SMTEncoding_Util.mkDiv  in
            let modulus = mk_nl "_mod" FStar_SMTEncoding_Util.mkMod  in
            let ops =
              [(FStar_Parser_Const.op_Addition, add1);
              (FStar_Parser_Const.op_Subtraction, sub1);
              (FStar_Parser_Const.op_Multiply, mul1);
              (FStar_Parser_Const.op_Division, div1);
              (FStar_Parser_Const.op_Modulus, modulus);
              (FStar_Parser_Const.op_Minus, minus)]  in
            let uu____2585 =
              let uu____2595 =
                FStar_List.tryFind
                  (fun uu____2619  ->
                     match uu____2619 with
                     | (l,uu____2629) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____2595 FStar_Util.must  in
            (match uu____2585 with
             | (uu____2673,op) ->
                 let uu____2685 = op arg_tms  in (uu____2685, decls))

and (encode_BitVector_term :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.arg Prims.list ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____2693 = FStar_List.hd args_e  in
        match uu____2693 with
        | (tm_sz,uu____2701) ->
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let uu____2715 =
                FStar_Util.smap_try_find env.FStar_SMTEncoding_Env.cache
                  sz_key
                 in
              match uu____2715 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None  ->
                  let t_decls1 = FStar_SMTEncoding_Term.mkBvConstructor sz
                     in
                  ((let uu____2723 =
                      FStar_SMTEncoding_Env.mk_cache_entry env "" [] []  in
                    FStar_Util.smap_add env.FStar_SMTEncoding_Env.cache
                      sz_key uu____2723);
                   t_decls1)
               in
            let uu____2724 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____2748::(sz_arg,uu____2750)::uu____2751::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____2818 =
                    let uu____2819 = FStar_List.tail args_e  in
                    FStar_List.tail uu____2819  in
                  let uu____2822 =
                    let uu____2825 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____2825  in
                  (uu____2818, uu____2822)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____2829::(sz_arg,uu____2831)::uu____2832::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____2899 =
                    let uu____2900 = FStar_Syntax_Print.term_to_string sz_arg
                       in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____2900
                     in
                  failwith uu____2899
              | uu____2907 ->
                  let uu____2922 = FStar_List.tail args_e  in
                  (uu____2922, FStar_Pervasives_Native.None)
               in
            (match uu____2724 with
             | (arg_tms,ext_sz) ->
                 let uu____2937 = encode_args arg_tms env  in
                 (match uu____2937 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____2958 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____2969 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____2969  in
                      let unary_arith arg_tms2 =
                        let uu____2980 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____2980  in
                      let binary arg_tms2 =
                        let uu____2995 =
                          let uu____2996 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____2996
                           in
                        let uu____2997 =
                          let uu____2998 =
                            let uu____2999 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____2999  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____2998
                           in
                        (uu____2995, uu____2997)  in
                      let binary_arith arg_tms2 =
                        let uu____3016 =
                          let uu____3017 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3017
                           in
                        let uu____3018 =
                          let uu____3019 =
                            let uu____3020 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____3020  in
                          FStar_SMTEncoding_Term.unboxInt uu____3019  in
                        (uu____3016, uu____3018)  in
                      let mk_bv op mk_args resBox ts =
                        let uu____3078 =
                          let uu____3079 = mk_args ts  in op uu____3079  in
                        FStar_All.pipe_right uu____3078 resBox  in
                      let bv_and =
                        mk_bv FStar_SMTEncoding_Util.mkBvAnd binary
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_xor =
                        mk_bv FStar_SMTEncoding_Util.mkBvXor binary
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_or =
                        mk_bv FStar_SMTEncoding_Util.mkBvOr binary
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_add =
                        mk_bv FStar_SMTEncoding_Util.mkBvAdd binary
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_sub =
                        mk_bv FStar_SMTEncoding_Util.mkBvSub binary
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_shl =
                        mk_bv (FStar_SMTEncoding_Util.mkBvShl sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_shr =
                        mk_bv (FStar_SMTEncoding_Util.mkBvShr sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_udiv =
                        mk_bv (FStar_SMTEncoding_Util.mkBvUdiv sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_mod =
                        mk_bv (FStar_SMTEncoding_Util.mkBvMod sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_mul =
                        mk_bv (FStar_SMTEncoding_Util.mkBvMul sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_ult =
                        mk_bv FStar_SMTEncoding_Util.mkBvUlt binary
                          FStar_SMTEncoding_Term.boxBool
                         in
                      let bv_uext arg_tms2 =
                        let uu____3211 =
                          let uu____3216 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____3216  in
                        let uu____3218 =
                          let uu____3223 =
                            let uu____3224 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____3224  in
                          FStar_SMTEncoding_Term.boxBitVec uu____3223  in
                        mk_bv uu____3211 unary uu____3218 arg_tms2  in
                      let to_int1 =
                        mk_bv FStar_SMTEncoding_Util.mkBvToNat unary
                          FStar_SMTEncoding_Term.boxInt
                         in
                      let bv_to =
                        mk_bv (FStar_SMTEncoding_Util.mkNatToBv sz)
                          unary_arith (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
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
                        (FStar_Parser_Const.nat_to_bv_lid, bv_to)]  in
                      let uu____3457 =
                        let uu____3467 =
                          FStar_List.tryFind
                            (fun uu____3491  ->
                               match uu____3491 with
                               | (l,uu____3501) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____3467 FStar_Util.must  in
                      (match uu____3457 with
                       | (uu____3547,op) ->
                           let uu____3559 = op arg_tms1  in
                           (uu____3559, (FStar_List.append sz_decls decls)))))

and (encode_deeply_embedded_quantifier :
  FStar_Syntax_Syntax.term ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let env1 =
        let uu___348_3569 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___348_3569.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___348_3569.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___348_3569.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___348_3569.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___348_3569.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.cache =
            (uu___348_3569.FStar_SMTEncoding_Env.cache);
          FStar_SMTEncoding_Env.nolabels =
            (uu___348_3569.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name =
            (uu___348_3569.FStar_SMTEncoding_Env.use_zfuel_name);
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___348_3569.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___348_3569.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier = true
        }  in
      let uu____3570 = encode_term t env1  in
      match uu____3570 with
      | (tm,decls) ->
          let vars = FStar_SMTEncoding_Term.free_variables tm  in
          let valid_tm = FStar_SMTEncoding_Term.mk_Valid tm  in
          let key =
            FStar_SMTEncoding_Term.mkForall t.FStar_Syntax_Syntax.pos
              ([], vars, valid_tm)
             in
          let tkey_hash = FStar_SMTEncoding_Term.hash_of_term key  in
          let uu____3591 =
            FStar_Util.smap_try_find env1.FStar_SMTEncoding_Env.cache
              tkey_hash
             in
          (match uu____3591 with
           | FStar_Pervasives_Native.Some uu____3598 -> (tm, decls)
           | uu____3599 ->
               (match tm.FStar_SMTEncoding_Term.tm with
                | FStar_SMTEncoding_Term.App
                    (uu____3606,{
                                  FStar_SMTEncoding_Term.tm =
                                    FStar_SMTEncoding_Term.FreeV uu____3607;
                                  FStar_SMTEncoding_Term.freevars =
                                    uu____3608;
                                  FStar_SMTEncoding_Term.rng = uu____3609;_}::
                     {
                       FStar_SMTEncoding_Term.tm =
                         FStar_SMTEncoding_Term.FreeV uu____3610;
                       FStar_SMTEncoding_Term.freevars = uu____3611;
                       FStar_SMTEncoding_Term.rng = uu____3612;_}::[])
                    ->
                    (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                       (FStar_Errors.Warning_QuantifierWithoutPattern,
                         "Not encoding deeply embedded, unguarded quantifier to SMT");
                     (tm, decls))
                | uu____3640 ->
                    let uu____3641 = encode_formula t env1  in
                    (match uu____3641 with
                     | (phi,decls') ->
                         let interp =
                           match vars with
                           | [] ->
                               let uu____3657 =
                                 let uu____3662 =
                                   FStar_SMTEncoding_Term.mk_Valid tm  in
                                 (uu____3662, phi)  in
                               FStar_SMTEncoding_Util.mkIff uu____3657
                           | uu____3663 ->
                               let uu____3664 =
                                 let uu____3675 =
                                   let uu____3676 =
                                     let uu____3681 =
                                       FStar_SMTEncoding_Term.mk_Valid tm  in
                                     (uu____3681, phi)  in
                                   FStar_SMTEncoding_Util.mkIff uu____3676
                                    in
                                 ([[valid_tm]], vars, uu____3675)  in
                               FStar_SMTEncoding_Term.mkForall
                                 t.FStar_Syntax_Syntax.pos uu____3664
                            in
                         let ax =
                           let uu____3691 =
                             let uu____3698 =
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 "l_quant_interp"
                                in
                             (interp,
                               (FStar_Pervasives_Native.Some
                                  "Interpretation of deeply embedded quantifier"),
                               uu____3698)
                              in
                           FStar_SMTEncoding_Util.mkAssume uu____3691  in
                         ((let uu____3700 =
                             FStar_SMTEncoding_Env.mk_cache_entry env1 "" []
                               [ax]
                              in
                           FStar_Util.smap_add
                             env1.FStar_SMTEncoding_Env.cache tkey_hash
                             uu____3700);
                          (tm,
                            (FStar_List.append decls
                               (FStar_List.append decls' [ax])))))))

and (encode_term :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____3709 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____3709
       then
         let uu____3710 = FStar_Syntax_Print.tag_of_term t  in
         let uu____3711 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____3712 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____3710 uu____3711
           uu____3712
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____3718 ->
           let uu____3741 =
             let uu____3742 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____3743 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____3744 = FStar_Syntax_Print.term_to_string t0  in
             let uu____3745 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____3742
               uu____3743 uu____3744 uu____3745
              in
           failwith uu____3741
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____3750 =
             let uu____3751 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____3752 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____3753 = FStar_Syntax_Print.term_to_string t0  in
             let uu____3754 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____3751
               uu____3752 uu____3753 uu____3754
              in
           failwith uu____3750
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____3760 = FStar_Syntax_Util.unfold_lazy i  in
           encode_term uu____3760 env
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____3762 =
             let uu____3763 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____3763
              in
           failwith uu____3762
       | FStar_Syntax_Syntax.Tm_ascribed (t1,(k,uu____3770),uu____3771) ->
           let uu____3820 =
             match k with
             | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
             | uu____3828 -> false  in
           if uu____3820
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t1 env
       | FStar_Syntax_Syntax.Tm_quoted (qt,uu____3843) ->
           let tv =
             let uu____3849 =
               let uu____3856 = FStar_Reflection_Basic.inspect_ln qt  in
               FStar_Syntax_Embeddings.embed
                 FStar_Reflection_Embeddings.e_term_view uu____3856
                in
             uu____3849 t.FStar_Syntax_Syntax.pos
               FStar_Pervasives_Native.None
               FStar_Syntax_Embeddings.id_norm_cb
              in
           let t1 =
             let uu____3885 =
               let uu____3896 = FStar_Syntax_Syntax.as_arg tv  in
               [uu____3896]  in
             FStar_Syntax_Util.mk_app
               (FStar_Reflection_Data.refl_constant_term
                  FStar_Reflection_Data.fstar_refl_pack_ln) uu____3885
              in
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_pattern uu____3922) ->
           encode_term t1
             (let uu___349_3940 = env  in
              {
                FStar_SMTEncoding_Env.bvar_bindings =
                  (uu___349_3940.FStar_SMTEncoding_Env.bvar_bindings);
                FStar_SMTEncoding_Env.fvar_bindings =
                  (uu___349_3940.FStar_SMTEncoding_Env.fvar_bindings);
                FStar_SMTEncoding_Env.depth =
                  (uu___349_3940.FStar_SMTEncoding_Env.depth);
                FStar_SMTEncoding_Env.tcenv =
                  (uu___349_3940.FStar_SMTEncoding_Env.tcenv);
                FStar_SMTEncoding_Env.warn =
                  (uu___349_3940.FStar_SMTEncoding_Env.warn);
                FStar_SMTEncoding_Env.cache =
                  (uu___349_3940.FStar_SMTEncoding_Env.cache);
                FStar_SMTEncoding_Env.nolabels =
                  (uu___349_3940.FStar_SMTEncoding_Env.nolabels);
                FStar_SMTEncoding_Env.use_zfuel_name =
                  (uu___349_3940.FStar_SMTEncoding_Env.use_zfuel_name);
                FStar_SMTEncoding_Env.encode_non_total_function_typ =
                  (uu___349_3940.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                FStar_SMTEncoding_Env.current_module_name =
                  (uu___349_3940.FStar_SMTEncoding_Env.current_module_name);
                FStar_SMTEncoding_Env.encoding_quantifier = false
              })
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____3942) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = FStar_SMTEncoding_Env.lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____3950 = head_redex env t  in
           if uu____3950
           then let uu____3955 = whnf env t  in encode_term uu____3955 env
           else
             (let uu____3957 =
                FStar_SMTEncoding_Env.lookup_free_var_name env
                  v1.FStar_Syntax_Syntax.fv_name
                 in
              match uu____3957 with
              | (uu____3966,arity) ->
                  let tok =
                    FStar_SMTEncoding_Env.lookup_free_var env
                      v1.FStar_Syntax_Syntax.fv_name
                     in
                  let aux_decls =
                    if arity > (Prims.parse_int "0")
                    then
                      match tok.FStar_SMTEncoding_Term.tm with
                      | FStar_SMTEncoding_Term.FreeV uu____3970 ->
                          let uu____3975 =
                            let uu____3976 =
                              let uu____3983 =
                                FStar_SMTEncoding_Term.kick_partial_app tok
                                 in
                              let uu____3984 =
                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                  "@kick_partial_app"
                                 in
                              (uu____3983,
                                (FStar_Pervasives_Native.Some
                                   "kick_partial_app"), uu____3984)
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____3976  in
                          [uu____3975]
                      | FStar_SMTEncoding_Term.App (uu____3985,[]) ->
                          let uu____3988 =
                            let uu____3989 =
                              let uu____3996 =
                                FStar_SMTEncoding_Term.kick_partial_app tok
                                 in
                              let uu____3997 =
                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                  "@kick_partial_app"
                                 in
                              (uu____3996,
                                (FStar_Pervasives_Native.Some
                                   "kick_partial_app"), uu____3997)
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____3989  in
                          [uu____3988]
                      | uu____3998 -> []
                    else []  in
                  (tok, aux_decls))
       | FStar_Syntax_Syntax.Tm_type uu____4000 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4002) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.FStar_SMTEncoding_Env.current_module_name
              in
           let uu____4031 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____4031 with
            | (binders1,res) ->
                let uu____4042 =
                  (env.FStar_SMTEncoding_Env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____4042
                then
                  let uu____4047 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____4047 with
                   | (vars,guards,env',decls,uu____4072) ->
                       let fsym =
                         let uu____4090 =
                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                             "f"
                            in
                         (uu____4090, FStar_SMTEncoding_Term.Term_sort)  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____4093 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___350_4102 =
                              env.FStar_SMTEncoding_Env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___350_4102.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___350_4102.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___350_4102.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___350_4102.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___350_4102.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___350_4102.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___350_4102.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___350_4102.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___350_4102.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___350_4102.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___350_4102.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___350_4102.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___350_4102.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___350_4102.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___350_4102.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___350_4102.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___350_4102.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___350_4102.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___350_4102.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___350_4102.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___350_4102.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___350_4102.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___350_4102.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___350_4102.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___350_4102.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___350_4102.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___350_4102.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___350_4102.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___350_4102.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___350_4102.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___350_4102.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___350_4102.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___350_4102.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___350_4102.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___350_4102.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___350_4102.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___350_4102.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___350_4102.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___350_4102.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___350_4102.FStar_TypeChecker_Env.dep_graph)
                            }) res
                          in
                       (match uu____4093 with
                        | (pre_opt,res_t) ->
                            let uu____4113 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____4113 with
                             | (res_pred,decls') ->
                                 let uu____4124 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____4137 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____4137, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____4141 =
                                         encode_formula pre env'  in
                                       (match uu____4141 with
                                        | (guard,decls0) ->
                                            let uu____4154 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____4154, decls0))
                                    in
                                 (match uu____4124 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____4168 =
                                          let uu____4179 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____4179)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t.FStar_Syntax_Syntax.pos
                                          uu____4168
                                         in
                                      let cvars =
                                        let uu____4195 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____4195
                                          (FStar_List.filter
                                             (fun uu____4221  ->
                                                match uu____4221 with
                                                | (x,uu____4227) ->
                                                    x <>
                                                      (FStar_Pervasives_Native.fst
                                                         fsym)))
                                         in
                                      let tkey =
                                        FStar_SMTEncoding_Term.mkForall
                                          t.FStar_Syntax_Syntax.pos
                                          ([], (fsym :: cvars), t_interp)
                                         in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey
                                         in
                                      let uu____4240 =
                                        FStar_Util.smap_try_find
                                          env.FStar_SMTEncoding_Env.cache
                                          tkey_hash
                                         in
                                      (match uu____4240 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____4248 =
                                             let uu____4249 =
                                               let uu____4256 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV)
                                                  in
                                               ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                                 uu____4256)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4249
                                              in
                                           (uu____4248,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (FStar_SMTEncoding_Env.use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____4274 =
                                               let uu____4275 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____4275
                                                in
                                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                               uu____4274
                                              in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars
                                              in
                                           let caption =
                                             let uu____4284 =
                                               FStar_Options.log_queries ()
                                                in
                                             if uu____4284
                                             then
                                               let uu____4285 =
                                                 let uu____4286 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env.FStar_SMTEncoding_Env.tcenv
                                                     t0
                                                    in
                                                 FStar_Util.replace_char
                                                   uu____4286 10 32
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____4285
                                             else
                                               FStar_Pervasives_Native.None
                                              in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption)
                                              in
                                           let t1 =
                                             let uu____4294 =
                                               let uu____4301 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars
                                                  in
                                               (tsym, uu____4301)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4294
                                              in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type
                                              in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym
                                                in
                                             let uu____4313 =
                                               let uu____4320 =
                                                 FStar_SMTEncoding_Term.mkForall
                                                   t0.FStar_Syntax_Syntax.pos
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind)
                                                  in
                                               (uu____4320,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name)
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4313
                                              in
                                           let f_has_t =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               f t1
                                              in
                                           let f_has_t_z =
                                             FStar_SMTEncoding_Term.mk_HasTypeZ
                                               f t1
                                              in
                                           let pre_typing =
                                             let a_name =
                                               Prims.strcat "pre_typing_"
                                                 tsym
                                                in
                                             let uu____4333 =
                                               let uu____4340 =
                                                 let uu____4341 =
                                                   let uu____4352 =
                                                     let uu____4353 =
                                                       let uu____4358 =
                                                         let uu____4359 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f
                                                            in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____4359
                                                          in
                                                       (f_has_t, uu____4358)
                                                        in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____4353
                                                      in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____4352)
                                                    in
                                                 let uu____4372 =
                                                   mkForall_fuel
                                                     t0.FStar_Syntax_Syntax.pos
                                                    in
                                                 uu____4372 uu____4341  in
                                               (uu____4340,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4333
                                              in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym
                                                in
                                             let uu____4389 =
                                               let uu____4396 =
                                                 let uu____4397 =
                                                   let uu____4408 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp)
                                                      in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____4408)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   t0.FStar_Syntax_Syntax.pos
                                                   uu____4397
                                                  in
                                               (uu____4396,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4389
                                              in
                                           let t_decls1 =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1]))
                                              in
                                           ((let uu____4425 =
                                               FStar_SMTEncoding_Env.mk_cache_entry
                                                 env tsym cvar_sorts t_decls1
                                                in
                                             FStar_Util.smap_add
                                               env.FStar_SMTEncoding_Env.cache
                                               tkey_hash uu____4425);
                                            (t1, t_decls1)))))))
                else
                  (let tsym =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                       "Non_total_Tm_arrow"
                      in
                   let tdecl =
                     FStar_SMTEncoding_Term.DeclFun
                       (tsym, [], FStar_SMTEncoding_Term.Term_sort,
                         FStar_Pervasives_Native.None)
                      in
                   let t1 = FStar_SMTEncoding_Util.mkApp (tsym, [])  in
                   let t_kinding =
                     let a_name =
                       Prims.strcat "non_total_function_typing_" tsym  in
                     let uu____4436 =
                       let uu____4443 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____4443,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____4436  in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)  in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym  in
                     let uu____4453 =
                       let uu____4460 =
                         let uu____4461 =
                           let uu____4472 =
                             let uu____4473 =
                               let uu____4478 =
                                 let uu____4479 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____4479
                                  in
                               (f_has_t, uu____4478)  in
                             FStar_SMTEncoding_Util.mkImp uu____4473  in
                           ([[f_has_t]], [fsym], uu____4472)  in
                         let uu____4496 =
                           mkForall_fuel t0.FStar_Syntax_Syntax.pos  in
                         uu____4496 uu____4461  in
                       (uu____4460, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____4453  in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____4511 ->
           let uu____4518 =
             let uu____4523 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.Weak;
                 FStar_TypeChecker_Normalize.HNF;
                 FStar_TypeChecker_Normalize.EraseUniverses]
                 env.FStar_SMTEncoding_Env.tcenv t0
                in
             match uu____4523 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____4530;
                 FStar_Syntax_Syntax.vars = uu____4531;_} ->
                 let uu____4538 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____4538 with
                  | (b,f1) ->
                      let uu____4563 =
                        let uu____4564 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____4564  in
                      (uu____4563, f1))
             | uu____4579 -> failwith "impossible"  in
           (match uu____4518 with
            | (x,f) ->
                let uu____4590 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____4590 with
                 | (base_t,decls) ->
                     let uu____4601 =
                       FStar_SMTEncoding_Env.gen_term_var env x  in
                     (match uu____4601 with
                      | (x1,xtm,env') ->
                          let uu____4615 = encode_formula f env'  in
                          (match uu____4615 with
                           | (refinement,decls') ->
                               let uu____4626 =
                                 FStar_SMTEncoding_Env.fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____4626 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t
                                       in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement)
                                       in
                                    let cvars =
                                      let uu____4646 =
                                        let uu____4653 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____4660 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____4653
                                          uu____4660
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____4646
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____4701  ->
                                              match uu____4701 with
                                              | (y,uu____4707) ->
                                                  (y <> x1) && (y <> fsym)))
                                       in
                                    let xfv =
                                      (x1, FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    let ffv =
                                      (fsym,
                                        FStar_SMTEncoding_Term.Fuel_sort)
                                       in
                                    let tkey =
                                      FStar_SMTEncoding_Term.mkForall
                                        t0.FStar_Syntax_Syntax.pos
                                        ([], (ffv :: xfv :: cvars1),
                                          encoding)
                                       in
                                    let tkey_hash =
                                      FStar_SMTEncoding_Term.hash_of_term
                                        tkey
                                       in
                                    let uu____4734 =
                                      FStar_Util.smap_try_find
                                        env.FStar_SMTEncoding_Env.cache
                                        tkey_hash
                                       in
                                    (match uu____4734 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____4742 =
                                           let uu____4743 =
                                             let uu____4750 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV)
                                                in
                                             ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                               uu____4750)
                                              in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____4743
                                            in
                                         (uu____4742,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (FStar_SMTEncoding_Env.use_cache_entry
                                                    cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.FStar_SMTEncoding_Env.current_module_name
                                            in
                                         let tsym =
                                           let uu____4769 =
                                             let uu____4770 =
                                               let uu____4771 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____4771
                                                in
                                             Prims.strcat module_name
                                               uu____4770
                                              in
                                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                             uu____4769
                                            in
                                         let cvar_sorts =
                                           FStar_List.map
                                             FStar_Pervasives_Native.snd
                                             cvars1
                                            in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None)
                                            in
                                         let t1 =
                                           let uu____4783 =
                                             let uu____4790 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1
                                                in
                                             (tsym, uu____4790)  in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____4783
                                            in
                                         let x_has_base_t =
                                           FStar_SMTEncoding_Term.mk_HasType
                                             xtm base_t
                                            in
                                         let x_has_t =
                                           FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                             (FStar_Pervasives_Native.Some
                                                fterm) xtm t1
                                            in
                                         let t_has_kind =
                                           FStar_SMTEncoding_Term.mk_HasType
                                             t1
                                             FStar_SMTEncoding_Term.mk_Term_type
                                            in
                                         let t_haseq_base =
                                           FStar_SMTEncoding_Term.mk_haseq
                                             base_t
                                            in
                                         let t_haseq_ref =
                                           FStar_SMTEncoding_Term.mk_haseq t1
                                            in
                                         let t_haseq1 =
                                           let uu____4805 =
                                             let uu____4812 =
                                               let uu____4813 =
                                                 let uu____4824 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base)
                                                    in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____4824)
                                                  in
                                               FStar_SMTEncoding_Term.mkForall
                                                 t0.FStar_Syntax_Syntax.pos
                                                 uu____4813
                                                in
                                             (uu____4812,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4805
                                            in
                                         let t_kinding =
                                           let uu____4834 =
                                             let uu____4841 =
                                               FStar_SMTEncoding_Term.mkForall
                                                 t0.FStar_Syntax_Syntax.pos
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind)
                                                in
                                             (uu____4841,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4834
                                            in
                                         let t_interp =
                                           let uu____4851 =
                                             let uu____4858 =
                                               let uu____4859 =
                                                 let uu____4870 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding)
                                                    in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____4870)
                                                  in
                                               FStar_SMTEncoding_Term.mkForall
                                                 t0.FStar_Syntax_Syntax.pos
                                                 uu____4859
                                                in
                                             (uu____4858,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement_interpretation"),
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4851
                                            in
                                         let t_decls1 =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1])
                                            in
                                         ((let uu____4891 =
                                             FStar_SMTEncoding_Env.mk_cache_entry
                                               env tsym cvar_sorts t_decls1
                                              in
                                           FStar_Util.smap_add
                                             env.FStar_SMTEncoding_Env.cache
                                             tkey_hash uu____4891);
                                          (t1, t_decls1))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,uu____4893) ->
           let ttm =
             let uu____4911 =
               FStar_Syntax_Unionfind.uvar_id
                 uv.FStar_Syntax_Syntax.ctx_uvar_head
                in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____4911  in
           let uu____4912 =
             encode_term_pred FStar_Pervasives_Native.None
               uv.FStar_Syntax_Syntax.ctx_uvar_typ env ttm
              in
           (match uu____4912 with
            | (t_has_k,decls) ->
                let d =
                  let uu____4924 =
                    let uu____4931 =
                      let uu____4932 =
                        let uu____4933 =
                          let uu____4934 =
                            FStar_Syntax_Unionfind.uvar_id
                              uv.FStar_Syntax_Syntax.ctx_uvar_head
                             in
                          FStar_Util.string_of_int uu____4934  in
                        FStar_Util.format1 "uvar_typing_%s" uu____4933  in
                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                        uu____4932
                       in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____4931)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____4924  in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____4935 ->
           let uu____4952 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____4952 with
            | (head1,args_e) ->
                let uu____4999 =
                  let uu____5014 =
                    let uu____5015 = FStar_Syntax_Subst.compress head1  in
                    uu____5015.FStar_Syntax_Syntax.n  in
                  (uu____5014, args_e)  in
                (match uu____4999 with
                 | uu____5032 when head_redex env head1 ->
                     let uu____5047 = whnf env t  in
                     encode_term uu____5047 env
                 | uu____5048 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____5071 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5089) when
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
                       FStar_Syntax_Syntax.pos = uu____5111;
                       FStar_Syntax_Syntax.vars = uu____5112;_},uu____5113),uu____5114)
                     when
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
                       FStar_Syntax_Syntax.pos = uu____5140;
                       FStar_Syntax_Syntax.vars = uu____5141;_},uu____5142),
                    (v0,uu____5144)::(v1,uu____5146)::(v2,uu____5148)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____5219 = encode_term v0 env  in
                     (match uu____5219 with
                      | (v01,decls0) ->
                          let uu____5230 = encode_term v1 env  in
                          (match uu____5230 with
                           | (v11,decls1) ->
                               let uu____5241 = encode_term v2 env  in
                               (match uu____5241 with
                                | (v21,decls2) ->
                                    let uu____5252 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____5252,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(v0,uu____5255)::(v1,uu____5257)::(v2,uu____5259)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____5326 = encode_term v0 env  in
                     (match uu____5326 with
                      | (v01,decls0) ->
                          let uu____5337 = encode_term v1 env  in
                          (match uu____5337 with
                           | (v11,decls1) ->
                               let uu____5348 = encode_term v2 env  in
                               (match uu____5348 with
                                | (v21,decls2) ->
                                    let uu____5359 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____5359,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____5361)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____5397)::(rng,uu____5399)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____5450) ->
                     let e0 =
                       let uu____5472 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg
                         env.FStar_SMTEncoding_Env.tcenv head1 uu____5472
                        in
                     ((let uu____5482 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug
                              env.FStar_SMTEncoding_Env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____5482
                       then
                         let uu____5483 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____5483
                       else ());
                      (let e =
                         let uu____5488 =
                           let uu____5493 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____5494 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____5493
                             uu____5494
                            in
                         uu____5488 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____5505),(arg,uu____5507)::[]) -> encode_term arg env
                 | uu____5542 ->
                     let uu____5557 = encode_args args_e env  in
                     (match uu____5557 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____5618 = encode_term head1 env  in
                            match uu____5618 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____5690 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____5690 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____5788  ->
                                                 fun uu____5789  ->
                                                   match (uu____5788,
                                                           uu____5789)
                                                   with
                                                   | ((bv,uu____5819),
                                                      (a,uu____5821)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____5851 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____5851
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____5852 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm
                                             in
                                          (match uu____5852 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type
                                                  in
                                               let e_typing =
                                                 let uu____5867 =
                                                   let uu____5874 =
                                                     FStar_SMTEncoding_Term.mkForall
                                                       t0.FStar_Syntax_Syntax.pos
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____5883 =
                                                     let uu____5884 =
                                                       let uu____5885 =
                                                         let uu____5886 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm
                                                            in
                                                         FStar_Util.digest_of_string
                                                           uu____5886
                                                          in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____5885
                                                        in
                                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                       uu____5884
                                                      in
                                                   (uu____5874,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____5883)
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____5867
                                                  in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing])))))))
                             in
                          let encode_full_app fv =
                            let uu____5903 =
                              FStar_SMTEncoding_Env.lookup_free_var_sym env
                                fv
                               in
                            match uu____5903 with
                            | (fname,fuel_args,arity) ->
                                let tm =
                                  maybe_curry_app t0.FStar_Syntax_Syntax.pos
                                    fname arity
                                    (FStar_List.append fuel_args args)
                                   in
                                (tm, decls)
                             in
                          let head2 = FStar_Syntax_Subst.compress head1  in
                          let head_type =
                            match head2.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_uinst
                                ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_name x;
                                   FStar_Syntax_Syntax.pos = uu____5931;
                                   FStar_Syntax_Syntax.vars = uu____5932;_},uu____5933)
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
                                   FStar_Syntax_Syntax.pos = uu____5940;
                                   FStar_Syntax_Syntax.vars = uu____5941;_},uu____5942)
                                ->
                                let uu____5947 =
                                  let uu____5948 =
                                    let uu____5953 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____5953
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____5948
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____5947
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____5983 =
                                  let uu____5984 =
                                    let uu____5989 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____5989
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____5984
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____5983
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____6018,(FStar_Util.Inl t1,uu____6020),uu____6021)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____6068,(FStar_Util.Inr c,uu____6070),uu____6071)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____6118 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____6139 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.Weak;
                                     FStar_TypeChecker_Normalize.HNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.FStar_SMTEncoding_Env.tcenv
                                     head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____6139
                                  in
                               let uu____6140 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____6140 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____6156;
                                            FStar_Syntax_Syntax.vars =
                                              uu____6157;_},uu____6158)
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
                                     | uu____6176 ->
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
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____6253 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____6253 with
            | (bs1,body1,opening) ->
                let fallback uu____6278 =
                  let f =
                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                      "Tm_abs"
                     in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding"))
                     in
                  let uu____6283 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort)
                     in
                  (uu____6283, [decl])  in
                let is_impure rc =
                  let uu____6292 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                      env.FStar_SMTEncoding_Env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____6292 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____6304 =
                          let uu____6317 =
                            FStar_TypeChecker_Env.get_range
                              env.FStar_SMTEncoding_Env.tcenv
                             in
                          FStar_TypeChecker_Util.new_implicit_var
                            "SMTEncoding codomain" uu____6317
                            env.FStar_SMTEncoding_Env.tcenv
                            FStar_Syntax_Util.ktype0
                           in
                        (match uu____6304 with
                         | (t1,uu____6319,uu____6320) -> t1)
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  let uu____6338 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                     in
                  if uu____6338
                  then
                    let uu____6341 = FStar_Syntax_Syntax.mk_Total res_typ  in
                    FStar_Pervasives_Native.Some uu____6341
                  else
                    (let uu____6343 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid
                        in
                     if uu____6343
                     then
                       let uu____6346 = FStar_Syntax_Syntax.mk_GTotal res_typ
                          in
                       FStar_Pervasives_Native.Some uu____6346
                     else FStar_Pervasives_Native.None)
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____6353 =
                         let uu____6358 =
                           let uu____6359 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____6359
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____6358)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____6353);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____6361 =
                       (is_impure rc) &&
                         (let uu____6363 =
                            FStar_TypeChecker_Env.is_reifiable
                              env.FStar_SMTEncoding_Env.tcenv rc
                             in
                          Prims.op_Negation uu____6363)
                        in
                     if uu____6361
                     then fallback ()
                     else
                       (let cache_size =
                          FStar_Util.smap_size
                            env.FStar_SMTEncoding_Env.cache
                           in
                        let uu____6370 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____6370 with
                        | (vars,guards,envbody,decls,uu____6395) ->
                            let body2 =
                              let uu____6409 =
                                FStar_TypeChecker_Env.is_reifiable
                                  env.FStar_SMTEncoding_Env.tcenv rc
                                 in
                              if uu____6409
                              then
                                FStar_TypeChecker_Util.reify_body
                                  env.FStar_SMTEncoding_Env.tcenv body1
                              else body1  in
                            let uu____6411 = encode_term body2 envbody  in
                            (match uu____6411 with
                             | (body3,decls') ->
                                 let uu____6422 =
                                   let uu____6431 = codomain_eff rc  in
                                   match uu____6431 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____6450 = encode_term tfun env
                                          in
                                       (match uu____6450 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____6422 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____6484 =
                                          let uu____6495 =
                                            let uu____6496 =
                                              let uu____6501 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____6501, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____6496
                                             in
                                          ([], vars, uu____6495)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t0.FStar_Syntax_Syntax.pos
                                          uu____6484
                                         in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body
                                         in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            cvars
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____6523 =
                                              let uu____6530 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1
                                                 in
                                              FStar_List.append uu____6530
                                                cvars
                                               in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____6523
                                         in
                                      let tkey =
                                        FStar_SMTEncoding_Term.mkForall
                                          t0.FStar_Syntax_Syntax.pos
                                          ([], cvars1, key_body)
                                         in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey
                                         in
                                      let uu____6553 =
                                        FStar_Util.smap_try_find
                                          env.FStar_SMTEncoding_Env.cache
                                          tkey_hash
                                         in
                                      (match uu____6553 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____6561 =
                                             let uu____6562 =
                                               let uu____6569 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1
                                                  in
                                               ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                                 uu____6569)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6562
                                              in
                                           (uu____6561,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (FStar_SMTEncoding_Env.use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____6578 =
                                             is_an_eta_expansion env vars
                                               body3
                                              in
                                           (match uu____6578 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____6587 =
                                                    let uu____6588 =
                                                      FStar_Util.smap_size
                                                        env.FStar_SMTEncoding_Env.cache
                                                       in
                                                    uu____6588 = cache_size
                                                     in
                                                  if uu____6587
                                                  then []
                                                  else
                                                    FStar_List.append decls
                                                      (FStar_List.append
                                                         decls' decls'')
                                                   in
                                                (t1, decls1)
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                let cvar_sorts =
                                                  FStar_List.map
                                                    FStar_Pervasives_Native.snd
                                                    cvars1
                                                   in
                                                let fsym =
                                                  let module_name =
                                                    env.FStar_SMTEncoding_Env.current_module_name
                                                     in
                                                  let fsym =
                                                    let uu____6600 =
                                                      let uu____6601 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash
                                                         in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____6601
                                                       in
                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                      uu____6600
                                                     in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym)
                                                   in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None)
                                                   in
                                                let f =
                                                  let uu____6606 =
                                                    let uu____6613 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    (fsym, uu____6613)  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____6606
                                                   in
                                                let app = mk_Apply f vars  in
                                                let typing_f =
                                                  match arrow_t_opt with
                                                  | FStar_Pervasives_Native.None
                                                       -> []
                                                  | FStar_Pervasives_Native.Some
                                                      t1 ->
                                                      let f_has_t =
                                                        FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                          FStar_Pervasives_Native.None
                                                          f t1
                                                         in
                                                      let a_name =
                                                        Prims.strcat
                                                          "typing_" fsym
                                                         in
                                                      let uu____6631 =
                                                        let uu____6632 =
                                                          let uu____6639 =
                                                            FStar_SMTEncoding_Term.mkForall
                                                              t0.FStar_Syntax_Syntax.pos
                                                              ([[f]], cvars1,
                                                                f_has_t)
                                                             in
                                                          (uu____6639,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name)
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____6632
                                                         in
                                                      [uu____6631]
                                                   in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym
                                                     in
                                                  let uu____6650 =
                                                    let uu____6657 =
                                                      let uu____6658 =
                                                        let uu____6669 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3)
                                                           in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____6669)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        t0.FStar_Syntax_Syntax.pos
                                                        uu____6658
                                                       in
                                                    (uu____6657,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____6650
                                                   in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f])))
                                                   in
                                                ((let uu____6682 =
                                                    FStar_SMTEncoding_Env.mk_cache_entry
                                                      env fsym cvar_sorts
                                                      f_decls
                                                     in
                                                  FStar_Util.smap_add
                                                    env.FStar_SMTEncoding_Env.cache
                                                    tkey_hash uu____6682);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____6683,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____6684;
                          FStar_Syntax_Syntax.lbunivs = uu____6685;
                          FStar_Syntax_Syntax.lbtyp = uu____6686;
                          FStar_Syntax_Syntax.lbeff = uu____6687;
                          FStar_Syntax_Syntax.lbdef = uu____6688;
                          FStar_Syntax_Syntax.lbattrs = uu____6689;
                          FStar_Syntax_Syntax.lbpos = uu____6690;_}::uu____6691),uu____6692)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____6722;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____6724;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____6726;
                FStar_Syntax_Syntax.lbpos = uu____6727;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____6751 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions, and their enclosings let bindings (including the top-level let) are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            FStar_Exn.raise FStar_SMTEncoding_Env.Inner_let_rec)
       | FStar_Syntax_Syntax.Tm_match (e,pats) ->
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
                 (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
                   FStar_Pervasives_Native.tuple2)
              ->
              (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
                FStar_Pervasives_Native.tuple2)
  =
  fun x  ->
    fun t1  ->
      fun e1  ->
        fun e2  ->
          fun env  ->
            fun encode_body  ->
              let uu____6821 =
                let uu____6826 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____6826 env  in
              match uu____6821 with
              | (ee1,decls1) ->
                  let uu____6851 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____6851 with
                   | (xs,e21) ->
                       let uu____6876 = FStar_List.hd xs  in
                       (match uu____6876 with
                        | (x1,uu____6894) ->
                            let env' =
                              FStar_SMTEncoding_Env.push_term_var env x1 ee1
                               in
                            let uu____6900 = encode_body e21 env'  in
                            (match uu____6900 with
                             | (ee2,decls2) ->
                                 (ee2, (FStar_List.append decls1 decls2)))))

and (encode_match :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.branch Prims.list ->
      FStar_SMTEncoding_Term.term ->
        FStar_SMTEncoding_Env.env_t ->
          (FStar_Syntax_Syntax.term ->
             FStar_SMTEncoding_Env.env_t ->
               (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
                 FStar_Pervasives_Native.tuple2)
            ->
            (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
              FStar_Pervasives_Native.tuple2)
  =
  fun e  ->
    fun pats  ->
      fun default_case  ->
        fun env  ->
          fun encode_br  ->
            let uu____6930 =
              let uu____6937 =
                let uu____6938 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____6938  in
              FStar_SMTEncoding_Env.gen_term_var env uu____6937  in
            match uu____6930 with
            | (scrsym,scr',env1) ->
                let uu____6946 = encode_term e env1  in
                (match uu____6946 with
                 | (scr,decls) ->
                     let uu____6957 =
                       let encode_branch b uu____6986 =
                         match uu____6986 with
                         | (else_case,decls1) ->
                             let uu____7005 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____7005 with
                              | (p,w,br) ->
                                  let uu____7031 = encode_pat env1 p  in
                                  (match uu____7031 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____7068  ->
                                                   match uu____7068 with
                                                   | (x,t) ->
                                                       FStar_SMTEncoding_Env.push_term_var
                                                         env2 x t) env1)
                                          in
                                       let uu____7075 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____7097 =
                                               encode_term w1 env2  in
                                             (match uu____7097 with
                                              | (w2,decls2) ->
                                                  let uu____7110 =
                                                    let uu____7111 =
                                                      let uu____7116 =
                                                        let uu____7117 =
                                                          let uu____7122 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____7122)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____7117
                                                         in
                                                      (guard, uu____7116)  in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____7111
                                                     in
                                                  (uu____7110, decls2))
                                          in
                                       (match uu____7075 with
                                        | (guard1,decls2) ->
                                            let uu____7137 =
                                              encode_br br env2  in
                                            (match uu____7137 with
                                             | (br1,decls3) ->
                                                 let uu____7150 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____7150,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____6957 with
                      | (match_tm,decls1) ->
                          let uu____7171 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange
                             in
                          (uu____7171, decls1)))

and (encode_pat :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.pat ->
      (FStar_SMTEncoding_Env.env_t,pattern) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun pat  ->
      (let uu____7193 =
         FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
           FStar_Options.Low
          in
       if uu____7193
       then
         let uu____7194 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____7194
       else ());
      (let uu____7196 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____7196 with
       | (vars,pat_term) ->
           let uu____7213 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____7266  ->
                     fun v1  ->
                       match uu____7266 with
                       | (env1,vars1) ->
                           let uu____7318 =
                             FStar_SMTEncoding_Env.gen_term_var env1 v1  in
                           (match uu____7318 with
                            | (xx,uu____7340,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, []))
              in
           (match uu____7213 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____7423 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____7424 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____7425 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____7433 = encode_const c env1  in
                      (match uu____7433 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____7441::uu____7442 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____7445 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon
                            env1.FStar_SMTEncoding_Env.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____7466 =
                          FStar_TypeChecker_Env.datacons_of_typ
                            env1.FStar_SMTEncoding_Env.tcenv tc_name
                           in
                        match uu____7466 with
                        | (uu____7473,uu____7474::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____7477 ->
                            FStar_SMTEncoding_Env.mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____7510  ->
                                  match uu____7510 with
                                  | (arg,uu____7518) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____7524 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____7524))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____7555) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____7586 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____7609 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____7653  ->
                                  match uu____7653 with
                                  | (arg,uu____7667) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____7673 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____7673))
                         in
                      FStar_All.pipe_right uu____7609 FStar_List.flatten
                   in
                let pat_term1 uu____7703 = encode_term pat_term env1  in
                let pattern =
                  {
                    pat_vars = vars1;
                    pat_term = pat_term1;
                    guard = (mk_guard pat);
                    projections = (mk_projections pat)
                  }  in
                (env1, pattern)))

and (encode_args :
  FStar_Syntax_Syntax.args ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term Prims.list,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    fun env  ->
      let uu____7713 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____7761  ->
                fun uu____7762  ->
                  match (uu____7761, uu____7762) with
                  | ((tms,decls),(t,uu____7802)) ->
                      let uu____7829 = encode_term t env  in
                      (match uu____7829 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____7713 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____7886 = FStar_Syntax_Util.list_elements e  in
        match uu____7886 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____7915 =
          let uu____7932 = FStar_Syntax_Util.unmeta p  in
          FStar_All.pipe_right uu____7932 FStar_Syntax_Util.head_and_args  in
        match uu____7915 with
        | (head1,args) ->
            let uu____7983 =
              let uu____7998 =
                let uu____7999 = FStar_Syntax_Util.un_uinst head1  in
                uu____7999.FStar_Syntax_Syntax.n  in
              (uu____7998, args)  in
            (match uu____7983 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____8021,uu____8022)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____8074 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or t1 =
          let uu____8128 =
            let uu____8145 = FStar_Syntax_Util.unmeta t1  in
            FStar_All.pipe_right uu____8145 FStar_Syntax_Util.head_and_args
             in
          match uu____8128 with
          | (head1,args) ->
              let uu____8192 =
                let uu____8207 =
                  let uu____8208 = FStar_Syntax_Util.un_uinst head1  in
                  uu____8208.FStar_Syntax_Syntax.n  in
                (uu____8207, args)  in
              (match uu____8192 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____8227)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____8264 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____8294 = smt_pat_or t1  in
            (match uu____8294 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____8316 = list_elements1 e  in
                 FStar_All.pipe_right uu____8316
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____8346 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____8346
                           (FStar_List.map one_pat)))
             | uu____8369 ->
                 let uu____8374 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____8374])
        | uu____8425 ->
            let uu____8428 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____8428]
         in
      let uu____8479 =
        let uu____8494 =
          let uu____8495 = FStar_Syntax_Subst.compress t  in
          uu____8495.FStar_Syntax_Syntax.n  in
        match uu____8494 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____8534 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____8534 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____8569;
                        FStar_Syntax_Syntax.effect_name = uu____8570;
                        FStar_Syntax_Syntax.result_typ = uu____8571;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____8573)::(post,uu____8575)::(pats,uu____8577)::[];
                        FStar_Syntax_Syntax.flags = uu____8578;_}
                      ->
                      let uu____8639 = lemma_pats pats  in
                      (binders1, pre, post, uu____8639)
                  | uu____8650 -> failwith "impos"))
        | uu____8665 -> failwith "Impos"  in
      match uu____8479 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___351_8701 = env  in
            {
              FStar_SMTEncoding_Env.bvar_bindings =
                (uu___351_8701.FStar_SMTEncoding_Env.bvar_bindings);
              FStar_SMTEncoding_Env.fvar_bindings =
                (uu___351_8701.FStar_SMTEncoding_Env.fvar_bindings);
              FStar_SMTEncoding_Env.depth =
                (uu___351_8701.FStar_SMTEncoding_Env.depth);
              FStar_SMTEncoding_Env.tcenv =
                (uu___351_8701.FStar_SMTEncoding_Env.tcenv);
              FStar_SMTEncoding_Env.warn =
                (uu___351_8701.FStar_SMTEncoding_Env.warn);
              FStar_SMTEncoding_Env.cache =
                (uu___351_8701.FStar_SMTEncoding_Env.cache);
              FStar_SMTEncoding_Env.nolabels =
                (uu___351_8701.FStar_SMTEncoding_Env.nolabels);
              FStar_SMTEncoding_Env.use_zfuel_name = true;
              FStar_SMTEncoding_Env.encode_non_total_function_typ =
                (uu___351_8701.FStar_SMTEncoding_Env.encode_non_total_function_typ);
              FStar_SMTEncoding_Env.current_module_name =
                (uu___351_8701.FStar_SMTEncoding_Env.current_module_name);
              FStar_SMTEncoding_Env.encoding_quantifier =
                (uu___351_8701.FStar_SMTEncoding_Env.encoding_quantifier)
            }  in
          let uu____8702 =
            encode_binders FStar_Pervasives_Native.None binders env1  in
          (match uu____8702 with
           | (vars,guards,env2,decls,uu____8727) ->
               let uu____8740 = encode_smt_patterns patterns env2  in
               (match uu____8740 with
                | (pats,decls') ->
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
                    let env3 =
                      let uu___352_8773 = env2  in
                      {
                        FStar_SMTEncoding_Env.bvar_bindings =
                          (uu___352_8773.FStar_SMTEncoding_Env.bvar_bindings);
                        FStar_SMTEncoding_Env.fvar_bindings =
                          (uu___352_8773.FStar_SMTEncoding_Env.fvar_bindings);
                        FStar_SMTEncoding_Env.depth =
                          (uu___352_8773.FStar_SMTEncoding_Env.depth);
                        FStar_SMTEncoding_Env.tcenv =
                          (uu___352_8773.FStar_SMTEncoding_Env.tcenv);
                        FStar_SMTEncoding_Env.warn =
                          (uu___352_8773.FStar_SMTEncoding_Env.warn);
                        FStar_SMTEncoding_Env.cache =
                          (uu___352_8773.FStar_SMTEncoding_Env.cache);
                        FStar_SMTEncoding_Env.nolabels = true;
                        FStar_SMTEncoding_Env.use_zfuel_name =
                          (uu___352_8773.FStar_SMTEncoding_Env.use_zfuel_name);
                        FStar_SMTEncoding_Env.encode_non_total_function_typ =
                          (uu___352_8773.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                        FStar_SMTEncoding_Env.current_module_name =
                          (uu___352_8773.FStar_SMTEncoding_Env.current_module_name);
                        FStar_SMTEncoding_Env.encoding_quantifier =
                          (uu___352_8773.FStar_SMTEncoding_Env.encoding_quantifier)
                      }  in
                    let uu____8774 =
                      let uu____8779 = FStar_Syntax_Util.unmeta pre  in
                      encode_formula uu____8779 env3  in
                    (match uu____8774 with
                     | (pre1,decls'') ->
                         let uu____8786 =
                           let uu____8791 = FStar_Syntax_Util.unmeta post1
                              in
                           encode_formula uu____8791 env3  in
                         (match uu____8786 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append decls'
                                     (FStar_List.append decls'' decls'''))
                                 in
                              let uu____8801 =
                                let uu____8802 =
                                  let uu____8813 =
                                    let uu____8814 =
                                      let uu____8819 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards)
                                         in
                                      (uu____8819, post2)  in
                                    FStar_SMTEncoding_Util.mkImp uu____8814
                                     in
                                  (pats, vars, uu____8813)  in
                                FStar_SMTEncoding_Term.mkForall
                                  t.FStar_Syntax_Syntax.pos uu____8802
                                 in
                              (uu____8801, decls1)))))

and (encode_smt_patterns :
  FStar_Syntax_Syntax.arg Prims.list Prims.list ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term Prims.list Prims.list,FStar_SMTEncoding_Term.decl
                                                           Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun pats_l  ->
    fun env  ->
      let env1 =
        let uu___353_8841 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___353_8841.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___353_8841.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___353_8841.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___353_8841.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___353_8841.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.cache =
            (uu___353_8841.FStar_SMTEncoding_Env.cache);
          FStar_SMTEncoding_Env.nolabels =
            (uu___353_8841.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___353_8841.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___353_8841.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___353_8841.FStar_SMTEncoding_Env.encoding_quantifier)
        }  in
      let encode_smt_pattern t =
        let uu____8856 = FStar_Syntax_Util.head_and_args t  in
        match uu____8856 with
        | (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____8919::(x,uu____8921)::(t1,uu____8923)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____8990 = encode_term x env1  in
                 (match uu____8990 with
                  | (x1,decls) ->
                      let uu____9001 = encode_term t1 env1  in
                      (match uu____9001 with
                       | (t2,decls') ->
                           let uu____9012 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                           (uu____9012, (FStar_List.append decls decls'))))
             | uu____9013 -> encode_term t env1)
         in
      FStar_List.fold_right
        (fun pats  ->
           fun uu____9056  ->
             match uu____9056 with
             | (pats_l1,decls) ->
                 let uu____9101 =
                   FStar_List.fold_right
                     (fun uu____9136  ->
                        fun uu____9137  ->
                          match (uu____9136, uu____9137) with
                          | ((p,uu____9179),(pats1,decls1)) ->
                              let uu____9214 = encode_smt_pattern p  in
                              (match uu____9214 with
                               | (t,d) ->
                                   let uu____9229 =
                                     FStar_SMTEncoding_Term.check_pattern_ok
                                       t
                                      in
                                   (match uu____9229 with
                                    | FStar_Pervasives_Native.None  ->
                                        ((t :: pats1),
                                          (FStar_List.append d decls1))
                                    | FStar_Pervasives_Native.Some
                                        illegal_subterm ->
                                        ((let uu____9246 =
                                            let uu____9251 =
                                              let uu____9252 =
                                                FStar_Syntax_Print.term_to_string
                                                  p
                                                 in
                                              let uu____9253 =
                                                FStar_SMTEncoding_Term.print_smt_term
                                                  illegal_subterm
                                                 in
                                              FStar_Util.format2
                                                "Pattern %s contains illegal sub-term (%s); dropping it"
                                                uu____9252 uu____9253
                                               in
                                            (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                                              uu____9251)
                                             in
                                          FStar_Errors.log_issue
                                            p.FStar_Syntax_Syntax.pos
                                            uu____9246);
                                         (pats1,
                                           (FStar_List.append d decls1))))))
                     pats ([], decls)
                    in
                 (match uu____9101 with
                  | (pats1,decls1) -> ((pats1 :: pats_l1), decls1))) pats_l
        ([], [])

and (encode_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____9310 =
          FStar_All.pipe_left
            (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____9310
        then
          let uu____9311 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____9312 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____9311 uu____9312
        else ()  in
      let enc f r l =
        let uu____9351 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____9383 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____9383 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____9351 with
        | (decls,args) ->
            let uu____9414 =
              let uu___354_9415 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___354_9415.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___354_9415.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____9414, decls)
         in
      let const_op f r uu____9450 = let uu____9463 = f r  in (uu____9463, [])
         in
      let un_op f l =
        let uu____9486 = FStar_List.hd l  in FStar_All.pipe_left f uu____9486
         in
      let bin_op f uu___345_9506 =
        match uu___345_9506 with
        | t1::t2::[] -> f (t1, t2)
        | uu____9517 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____9557 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____9582  ->
                 match uu____9582 with
                 | (t,uu____9598) ->
                     let uu____9603 = encode_formula t env  in
                     (match uu____9603 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____9557 with
        | (decls,phis) ->
            let uu____9632 =
              let uu___355_9633 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___355_9633.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___355_9633.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____9632, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____9696  ->
               match uu____9696 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____9715) -> false
                    | uu____9716 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____9731 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____9731
        else
          (let uu____9745 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____9745 r rf)
         in
      let mk_imp1 r uu___346_9780 =
        match uu___346_9780 with
        | (lhs,uu____9786)::(rhs,uu____9788)::[] ->
            let uu____9829 = encode_formula rhs env  in
            (match uu____9829 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____9844) ->
                      (l1, decls1)
                  | uu____9849 ->
                      let uu____9850 = encode_formula lhs env  in
                      (match uu____9850 with
                       | (l2,decls2) ->
                           let uu____9861 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____9861, (FStar_List.append decls1 decls2)))))
        | uu____9862 -> failwith "impossible"  in
      let mk_ite r uu___347_9889 =
        match uu___347_9889 with
        | (guard,uu____9895)::(_then,uu____9897)::(_else,uu____9899)::[] ->
            let uu____9956 = encode_formula guard env  in
            (match uu____9956 with
             | (g,decls1) ->
                 let uu____9967 = encode_formula _then env  in
                 (match uu____9967 with
                  | (t,decls2) ->
                      let uu____9978 = encode_formula _else env  in
                      (match uu____9978 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____9990 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____10019 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l
           in
        f uu____10019  in
      let connectives =
        let uu____10049 =
          let uu____10074 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____10074)  in
        let uu____10117 =
          let uu____10144 =
            let uu____10169 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____10169)  in
          let uu____10212 =
            let uu____10239 =
              let uu____10266 =
                let uu____10291 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____10291)  in
              let uu____10334 =
                let uu____10361 =
                  let uu____10388 =
                    let uu____10413 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____10413)  in
                  [uu____10388;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____10361  in
              uu____10266 :: uu____10334  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____10239  in
          uu____10144 :: uu____10212  in
        uu____10049 :: uu____10117  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____10866 = encode_formula phi' env  in
            (match uu____10866 with
             | (phi2,decls) ->
                 let uu____10877 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____10877, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____10878 ->
            let uu____10885 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____10885 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____10924 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____10924 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____10936;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____10938;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____10940;
                 FStar_Syntax_Syntax.lbpos = uu____10941;_}::[]),e2)
            ->
            let uu____10965 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____10965 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____11018::(x,uu____11020)::(t,uu____11022)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____11089 = encode_term x env  in
                 (match uu____11089 with
                  | (x1,decls) ->
                      let uu____11100 = encode_term t env  in
                      (match uu____11100 with
                       | (t1,decls') ->
                           let uu____11111 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____11111, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____11114)::(msg,uu____11116)::(phi2,uu____11118)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____11185 =
                   let uu____11190 =
                     let uu____11191 = FStar_Syntax_Subst.compress r  in
                     uu____11191.FStar_Syntax_Syntax.n  in
                   let uu____11194 =
                     let uu____11195 = FStar_Syntax_Subst.compress msg  in
                     uu____11195.FStar_Syntax_Syntax.n  in
                   (uu____11190, uu____11194)  in
                 (match uu____11185 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____11204))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____11210 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____11217)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____11252 when head_redex env head2 ->
                 let uu____11267 = whnf env phi1  in
                 encode_formula uu____11267 env
             | uu____11268 ->
                 let uu____11283 = encode_term phi1 env  in
                 (match uu____11283 with
                  | (tt,decls) ->
                      let tt1 =
                        let uu____11295 =
                          let uu____11296 =
                            FStar_Range.use_range
                              tt.FStar_SMTEncoding_Term.rng
                             in
                          let uu____11297 =
                            FStar_Range.use_range
                              phi1.FStar_Syntax_Syntax.pos
                             in
                          FStar_Range.rng_included uu____11296 uu____11297
                           in
                        if uu____11295
                        then tt
                        else
                          (let uu___356_11299 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___356_11299.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___356_11299.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      let uu____11300 = FStar_SMTEncoding_Term.mk_Valid tt1
                         in
                      (uu____11300, decls)))
        | uu____11301 ->
            let uu____11302 = encode_term phi1 env  in
            (match uu____11302 with
             | (tt,decls) ->
                 let tt1 =
                   let uu____11314 =
                     let uu____11315 =
                       FStar_Range.use_range tt.FStar_SMTEncoding_Term.rng
                        in
                     let uu____11316 =
                       FStar_Range.use_range phi1.FStar_Syntax_Syntax.pos  in
                     FStar_Range.rng_included uu____11315 uu____11316  in
                   if uu____11314
                   then tt
                   else
                     (let uu___357_11318 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___357_11318.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___357_11318.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 let uu____11319 = FStar_SMTEncoding_Term.mk_Valid tt1  in
                 (uu____11319, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____11363 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____11363 with
        | (vars,guards,env2,decls,uu____11402) ->
            let uu____11415 = encode_smt_patterns ps env2  in
            (match uu____11415 with
             | (pats,decls') ->
                 let uu____11458 = encode_formula body env2  in
                 (match uu____11458 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____11490;
                             FStar_SMTEncoding_Term.rng = uu____11491;_}::[])::[]
                            when
                            let uu____11506 =
                              FStar_Ident.text_of_lid
                                FStar_Parser_Const.guard_free
                               in
                            uu____11506 = gf -> []
                        | uu____11507 -> guards  in
                      let uu____11512 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____11512, body1,
                        (FStar_List.append decls
                           (FStar_List.append decls' decls'')))))
         in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi  in
       let uu____11523 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____11523 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____11532 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____11638  ->
                     match uu____11638 with
                     | (l,uu____11662) -> FStar_Ident.lid_equals op l))
              in
           (match uu____11532 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____11731,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____11823 = encode_q_body env vars pats body  in
             match uu____11823 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____11868 =
                     let uu____11879 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____11879)  in
                   FStar_SMTEncoding_Term.mkForall
                     phi1.FStar_Syntax_Syntax.pos uu____11868
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____11910 = encode_q_body env vars pats body  in
             match uu____11910 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____11954 =
                   let uu____11955 =
                     let uu____11966 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____11966)  in
                   FStar_SMTEncoding_Term.mkExists
                     phi1.FStar_Syntax_Syntax.pos uu____11955
                    in
                 (uu____11954, decls))))
