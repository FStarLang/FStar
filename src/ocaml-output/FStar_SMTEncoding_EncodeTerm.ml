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
      | FStar_Syntax_Syntax.Tm_arrow uu____182 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____195 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____202 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____203 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____220 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____237 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____239 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____239 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____257;
             FStar_Syntax_Syntax.vars = uu____258;_},uu____259)
          ->
          let uu____280 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____280 FStar_Option.isNone
      | uu____297 -> false
  
let (head_redex :
  FStar_SMTEncoding_Env.env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____308 =
        let uu____309 = FStar_Syntax_Util.un_uinst t  in
        uu____309.FStar_Syntax_Syntax.n  in
      match uu____308 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____312,uu____313,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___65_334  ->
                  match uu___65_334 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____335 -> false) rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____337 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____337 FStar_Option.isSome
      | uu____354 -> false
  
let (whnf :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____365 = head_normal env t  in
      if uu____365
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
    let uu____382 =
      let uu____383 = FStar_Syntax_Syntax.null_binder t  in [uu____383]  in
    let uu____384 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    FStar_Syntax_Util.abs uu____382 uu____384 FStar_Pervasives_Native.None
  
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
                    let uu____426 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____426
                | s ->
                    let uu____429 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____429) e)
  
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
          let uu____477 =
            let uu____482 =
              let uu____483 = FStar_Util.string_of_int arity  in
              let uu____484 = FStar_Util.string_of_int n_args  in
              FStar_Util.format3
                "Head symbol %s expects at least %s arguments; got only %s"
                head1 uu____483 uu____484
               in
            (FStar_Errors.Fatal_SMTEncodingArityMismatch, uu____482)  in
          FStar_Errors.raise_error uu____477 rng
  
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
              (let uu____523 = FStar_Util.first_N arity args  in
               match uu____523 with
               | (args1,rest) ->
                   let head2 = FStar_SMTEncoding_Util.mkApp' (head1, args1)
                      in
                   mk_Apply_args head2 rest)
            else
              (let uu____546 = FStar_SMTEncoding_Term.op_to_string head1  in
               raise_arity_mismatch uu____546 arity n_args rng)
  
let (is_app : FStar_SMTEncoding_Term.op -> Prims.bool) =
  fun uu___66_555  ->
    match uu___66_555 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____556 -> false
  
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
                       FStar_SMTEncoding_Term.freevars = uu____602;
                       FStar_SMTEncoding_Term.rng = uu____603;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____626) ->
              let uu____635 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____646 -> false) args (FStar_List.rev xs))
                 in
              if uu____635
              then FStar_SMTEncoding_Env.tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____650,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t  in
              let uu____654 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____658 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars
                           in
                        Prims.op_Negation uu____658))
                 in
              if uu____654
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____662 -> FStar_Pervasives_Native.None  in
        check_partial_applications body (FStar_List.rev vars)
  
let check_pattern_vars :
  'Auu____679 'Auu____680 .
    FStar_SMTEncoding_Env.env_t ->
      (FStar_Syntax_Syntax.bv,'Auu____679) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____680) FStar_Pervasives_Native.tuple2
          Prims.list -> unit
  =
  fun env  ->
    fun vars  ->
      fun pats  ->
        let pats1 =
          FStar_All.pipe_right pats
            (FStar_List.map
               (fun uu____738  ->
                  match uu____738 with
                  | (x,uu____744) ->
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
              let uu____752 = FStar_Syntax_Free.names hd1  in
              FStar_List.fold_left
                (fun out  ->
                   fun x  ->
                     let uu____764 = FStar_Syntax_Free.names x  in
                     FStar_Util.set_union out uu____764) uu____752 tl1
               in
            let uu____767 =
              FStar_All.pipe_right vars
                (FStar_Util.find_opt
                   (fun uu____794  ->
                      match uu____794 with
                      | (b,uu____800) ->
                          let uu____801 = FStar_Util.set_mem b pat_vars  in
                          Prims.op_Negation uu____801))
               in
            (match uu____767 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some (x,uu____807) ->
                 let pos =
                   FStar_List.fold_left
                     (fun out  ->
                        fun t  ->
                          FStar_Range.union_ranges out
                            t.FStar_Syntax_Syntax.pos)
                     hd1.FStar_Syntax_Syntax.pos tl1
                    in
                 let uu____821 =
                   let uu____826 =
                     let uu____827 = FStar_Syntax_Print.bv_to_string x  in
                     FStar_Util.format1
                       "SMT pattern misses at least one bound variable: %s"
                       uu____827
                      in
                   (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                     uu____826)
                    in
                 FStar_Errors.log_issue pos uu____821)
  
type label =
  (FStar_SMTEncoding_Term.fv,Prims.string,FStar_Range.range)
    FStar_Pervasives_Native.tuple3[@@deriving show]
type labels = label Prims.list[@@deriving show]
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
    }[@@deriving show]
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
        | FStar_Syntax_Syntax.Tm_arrow uu____1102 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____1115 ->
            let uu____1122 = FStar_Syntax_Util.unrefine t1  in
            aux true uu____1122
        | uu____1123 ->
            if norm1
            then let uu____1124 = whnf env t1  in aux false uu____1124
            else
              (let uu____1126 =
                 let uu____1127 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let uu____1128 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____1127 uu____1128
                  in
               failwith uu____1126)
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
    | FStar_Syntax_Syntax.Tm_refine (bv,uu____1162) ->
        curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort
    | uu____1167 ->
        let uu____1168 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____1168)
  
let is_arithmetic_primitive :
  'Auu____1185 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____1185 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1207::uu____1208::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1212::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____1215 -> false
  
let (isInteger : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____1238 -> false
  
let (getInteger : FStar_Syntax_Syntax.term' -> Prims.int) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____1255 -> failwith "Expected an Integer term"
  
let is_BitVector_primitive :
  'Auu____1262 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1262)
        FStar_Pervasives_Native.tuple2 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____1303)::uu____1304::uu____1305::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____1356)::uu____1357::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____1394 -> false
  
let rec (encode_const :
  FStar_Const.sconst ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decl Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun c  ->
    fun env  ->
      match c with
      | FStar_Const.Const_unit  -> (FStar_SMTEncoding_Term.mk_Term_unit, [])
      | FStar_Const.Const_bool (true ) ->
          let uu____1715 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue  in
          (uu____1715, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____1718 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse  in
          (uu____1718, [])
      | FStar_Const.Const_char c1 ->
          let uu____1722 =
            let uu____1723 =
              let uu____1730 =
                let uu____1733 =
                  let uu____1734 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1)
                     in
                  FStar_SMTEncoding_Term.boxInt uu____1734  in
                [uu____1733]  in
              ("FStar.Char.__char_of_int", uu____1730)  in
            FStar_SMTEncoding_Util.mkApp uu____1723  in
          (uu____1722, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____1750 =
            let uu____1751 = FStar_SMTEncoding_Util.mkInteger i  in
            FStar_SMTEncoding_Term.boxInt uu____1751  in
          (uu____1750, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.FStar_SMTEncoding_Env.tcenv).FStar_TypeChecker_Env.dsenv
              repr sw FStar_Range.dummyRange
             in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____1772) ->
          let uu____1773 =
            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.string_const s
             in
          (uu____1773, [])
      | FStar_Const.Const_range uu____1776 ->
          let uu____1777 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          (uu____1777, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | c1 ->
          let uu____1783 =
            let uu____1784 = FStar_Syntax_Print.const_to_string c1  in
            FStar_Util.format1 "Unhandled constant: %s" uu____1784  in
          failwith uu____1783

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
        (let uu____1813 =
           FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
             FStar_Options.Low
            in
         if uu____1813
         then
           let uu____1814 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____1814
         else ());
        (let uu____1816 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____1900  ->
                   fun b  ->
                     match uu____1900 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____1979 =
                           let x =
                             FStar_SMTEncoding_Env.unmangle
                               (FStar_Pervasives_Native.fst b)
                              in
                           let uu____1995 =
                             FStar_SMTEncoding_Env.gen_term_var env1 x  in
                           match uu____1995 with
                           | (xxsym,xx,env') ->
                               let uu____2019 =
                                 let uu____2024 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____2024 env1 xx
                                  in
                               (match uu____2019 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x))
                            in
                         (match uu____1979 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____1816 with
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
          let uu____2183 = encode_term t env  in
          match uu____2183 with
          | (t1,decls) ->
              let uu____2194 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____2194, decls)

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
          let uu____2205 = encode_term t env  in
          match uu____2205 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____2220 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____2220, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____2222 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____2222, decls))

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
        let uu____2228 = encode_args args_e env  in
        match uu____2228 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____2247 -> failwith "Impossible"  in
            let unary arg_tms1 =
              let uu____2258 = FStar_List.hd arg_tms1  in
              FStar_SMTEncoding_Term.unboxInt uu____2258  in
            let binary arg_tms1 =
              let uu____2273 =
                let uu____2274 = FStar_List.hd arg_tms1  in
                FStar_SMTEncoding_Term.unboxInt uu____2274  in
              let uu____2275 =
                let uu____2276 =
                  let uu____2277 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____2277  in
                FStar_SMTEncoding_Term.unboxInt uu____2276  in
              (uu____2273, uu____2275)  in
            let mk_default uu____2285 =
              let uu____2286 =
                FStar_SMTEncoding_Env.lookup_free_var_sym env
                  head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____2286 with
              | (fname,fuel_args,arity) ->
                  let args = FStar_List.append fuel_args arg_tms  in
                  maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity
                    args
               in
            let mk_l op mk_args ts =
              let uu____2348 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____2348
              then
                let uu____2349 =
                  let uu____2350 = mk_args ts  in op uu____2350  in
                FStar_All.pipe_right uu____2349 FStar_SMTEncoding_Term.boxInt
              else mk_default ()  in
            let mk_nl nm op ts =
              let uu____2385 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____2385
              then
                let uu____2386 = binary ts  in
                match uu____2386 with
                | (t1,t2) ->
                    let uu____2393 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____2393
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____2397 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____2397
                 then
                   let uu____2398 =
                     let uu____2399 = binary ts  in op uu____2399  in
                   FStar_All.pipe_right uu____2398
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
            let uu____2560 =
              let uu____2570 =
                FStar_List.tryFind
                  (fun uu____2594  ->
                     match uu____2594 with
                     | (l,uu____2604) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____2570 FStar_Util.must  in
            (match uu____2560 with
             | (uu____2648,op) ->
                 let uu____2660 = op arg_tms  in (uu____2660, decls))

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
        let uu____2668 = FStar_List.hd args_e  in
        match uu____2668 with
        | (tm_sz,uu____2676) ->
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let uu____2686 =
                FStar_Util.smap_try_find env.FStar_SMTEncoding_Env.cache
                  sz_key
                 in
              match uu____2686 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None  ->
                  let t_decls1 = FStar_SMTEncoding_Term.mkBvConstructor sz
                     in
                  ((let uu____2694 =
                      FStar_SMTEncoding_Env.mk_cache_entry env "" [] []  in
                    FStar_Util.smap_add env.FStar_SMTEncoding_Env.cache
                      sz_key uu____2694);
                   t_decls1)
               in
            let uu____2695 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____2715::(sz_arg,uu____2717)::uu____2718::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____2767 =
                    let uu____2770 = FStar_List.tail args_e  in
                    FStar_List.tail uu____2770  in
                  let uu____2773 =
                    let uu____2776 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____2776  in
                  (uu____2767, uu____2773)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____2782::(sz_arg,uu____2784)::uu____2785::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____2834 =
                    let uu____2835 = FStar_Syntax_Print.term_to_string sz_arg
                       in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____2835
                     in
                  failwith uu____2834
              | uu____2844 ->
                  let uu____2851 = FStar_List.tail args_e  in
                  (uu____2851, FStar_Pervasives_Native.None)
               in
            (match uu____2695 with
             | (arg_tms,ext_sz) ->
                 let uu____2874 = encode_args arg_tms env  in
                 (match uu____2874 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____2895 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____2906 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____2906  in
                      let unary_arith arg_tms2 =
                        let uu____2917 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____2917  in
                      let binary arg_tms2 =
                        let uu____2932 =
                          let uu____2933 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____2933
                           in
                        let uu____2934 =
                          let uu____2935 =
                            let uu____2936 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____2936  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____2935
                           in
                        (uu____2932, uu____2934)  in
                      let binary_arith arg_tms2 =
                        let uu____2953 =
                          let uu____2954 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____2954
                           in
                        let uu____2955 =
                          let uu____2956 =
                            let uu____2957 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____2957  in
                          FStar_SMTEncoding_Term.unboxInt uu____2956  in
                        (uu____2953, uu____2955)  in
                      let mk_bv op mk_args resBox ts =
                        let uu____3015 =
                          let uu____3016 = mk_args ts  in op uu____3016  in
                        FStar_All.pipe_right uu____3015 resBox  in
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
                        let uu____3148 =
                          let uu____3153 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____3153  in
                        let uu____3155 =
                          let uu____3160 =
                            let uu____3161 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____3161  in
                          FStar_SMTEncoding_Term.boxBitVec uu____3160  in
                        mk_bv uu____3148 unary uu____3155 arg_tms2  in
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
                      let uu____3394 =
                        let uu____3404 =
                          FStar_List.tryFind
                            (fun uu____3428  ->
                               match uu____3428 with
                               | (l,uu____3438) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____3404 FStar_Util.must  in
                      (match uu____3394 with
                       | (uu____3484,op) ->
                           let uu____3496 = op arg_tms1  in
                           (uu____3496, (FStar_List.append sz_decls decls)))))

and (encode_deeply_embedded_quantifier :
  FStar_Syntax_Syntax.term ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let env1 =
        let uu___70_3506 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___70_3506.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___70_3506.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___70_3506.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___70_3506.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___70_3506.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.cache =
            (uu___70_3506.FStar_SMTEncoding_Env.cache);
          FStar_SMTEncoding_Env.nolabels =
            (uu___70_3506.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name =
            (uu___70_3506.FStar_SMTEncoding_Env.use_zfuel_name);
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___70_3506.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___70_3506.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier = true
        }  in
      let uu____3507 = encode_term t env1  in
      match uu____3507 with
      | (tm,decls) ->
          let vars = FStar_SMTEncoding_Term.free_variables tm  in
          let tm1 =
            match tm.FStar_SMTEncoding_Term.tm with
            | FStar_SMTEncoding_Term.App
                (uu____3520,{
                              FStar_SMTEncoding_Term.tm =
                                FStar_SMTEncoding_Term.FreeV uu____3521;
                              FStar_SMTEncoding_Term.freevars = uu____3522;
                              FStar_SMTEncoding_Term.rng = uu____3523;_}::
                 {
                   FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV
                     uu____3524;
                   FStar_SMTEncoding_Term.freevars = uu____3525;
                   FStar_SMTEncoding_Term.rng = uu____3526;_}::[])
                -> FStar_SMTEncoding_Term.mk_id_wrapper tm
            | uu____3553 -> tm  in
          let valid_tm = FStar_SMTEncoding_Term.mk_Valid tm1  in
          let key =
            FStar_SMTEncoding_Term.mkForall t.FStar_Syntax_Syntax.pos
              ([], vars, valid_tm)
             in
          let tkey_hash = FStar_SMTEncoding_Term.hash_of_term key  in
          let uu____3563 =
            FStar_Util.smap_try_find env1.FStar_SMTEncoding_Env.cache
              tkey_hash
             in
          (match uu____3563 with
           | FStar_Pervasives_Native.Some uu____3570 -> (tm1, decls)
           | uu____3571 ->
               let uu____3574 = encode_formula t env1  in
               (match uu____3574 with
                | (phi,decls') ->
                    let interp =
                      match vars with
                      | [] ->
                          let uu____3590 =
                            let uu____3595 =
                              FStar_SMTEncoding_Term.mk_Valid tm1  in
                            (uu____3595, phi)  in
                          FStar_SMTEncoding_Util.mkIff uu____3590
                      | uu____3596 ->
                          let uu____3597 =
                            let uu____3608 =
                              let uu____3609 =
                                let uu____3614 =
                                  FStar_SMTEncoding_Term.mk_Valid tm1  in
                                (uu____3614, phi)  in
                              FStar_SMTEncoding_Util.mkIff uu____3609  in
                            ([[valid_tm]], vars, uu____3608)  in
                          FStar_SMTEncoding_Term.mkForall
                            t.FStar_Syntax_Syntax.pos uu____3597
                       in
                    let ax =
                      let uu____3624 =
                        let uu____3631 =
                          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                            "l_quant_interp"
                           in
                        (interp,
                          (FStar_Pervasives_Native.Some
                             "Interpretation of deeply embedded quantifier"),
                          uu____3631)
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____3624  in
                    ((let uu____3635 =
                        FStar_SMTEncoding_Env.mk_cache_entry env1 "" [] [ax]
                         in
                      FStar_Util.smap_add env1.FStar_SMTEncoding_Env.cache
                        tkey_hash uu____3635);
                     (tm1,
                       (FStar_List.append decls
                          (FStar_List.append decls' [ax]))))))

and (encode_term :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____3646 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____3646
       then
         let uu____3647 = FStar_Syntax_Print.tag_of_term t  in
         let uu____3648 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____3649 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____3647 uu____3648
           uu____3649
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____3655 ->
           let uu____3680 =
             let uu____3681 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____3682 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____3683 = FStar_Syntax_Print.term_to_string t0  in
             let uu____3684 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____3681
               uu____3682 uu____3683 uu____3684
              in
           failwith uu____3680
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____3689 =
             let uu____3690 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____3691 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____3692 = FStar_Syntax_Print.term_to_string t0  in
             let uu____3693 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____3690
               uu____3691 uu____3692 uu____3693
              in
           failwith uu____3689
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____3699 = FStar_Syntax_Util.unfold_lazy i  in
           encode_term uu____3699 env
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____3701 =
             let uu____3702 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____3702
              in
           failwith uu____3701
       | FStar_Syntax_Syntax.Tm_ascribed (t1,(k,uu____3709),uu____3710) ->
           let uu____3759 =
             match k with
             | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
             | uu____3767 -> false  in
           if uu____3759
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t1 env
       | FStar_Syntax_Syntax.Tm_quoted (qt,uu____3784) ->
           let tv =
             let uu____3790 = FStar_Reflection_Basic.inspect_ln qt  in
             FStar_Syntax_Embeddings.embed
               FStar_Reflection_Embeddings.e_term_view
               t.FStar_Syntax_Syntax.pos uu____3790
              in
           let t1 =
             let uu____3794 =
               let uu____3803 = FStar_Syntax_Syntax.as_arg tv  in
               [uu____3803]  in
             FStar_Syntax_Util.mk_app
               (FStar_Reflection_Data.refl_constant_term
                  FStar_Reflection_Data.fstar_refl_pack_ln) uu____3794
              in
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_pattern uu____3805) ->
           encode_term t1
             (let uu___71_3821 = env  in
              {
                FStar_SMTEncoding_Env.bvar_bindings =
                  (uu___71_3821.FStar_SMTEncoding_Env.bvar_bindings);
                FStar_SMTEncoding_Env.fvar_bindings =
                  (uu___71_3821.FStar_SMTEncoding_Env.fvar_bindings);
                FStar_SMTEncoding_Env.depth =
                  (uu___71_3821.FStar_SMTEncoding_Env.depth);
                FStar_SMTEncoding_Env.tcenv =
                  (uu___71_3821.FStar_SMTEncoding_Env.tcenv);
                FStar_SMTEncoding_Env.warn =
                  (uu___71_3821.FStar_SMTEncoding_Env.warn);
                FStar_SMTEncoding_Env.cache =
                  (uu___71_3821.FStar_SMTEncoding_Env.cache);
                FStar_SMTEncoding_Env.nolabels =
                  (uu___71_3821.FStar_SMTEncoding_Env.nolabels);
                FStar_SMTEncoding_Env.use_zfuel_name =
                  (uu___71_3821.FStar_SMTEncoding_Env.use_zfuel_name);
                FStar_SMTEncoding_Env.encode_non_total_function_typ =
                  (uu___71_3821.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                FStar_SMTEncoding_Env.current_module_name =
                  (uu___71_3821.FStar_SMTEncoding_Env.current_module_name);
                FStar_SMTEncoding_Env.encoding_quantifier = false
              })
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____3823) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = FStar_SMTEncoding_Env.lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____3833 = head_redex env t  in
           if uu____3833
           then let uu____3838 = whnf env t  in encode_term uu____3838 env
           else
             (let uu____3840 =
                FStar_SMTEncoding_Env.lookup_free_var_name env
                  v1.FStar_Syntax_Syntax.fv_name
                 in
              match uu____3840 with
              | (uu____3849,arity) ->
                  let tok =
                    FStar_SMTEncoding_Env.lookup_free_var env
                      v1.FStar_Syntax_Syntax.fv_name
                     in
                  let aux_decls =
                    if arity > (Prims.parse_int "0")
                    then
                      match tok.FStar_SMTEncoding_Term.tm with
                      | FStar_SMTEncoding_Term.FreeV uu____3859 ->
                          let uu____3864 =
                            let uu____3865 =
                              let uu____3872 =
                                FStar_SMTEncoding_Term.kick_partial_app tok
                                 in
                              let uu____3873 =
                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                  "@kick_partial_app"
                                 in
                              (uu____3872,
                                (FStar_Pervasives_Native.Some
                                   "kick_partial_app"), uu____3873)
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____3865  in
                          [uu____3864]
                      | FStar_SMTEncoding_Term.App (uu____3876,[]) ->
                          let uu____3879 =
                            let uu____3880 =
                              let uu____3887 =
                                FStar_SMTEncoding_Term.kick_partial_app tok
                                 in
                              let uu____3888 =
                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                  "@kick_partial_app"
                                 in
                              (uu____3887,
                                (FStar_Pervasives_Native.Some
                                   "kick_partial_app"), uu____3888)
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____3880  in
                          [uu____3879]
                      | uu____3891 -> []
                    else []  in
                  (tok, aux_decls))
       | FStar_Syntax_Syntax.Tm_type uu____3895 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3899) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.FStar_SMTEncoding_Env.current_module_name
              in
           let uu____3924 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____3924 with
            | (binders1,res) ->
                let uu____3935 =
                  (env.FStar_SMTEncoding_Env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____3935
                then
                  let uu____3940 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____3940 with
                   | (vars,guards,env',decls,uu____3965) ->
                       let fsym =
                         let uu____3983 =
                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                             "f"
                            in
                         (uu____3983, FStar_SMTEncoding_Term.Term_sort)  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____3986 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___72_3995 =
                              env.FStar_SMTEncoding_Env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___72_3995.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___72_3995.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___72_3995.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___72_3995.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___72_3995.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___72_3995.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___72_3995.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___72_3995.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___72_3995.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___72_3995.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___72_3995.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___72_3995.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___72_3995.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___72_3995.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___72_3995.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___72_3995.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___72_3995.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___72_3995.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___72_3995.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___72_3995.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___72_3995.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___72_3995.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___72_3995.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___72_3995.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___72_3995.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___72_3995.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___72_3995.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___72_3995.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___72_3995.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___72_3995.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___72_3995.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___72_3995.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___72_3995.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___72_3995.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___72_3995.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___72_3995.FStar_TypeChecker_Env.dep_graph)
                            }) res
                          in
                       (match uu____3986 with
                        | (pre_opt,res_t) ->
                            let uu____4006 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____4006 with
                             | (res_pred,decls') ->
                                 let uu____4017 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____4030 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____4030, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____4034 =
                                         encode_formula pre env'  in
                                       (match uu____4034 with
                                        | (guard,decls0) ->
                                            let uu____4047 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____4047, decls0))
                                    in
                                 (match uu____4017 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____4059 =
                                          let uu____4070 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____4070)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t.FStar_Syntax_Syntax.pos
                                          uu____4059
                                         in
                                      let cvars =
                                        let uu____4088 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____4088
                                          (FStar_List.filter
                                             (fun uu____4102  ->
                                                match uu____4102 with
                                                | (x,uu____4108) ->
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
                                      let uu____4127 =
                                        FStar_Util.smap_try_find
                                          env.FStar_SMTEncoding_Env.cache
                                          tkey_hash
                                         in
                                      (match uu____4127 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____4135 =
                                             let uu____4136 =
                                               let uu____4143 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV)
                                                  in
                                               ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                                 uu____4143)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4136
                                              in
                                           (uu____4135,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (FStar_SMTEncoding_Env.use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____4163 =
                                               let uu____4164 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____4164
                                                in
                                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                               uu____4163
                                              in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars
                                              in
                                           let caption =
                                             let uu____4175 =
                                               FStar_Options.log_queries ()
                                                in
                                             if uu____4175
                                             then
                                               let uu____4178 =
                                                 let uu____4179 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env.FStar_SMTEncoding_Env.tcenv
                                                     t0
                                                    in
                                                 FStar_Util.replace_char
                                                   uu____4179 10 32
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____4178
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
                                             let uu____4189 =
                                               let uu____4196 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars
                                                  in
                                               (tsym, uu____4196)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4189
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
                                             let uu____4208 =
                                               let uu____4215 =
                                                 FStar_SMTEncoding_Term.mkForall
                                                   t0.FStar_Syntax_Syntax.pos
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind)
                                                  in
                                               (uu____4215,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name)
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4208
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
                                             let uu____4236 =
                                               let uu____4243 =
                                                 let uu____4244 =
                                                   let uu____4255 =
                                                     let uu____4256 =
                                                       let uu____4261 =
                                                         let uu____4262 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f
                                                            in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____4262
                                                          in
                                                       (f_has_t, uu____4261)
                                                        in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____4256
                                                      in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____4255)
                                                    in
                                                 let uu____4281 =
                                                   mkForall_fuel
                                                     t0.FStar_Syntax_Syntax.pos
                                                    in
                                                 uu____4281 uu____4244  in
                                               (uu____4243,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4236
                                              in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym
                                                in
                                             let uu____4300 =
                                               let uu____4307 =
                                                 let uu____4308 =
                                                   let uu____4319 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp)
                                                      in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____4319)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   t0.FStar_Syntax_Syntax.pos
                                                   uu____4308
                                                  in
                                               (uu____4307,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4300
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
                                           ((let uu____4344 =
                                               FStar_SMTEncoding_Env.mk_cache_entry
                                                 env tsym cvar_sorts t_decls1
                                                in
                                             FStar_Util.smap_add
                                               env.FStar_SMTEncoding_Env.cache
                                               tkey_hash uu____4344);
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
                     let uu____4359 =
                       let uu____4366 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____4366,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____4359  in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)  in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym  in
                     let uu____4378 =
                       let uu____4385 =
                         let uu____4386 =
                           let uu____4397 =
                             let uu____4398 =
                               let uu____4403 =
                                 let uu____4404 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____4404
                                  in
                               (f_has_t, uu____4403)  in
                             FStar_SMTEncoding_Util.mkImp uu____4398  in
                           ([[f_has_t]], [fsym], uu____4397)  in
                         let uu____4427 =
                           mkForall_fuel t0.FStar_Syntax_Syntax.pos  in
                         uu____4427 uu____4386  in
                       (uu____4385, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____4378  in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____4446 ->
           let uu____4453 =
             let uu____4458 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.Weak;
                 FStar_TypeChecker_Normalize.HNF;
                 FStar_TypeChecker_Normalize.EraseUniverses]
                 env.FStar_SMTEncoding_Env.tcenv t0
                in
             match uu____4458 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____4465;
                 FStar_Syntax_Syntax.vars = uu____4466;_} ->
                 let uu____4473 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____4473 with
                  | (b,f1) ->
                      let uu____4498 =
                        let uu____4499 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____4499  in
                      (uu____4498, f1))
             | uu____4508 -> failwith "impossible"  in
           (match uu____4453 with
            | (x,f) ->
                let uu____4519 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____4519 with
                 | (base_t,decls) ->
                     let uu____4530 =
                       FStar_SMTEncoding_Env.gen_term_var env x  in
                     (match uu____4530 with
                      | (x1,xtm,env') ->
                          let uu____4544 = encode_formula f env'  in
                          (match uu____4544 with
                           | (refinement,decls') ->
                               let uu____4555 =
                                 FStar_SMTEncoding_Env.fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____4555 with
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
                                      let uu____4571 =
                                        let uu____4574 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____4581 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____4574
                                          uu____4581
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____4571
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____4614  ->
                                              match uu____4614 with
                                              | (y,uu____4620) ->
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
                                    let uu____4653 =
                                      FStar_Util.smap_try_find
                                        env.FStar_SMTEncoding_Env.cache
                                        tkey_hash
                                       in
                                    (match uu____4653 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____4661 =
                                           let uu____4662 =
                                             let uu____4669 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV)
                                                in
                                             ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                               uu____4669)
                                              in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____4662
                                            in
                                         (uu____4661,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (FStar_SMTEncoding_Env.use_cache_entry
                                                    cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.FStar_SMTEncoding_Env.current_module_name
                                            in
                                         let tsym =
                                           let uu____4690 =
                                             let uu____4691 =
                                               let uu____4692 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____4692
                                                in
                                             Prims.strcat module_name
                                               uu____4691
                                              in
                                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                             uu____4690
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
                                           let uu____4706 =
                                             let uu____4713 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1
                                                in
                                             (tsym, uu____4713)  in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____4706
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
                                           let uu____4728 =
                                             let uu____4735 =
                                               let uu____4736 =
                                                 let uu____4747 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base)
                                                    in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____4747)
                                                  in
                                               FStar_SMTEncoding_Term.mkForall
                                                 t0.FStar_Syntax_Syntax.pos
                                                 uu____4736
                                                in
                                             (uu____4735,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4728
                                            in
                                         let t_kinding =
                                           let uu____4765 =
                                             let uu____4772 =
                                               FStar_SMTEncoding_Term.mkForall
                                                 t0.FStar_Syntax_Syntax.pos
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind)
                                                in
                                             (uu____4772,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4765
                                            in
                                         let t_interp =
                                           let uu____4790 =
                                             let uu____4797 =
                                               let uu____4798 =
                                                 let uu____4809 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding)
                                                    in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____4809)
                                                  in
                                               FStar_SMTEncoding_Term.mkForall
                                                 t0.FStar_Syntax_Syntax.pos
                                                 uu____4798
                                                in
                                             (uu____4797,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement_interpretation"),
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4790
                                            in
                                         let t_decls1 =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1])
                                            in
                                         ((let uu____4838 =
                                             FStar_SMTEncoding_Env.mk_cache_entry
                                               env tsym cvar_sorts t_decls1
                                              in
                                           FStar_Util.smap_add
                                             env.FStar_SMTEncoding_Env.cache
                                             tkey_hash uu____4838);
                                          (t1, t_decls1))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____4868 = FStar_Syntax_Unionfind.uvar_id uv  in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____4868  in
           let uu____4869 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm  in
           (match uu____4869 with
            | (t_has_k,decls) ->
                let d =
                  let uu____4881 =
                    let uu____4888 =
                      let uu____4889 =
                        let uu____4890 =
                          let uu____4891 = FStar_Syntax_Unionfind.uvar_id uv
                             in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____4891
                           in
                        FStar_Util.format1 "uvar_typing_%s" uu____4890  in
                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                        uu____4889
                       in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____4888)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____4881  in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____4896 ->
           let uu____4911 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____4911 with
            | (head1,args_e) ->
                let uu____4952 =
                  let uu____4965 =
                    let uu____4966 = FStar_Syntax_Subst.compress head1  in
                    uu____4966.FStar_Syntax_Syntax.n  in
                  (uu____4965, args_e)  in
                (match uu____4952 with
                 | uu____4981 when head_redex env head1 ->
                     let uu____4994 = whnf env t  in
                     encode_term uu____4994 env
                 | uu____4995 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____5014 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5028) when
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
                       FStar_Syntax_Syntax.pos = uu____5046;
                       FStar_Syntax_Syntax.vars = uu____5047;_},uu____5048),uu____5049)
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
                       FStar_Syntax_Syntax.pos = uu____5071;
                       FStar_Syntax_Syntax.vars = uu____5072;_},uu____5073),uu____5074::
                    (v1,uu____5076)::(v2,uu____5078)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____5129 = encode_term v1 env  in
                     (match uu____5129 with
                      | (v11,decls1) ->
                          let uu____5140 = encode_term v2 env  in
                          (match uu____5140 with
                           | (v21,decls2) ->
                               let uu____5151 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21
                                  in
                               (uu____5151,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____5155::(v1,uu____5157)::(v2,uu____5159)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____5206 = encode_term v1 env  in
                     (match uu____5206 with
                      | (v11,decls1) ->
                          let uu____5217 = encode_term v2 env  in
                          (match uu____5217 with
                           | (v21,decls2) ->
                               let uu____5228 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21
                                  in
                               (uu____5228,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____5232)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____5258)::(rng,uu____5260)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____5295) ->
                     let e0 =
                       let uu____5313 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg
                         env.FStar_SMTEncoding_Env.tcenv head1 uu____5313
                        in
                     ((let uu____5321 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug
                              env.FStar_SMTEncoding_Env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____5321
                       then
                         let uu____5322 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____5322
                       else ());
                      (let e =
                         let uu____5327 =
                           let uu____5332 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____5333 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____5332
                             uu____5333
                            in
                         uu____5327 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____5342),(arg,uu____5344)::[]) -> encode_term arg env
                 | uu____5369 ->
                     let uu____5382 = encode_args args_e env  in
                     (match uu____5382 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____5439 = encode_term head1 env  in
                            match uu____5439 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____5503 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____5503 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____5581  ->
                                                 fun uu____5582  ->
                                                   match (uu____5581,
                                                           uu____5582)
                                                   with
                                                   | ((bv,uu____5604),
                                                      (a,uu____5606)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____5624 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____5624
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____5629 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm
                                             in
                                          (match uu____5629 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type
                                                  in
                                               let e_typing =
                                                 let uu____5644 =
                                                   let uu____5651 =
                                                     FStar_SMTEncoding_Term.mkForall
                                                       t0.FStar_Syntax_Syntax.pos
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____5660 =
                                                     let uu____5661 =
                                                       let uu____5662 =
                                                         let uu____5663 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm
                                                            in
                                                         FStar_Util.digest_of_string
                                                           uu____5663
                                                          in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____5662
                                                        in
                                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                       uu____5661
                                                      in
                                                   (uu____5651,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____5660)
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____5644
                                                  in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing])))))))
                             in
                          let encode_full_app fv =
                            let uu____5682 =
                              FStar_SMTEncoding_Env.lookup_free_var_sym env
                                fv
                               in
                            match uu____5682 with
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
                                   FStar_Syntax_Syntax.pos = uu____5714;
                                   FStar_Syntax_Syntax.vars = uu____5715;_},uu____5716)
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
                                   FStar_Syntax_Syntax.pos = uu____5727;
                                   FStar_Syntax_Syntax.vars = uu____5728;_},uu____5729)
                                ->
                                let uu____5734 =
                                  let uu____5735 =
                                    let uu____5740 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____5740
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____5735
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____5734
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____5770 =
                                  let uu____5771 =
                                    let uu____5776 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____5776
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____5771
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____5770
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____5805,(FStar_Util.Inl t1,uu____5807),uu____5808)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____5857,(FStar_Util.Inr c,uu____5859),uu____5860)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____5909 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____5936 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.Weak;
                                     FStar_TypeChecker_Normalize.HNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.FStar_SMTEncoding_Env.tcenv
                                     head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____5936
                                  in
                               let uu____5937 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____5937 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____5953;
                                            FStar_Syntax_Syntax.vars =
                                              uu____5954;_},uu____5955)
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
                                     | uu____5969 ->
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
           let uu____6018 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____6018 with
            | (bs1,body1,opening) ->
                let fallback uu____6043 =
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
                  let uu____6050 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort)
                     in
                  (uu____6050, [decl])  in
                let is_impure rc =
                  let uu____6059 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                      env.FStar_SMTEncoding_Env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____6059 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____6071 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_All.pipe_right uu____6071
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  let uu____6089 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                     in
                  if uu____6089
                  then
                    let uu____6092 = FStar_Syntax_Syntax.mk_Total res_typ  in
                    FStar_Pervasives_Native.Some uu____6092
                  else
                    (let uu____6094 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid
                        in
                     if uu____6094
                     then
                       let uu____6097 = FStar_Syntax_Syntax.mk_GTotal res_typ
                          in
                       FStar_Pervasives_Native.Some uu____6097
                     else FStar_Pervasives_Native.None)
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____6104 =
                         let uu____6109 =
                           let uu____6110 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____6110
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____6109)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____6104);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____6112 =
                       (is_impure rc) &&
                         (let uu____6114 =
                            FStar_TypeChecker_Env.is_reifiable
                              env.FStar_SMTEncoding_Env.tcenv rc
                             in
                          Prims.op_Negation uu____6114)
                        in
                     if uu____6112
                     then fallback ()
                     else
                       (let cache_size =
                          FStar_Util.smap_size
                            env.FStar_SMTEncoding_Env.cache
                           in
                        let uu____6121 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____6121 with
                        | (vars,guards,envbody,decls,uu____6146) ->
                            let body2 =
                              let uu____6160 =
                                FStar_TypeChecker_Env.is_reifiable
                                  env.FStar_SMTEncoding_Env.tcenv rc
                                 in
                              if uu____6160
                              then
                                FStar_TypeChecker_Util.reify_body
                                  env.FStar_SMTEncoding_Env.tcenv body1
                              else body1  in
                            let uu____6162 = encode_term body2 envbody  in
                            (match uu____6162 with
                             | (body3,decls') ->
                                 let uu____6173 =
                                   let uu____6182 = codomain_eff rc  in
                                   match uu____6182 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____6201 = encode_term tfun env
                                          in
                                       (match uu____6201 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____6173 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____6233 =
                                          let uu____6244 =
                                            let uu____6245 =
                                              let uu____6250 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____6250, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____6245
                                             in
                                          ([], vars, uu____6244)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t0.FStar_Syntax_Syntax.pos
                                          uu____6233
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
                                            let uu____6262 =
                                              let uu____6265 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1
                                                 in
                                              FStar_List.append uu____6265
                                                cvars
                                               in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____6262
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
                                      let uu____6284 =
                                        FStar_Util.smap_try_find
                                          env.FStar_SMTEncoding_Env.cache
                                          tkey_hash
                                         in
                                      (match uu____6284 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____6292 =
                                             let uu____6293 =
                                               let uu____6300 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1
                                                  in
                                               ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                                 uu____6300)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6293
                                              in
                                           (uu____6292,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (FStar_SMTEncoding_Env.use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____6311 =
                                             is_an_eta_expansion env vars
                                               body3
                                              in
                                           (match uu____6311 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____6322 =
                                                    let uu____6323 =
                                                      FStar_Util.smap_size
                                                        env.FStar_SMTEncoding_Env.cache
                                                       in
                                                    uu____6323 = cache_size
                                                     in
                                                  if uu____6322
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
                                                    let uu____6339 =
                                                      let uu____6340 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash
                                                         in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____6340
                                                       in
                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                      uu____6339
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
                                                  let uu____6347 =
                                                    let uu____6354 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    (fsym, uu____6354)  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____6347
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
                                                      let uu____6372 =
                                                        let uu____6373 =
                                                          let uu____6380 =
                                                            FStar_SMTEncoding_Term.mkForall
                                                              t0.FStar_Syntax_Syntax.pos
                                                              ([[f]], cvars1,
                                                                f_has_t)
                                                             in
                                                          (uu____6380,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name)
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____6373
                                                         in
                                                      [uu____6372]
                                                   in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym
                                                     in
                                                  let uu____6393 =
                                                    let uu____6400 =
                                                      let uu____6401 =
                                                        let uu____6412 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3)
                                                           in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____6412)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        t0.FStar_Syntax_Syntax.pos
                                                        uu____6401
                                                       in
                                                    (uu____6400,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____6393
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
                                                ((let uu____6429 =
                                                    FStar_SMTEncoding_Env.mk_cache_entry
                                                      env fsym cvar_sorts
                                                      f_decls
                                                     in
                                                  FStar_Util.smap_add
                                                    env.FStar_SMTEncoding_Env.cache
                                                    tkey_hash uu____6429);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____6432,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____6433;
                          FStar_Syntax_Syntax.lbunivs = uu____6434;
                          FStar_Syntax_Syntax.lbtyp = uu____6435;
                          FStar_Syntax_Syntax.lbeff = uu____6436;
                          FStar_Syntax_Syntax.lbdef = uu____6437;
                          FStar_Syntax_Syntax.lbattrs = uu____6438;
                          FStar_Syntax_Syntax.lbpos = uu____6439;_}::uu____6440),uu____6441)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____6471;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____6473;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____6475;
                FStar_Syntax_Syntax.lbpos = uu____6476;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____6500 ->
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
              let uu____6570 =
                let uu____6575 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____6575 env  in
              match uu____6570 with
              | (ee1,decls1) ->
                  let uu____6596 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____6596 with
                   | (xs,e21) ->
                       let uu____6621 = FStar_List.hd xs  in
                       (match uu____6621 with
                        | (x1,uu____6635) ->
                            let env' =
                              FStar_SMTEncoding_Env.push_term_var env x1 ee1
                               in
                            let uu____6637 = encode_body e21 env'  in
                            (match uu____6637 with
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
            let uu____6669 =
              let uu____6676 =
                let uu____6677 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____6677  in
              FStar_SMTEncoding_Env.gen_term_var env uu____6676  in
            match uu____6669 with
            | (scrsym,scr',env1) ->
                let uu____6685 = encode_term e env1  in
                (match uu____6685 with
                 | (scr,decls) ->
                     let uu____6696 =
                       let encode_branch b uu____6725 =
                         match uu____6725 with
                         | (else_case,decls1) ->
                             let uu____6744 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____6744 with
                              | (p,w,br) ->
                                  let uu____6770 = encode_pat env1 p  in
                                  (match uu____6770 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____6807  ->
                                                   match uu____6807 with
                                                   | (x,t) ->
                                                       FStar_SMTEncoding_Env.push_term_var
                                                         env2 x t) env1)
                                          in
                                       let uu____6814 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____6836 =
                                               encode_term w1 env2  in
                                             (match uu____6836 with
                                              | (w2,decls2) ->
                                                  let uu____6849 =
                                                    let uu____6850 =
                                                      let uu____6855 =
                                                        let uu____6856 =
                                                          let uu____6861 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____6861)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____6856
                                                         in
                                                      (guard, uu____6855)  in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____6850
                                                     in
                                                  (uu____6849, decls2))
                                          in
                                       (match uu____6814 with
                                        | (guard1,decls2) ->
                                            let uu____6874 =
                                              encode_br br env2  in
                                            (match uu____6874 with
                                             | (br1,decls3) ->
                                                 let uu____6887 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____6887,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____6696 with
                      | (match_tm,decls1) ->
                          let uu____6906 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange
                             in
                          (uu____6906, decls1)))

and (encode_pat :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.pat ->
      (FStar_SMTEncoding_Env.env_t,pattern) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun pat  ->
      (let uu____6946 =
         FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
           FStar_Options.Low
          in
       if uu____6946
       then
         let uu____6947 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____6947
       else ());
      (let uu____6949 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____6949 with
       | (vars,pat_term) ->
           let uu____6966 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____7019  ->
                     fun v1  ->
                       match uu____7019 with
                       | (env1,vars1) ->
                           let uu____7071 =
                             FStar_SMTEncoding_Env.gen_term_var env1 v1  in
                           (match uu____7071 with
                            | (xx,uu____7093,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, []))
              in
           (match uu____6966 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____7176 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____7177 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____7178 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____7186 = encode_const c env1  in
                      (match uu____7186 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____7200::uu____7201 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____7204 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon
                            env1.FStar_SMTEncoding_Env.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____7227 =
                          FStar_TypeChecker_Env.datacons_of_typ
                            env1.FStar_SMTEncoding_Env.tcenv tc_name
                           in
                        match uu____7227 with
                        | (uu____7234,uu____7235::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____7238 ->
                            FStar_SMTEncoding_Env.mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____7271  ->
                                  match uu____7271 with
                                  | (arg,uu____7279) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____7285 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____7285))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____7316) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____7347 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____7370 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____7414  ->
                                  match uu____7414 with
                                  | (arg,uu____7428) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____7434 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____7434))
                         in
                      FStar_All.pipe_right uu____7370 FStar_List.flatten
                   in
                let pat_term1 uu____7464 = encode_term pat_term env1  in
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
      let uu____7474 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____7512  ->
                fun uu____7513  ->
                  match (uu____7512, uu____7513) with
                  | ((tms,decls),(t,uu____7549)) ->
                      let uu____7570 = encode_term t env  in
                      (match uu____7570 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____7474 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____7629 = FStar_Syntax_Util.list_elements e  in
        match uu____7629 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____7656 =
          let uu____7671 = FStar_Syntax_Util.unmeta p  in
          FStar_All.pipe_right uu____7671 FStar_Syntax_Util.head_and_args  in
        match uu____7656 with
        | (head1,args) ->
            let uu____7714 =
              let uu____7727 =
                let uu____7728 = FStar_Syntax_Util.un_uinst head1  in
                uu____7728.FStar_Syntax_Syntax.n  in
              (uu____7727, args)  in
            (match uu____7714 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____7746,uu____7747)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____7785 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or t1 =
          let uu____7833 =
            let uu____7848 = FStar_Syntax_Util.unmeta t1  in
            FStar_All.pipe_right uu____7848 FStar_Syntax_Util.head_and_args
             in
          match uu____7833 with
          | (head1,args) ->
              let uu____7889 =
                let uu____7902 =
                  let uu____7903 = FStar_Syntax_Util.un_uinst head1  in
                  uu____7903.FStar_Syntax_Syntax.n  in
                (uu____7902, args)  in
              (match uu____7889 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____7920)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____7947 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____7973 = smt_pat_or t1  in
            (match uu____7973 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____7993 = list_elements1 e  in
                 FStar_All.pipe_right uu____7993
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____8019 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____8019
                           (FStar_List.map one_pat)))
             | uu____8038 ->
                 let uu____8043 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____8043])
        | uu____8084 ->
            let uu____8087 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____8087]
         in
      let uu____8128 =
        let uu____8151 =
          let uu____8152 = FStar_Syntax_Subst.compress t  in
          uu____8152.FStar_Syntax_Syntax.n  in
        match uu____8151 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____8195 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____8195 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____8246;
                        FStar_Syntax_Syntax.effect_name = uu____8247;
                        FStar_Syntax_Syntax.result_typ = uu____8248;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____8250)::(post,uu____8252)::(pats,uu____8254)::[];
                        FStar_Syntax_Syntax.flags = uu____8255;_}
                      ->
                      let uu____8296 = lemma_pats pats  in
                      (binders1, pre, post, uu____8296)
                  | uu____8321 -> failwith "impos"))
        | uu____8344 -> failwith "Impos"  in
      match uu____8128 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___73_8404 = env  in
            {
              FStar_SMTEncoding_Env.bvar_bindings =
                (uu___73_8404.FStar_SMTEncoding_Env.bvar_bindings);
              FStar_SMTEncoding_Env.fvar_bindings =
                (uu___73_8404.FStar_SMTEncoding_Env.fvar_bindings);
              FStar_SMTEncoding_Env.depth =
                (uu___73_8404.FStar_SMTEncoding_Env.depth);
              FStar_SMTEncoding_Env.tcenv =
                (uu___73_8404.FStar_SMTEncoding_Env.tcenv);
              FStar_SMTEncoding_Env.warn =
                (uu___73_8404.FStar_SMTEncoding_Env.warn);
              FStar_SMTEncoding_Env.cache =
                (uu___73_8404.FStar_SMTEncoding_Env.cache);
              FStar_SMTEncoding_Env.nolabels =
                (uu___73_8404.FStar_SMTEncoding_Env.nolabels);
              FStar_SMTEncoding_Env.use_zfuel_name = true;
              FStar_SMTEncoding_Env.encode_non_total_function_typ =
                (uu___73_8404.FStar_SMTEncoding_Env.encode_non_total_function_typ);
              FStar_SMTEncoding_Env.current_module_name =
                (uu___73_8404.FStar_SMTEncoding_Env.current_module_name);
              FStar_SMTEncoding_Env.encoding_quantifier =
                (uu___73_8404.FStar_SMTEncoding_Env.encoding_quantifier)
            }  in
          let uu____8405 =
            encode_binders FStar_Pervasives_Native.None binders env1  in
          (match uu____8405 with
           | (vars,guards,env2,decls,uu____8430) ->
               let uu____8443 = encode_smt_patterns patterns env2  in
               (match uu____8443 with
                | (pats,decls') ->
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
                    let env3 =
                      let uu___74_8476 = env2  in
                      {
                        FStar_SMTEncoding_Env.bvar_bindings =
                          (uu___74_8476.FStar_SMTEncoding_Env.bvar_bindings);
                        FStar_SMTEncoding_Env.fvar_bindings =
                          (uu___74_8476.FStar_SMTEncoding_Env.fvar_bindings);
                        FStar_SMTEncoding_Env.depth =
                          (uu___74_8476.FStar_SMTEncoding_Env.depth);
                        FStar_SMTEncoding_Env.tcenv =
                          (uu___74_8476.FStar_SMTEncoding_Env.tcenv);
                        FStar_SMTEncoding_Env.warn =
                          (uu___74_8476.FStar_SMTEncoding_Env.warn);
                        FStar_SMTEncoding_Env.cache =
                          (uu___74_8476.FStar_SMTEncoding_Env.cache);
                        FStar_SMTEncoding_Env.nolabels = true;
                        FStar_SMTEncoding_Env.use_zfuel_name =
                          (uu___74_8476.FStar_SMTEncoding_Env.use_zfuel_name);
                        FStar_SMTEncoding_Env.encode_non_total_function_typ =
                          (uu___74_8476.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                        FStar_SMTEncoding_Env.current_module_name =
                          (uu___74_8476.FStar_SMTEncoding_Env.current_module_name);
                        FStar_SMTEncoding_Env.encoding_quantifier =
                          (uu___74_8476.FStar_SMTEncoding_Env.encoding_quantifier)
                      }  in
                    let uu____8477 =
                      let uu____8482 = FStar_Syntax_Util.unmeta pre  in
                      encode_formula uu____8482 env3  in
                    (match uu____8477 with
                     | (pre1,decls'') ->
                         let uu____8489 =
                           let uu____8494 = FStar_Syntax_Util.unmeta post1
                              in
                           encode_formula uu____8494 env3  in
                         (match uu____8489 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append decls'
                                     (FStar_List.append decls'' decls'''))
                                 in
                              let uu____8504 =
                                let uu____8505 =
                                  let uu____8516 =
                                    let uu____8517 =
                                      let uu____8522 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards)
                                         in
                                      (uu____8522, post2)  in
                                    FStar_SMTEncoding_Util.mkImp uu____8517
                                     in
                                  (pats, vars, uu____8516)  in
                                FStar_SMTEncoding_Term.mkForall
                                  t.FStar_Syntax_Syntax.pos uu____8505
                                 in
                              (uu____8504, decls1)))))

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
        let uu___75_8548 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___75_8548.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___75_8548.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___75_8548.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___75_8548.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___75_8548.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.cache =
            (uu___75_8548.FStar_SMTEncoding_Env.cache);
          FStar_SMTEncoding_Env.nolabels =
            (uu___75_8548.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___75_8548.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___75_8548.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___75_8548.FStar_SMTEncoding_Env.encoding_quantifier)
        }  in
      let encode_smt_pattern t =
        let uu____8561 = FStar_Syntax_Util.head_and_args t  in
        match uu____8561 with
        | (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____8620::(x,uu____8622)::(t1,uu____8624)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____8671 = encode_term x env1  in
                 (match uu____8671 with
                  | (x1,decls) ->
                      let uu____8684 = encode_term t1 env1  in
                      (match uu____8684 with
                       | (t2,decls') ->
                           let uu____8697 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                           (uu____8697, (FStar_List.append decls decls'))))
             | uu____8700 -> encode_term t env1)
         in
      FStar_List.fold_right
        (fun pats  ->
           fun uu____8737  ->
             match uu____8737 with
             | (pats_l1,decls) ->
                 let uu____8778 =
                   FStar_List.fold_right
                     (fun uu____8809  ->
                        fun uu____8810  ->
                          match (uu____8809, uu____8810) with
                          | ((p,uu____8844),(pats1,decls1)) ->
                              let uu____8867 = encode_smt_pattern p  in
                              (match uu____8867 with
                               | (t,d) ->
                                   let uu____8888 =
                                     FStar_SMTEncoding_Term.check_pattern_ok
                                       t
                                      in
                                   (match uu____8888 with
                                    | FStar_Pervasives_Native.None  ->
                                        ((t :: pats1),
                                          (FStar_List.append d decls1))
                                    | FStar_Pervasives_Native.Some
                                        illegal_subterm ->
                                        ((let uu____8905 =
                                            let uu____8910 =
                                              let uu____8911 =
                                                FStar_Syntax_Print.term_to_string
                                                  p
                                                 in
                                              let uu____8912 =
                                                FStar_SMTEncoding_Term.print_smt_term
                                                  illegal_subterm
                                                 in
                                              FStar_Util.format2
                                                "Pattern %s contains illegal sub-term (%s); dropping it"
                                                uu____8911 uu____8912
                                               in
                                            (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                                              uu____8910)
                                             in
                                          FStar_Errors.log_issue
                                            p.FStar_Syntax_Syntax.pos
                                            uu____8905);
                                         (pats1,
                                           (FStar_List.append d decls1))))))
                     pats ([], decls)
                    in
                 (match uu____8778 with
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
        let uu____8969 =
          FStar_All.pipe_left
            (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____8969
        then
          let uu____8970 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____8971 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____8970 uu____8971
        else ()  in
      let enc f r l =
        let uu____9010 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____9038 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____9038 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____9010 with
        | (decls,args) ->
            let uu____9067 =
              let uu___76_9068 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___76_9068.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___76_9068.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____9067, decls)
         in
      let const_op f r uu____9105 = let uu____9118 = f r  in (uu____9118, [])
         in
      let un_op f l =
        let uu____9141 = FStar_List.hd l  in FStar_All.pipe_left f uu____9141
         in
      let bin_op f uu___67_9161 =
        match uu___67_9161 with
        | t1::t2::[] -> f (t1, t2)
        | uu____9172 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____9212 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____9235  ->
                 match uu____9235 with
                 | (t,uu____9249) ->
                     let uu____9250 = encode_formula t env  in
                     (match uu____9250 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____9212 with
        | (decls,phis) ->
            let uu____9279 =
              let uu___77_9280 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___77_9280.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___77_9280.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____9279, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____9345  ->
               match uu____9345 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____9364) -> false
                    | uu____9365 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____9380 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____9380
        else
          (let uu____9394 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____9394 r rf)
         in
      let mk_imp1 r uu___68_9429 =
        match uu___68_9429 with
        | (lhs,uu____9435)::(rhs,uu____9437)::[] ->
            let uu____9464 = encode_formula rhs env  in
            (match uu____9464 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____9479) ->
                      (l1, decls1)
                  | uu____9484 ->
                      let uu____9485 = encode_formula lhs env  in
                      (match uu____9485 with
                       | (l2,decls2) ->
                           let uu____9496 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____9496, (FStar_List.append decls1 decls2)))))
        | uu____9499 -> failwith "impossible"  in
      let mk_ite r uu___69_9526 =
        match uu___69_9526 with
        | (guard,uu____9532)::(_then,uu____9534)::(_else,uu____9536)::[] ->
            let uu____9573 = encode_formula guard env  in
            (match uu____9573 with
             | (g,decls1) ->
                 let uu____9584 = encode_formula _then env  in
                 (match uu____9584 with
                  | (t,decls2) ->
                      let uu____9595 = encode_formula _else env  in
                      (match uu____9595 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____9609 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____9638 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l  in
        f uu____9638  in
      let connectives =
        let uu____9658 =
          let uu____9673 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____9673)  in
        let uu____9696 =
          let uu____9713 =
            let uu____9728 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____9728)  in
          let uu____9751 =
            let uu____9768 =
              let uu____9786 =
                let uu____9801 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____9801)  in
              let uu____9824 =
                let uu____9841 =
                  let uu____9859 =
                    let uu____9874 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____9874)  in
                  [uu____9859;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____9841  in
              uu____9786 :: uu____9824  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____9768  in
          uu____9713 :: uu____9751  in
        uu____9658 :: uu____9696  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____10241 = encode_formula phi' env  in
            (match uu____10241 with
             | (phi2,decls) ->
                 let uu____10252 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____10252, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____10253 ->
            let uu____10260 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____10260 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____10299 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____10299 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____10311;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____10313;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____10315;
                 FStar_Syntax_Syntax.lbpos = uu____10316;_}::[]),e2)
            ->
            let uu____10340 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____10340 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____10387::(x,uu____10389)::(t,uu____10391)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____10438 = encode_term x env  in
                 (match uu____10438 with
                  | (x1,decls) ->
                      let uu____10449 = encode_term t env  in
                      (match uu____10449 with
                       | (t1,decls') ->
                           let uu____10460 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____10460, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____10465)::(msg,uu____10467)::(phi2,uu____10469)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____10514 =
                   let uu____10519 =
                     let uu____10520 = FStar_Syntax_Subst.compress r  in
                     uu____10520.FStar_Syntax_Syntax.n  in
                   let uu____10523 =
                     let uu____10524 = FStar_Syntax_Subst.compress msg  in
                     uu____10524.FStar_Syntax_Syntax.n  in
                   (uu____10519, uu____10523)  in
                 (match uu____10514 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____10533))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____10539 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____10546)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____10571 when head_redex env head2 ->
                 let uu____10584 = whnf env phi1  in
                 encode_formula uu____10584 env
             | uu____10585 ->
                 let uu____10598 = encode_term phi1 env  in
                 (match uu____10598 with
                  | (tt,decls) ->
                      let uu____10609 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___78_10612 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___78_10612.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___78_10612.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      (uu____10609, decls)))
        | uu____10613 ->
            let uu____10614 = encode_term phi1 env  in
            (match uu____10614 with
             | (tt,decls) ->
                 let uu____10625 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___79_10628 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___79_10628.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___79_10628.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 (uu____10625, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____10672 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____10672 with
        | (vars,guards,env2,decls,uu____10711) ->
            let uu____10724 = encode_smt_patterns ps env2  in
            (match uu____10724 with
             | (pats,decls') ->
                 let uu____10767 = encode_formula body env2  in
                 (match uu____10767 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____10799;
                             FStar_SMTEncoding_Term.rng = uu____10800;_}::[])::[]
                            when
                            let uu____10815 =
                              FStar_Ident.text_of_lid
                                FStar_Parser_Const.guard_free
                               in
                            uu____10815 = gf -> []
                        | uu____10816 -> guards  in
                      let uu____10821 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____10821, body1,
                        (FStar_List.append decls
                           (FStar_List.append decls' decls'')))))
         in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi  in
       let uu____10832 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____10832 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____10841 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____10907  ->
                     match uu____10907 with
                     | (l,uu____10921) -> FStar_Ident.lid_equals op l))
              in
           (match uu____10841 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____10960,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____11006 = encode_q_body env vars pats body  in
             match uu____11006 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____11051 =
                     let uu____11062 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____11062)  in
                   FStar_SMTEncoding_Term.mkForall
                     phi1.FStar_Syntax_Syntax.pos uu____11051
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____11081 = encode_q_body env vars pats body  in
             match uu____11081 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____11125 =
                   let uu____11126 =
                     let uu____11137 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____11137)  in
                   FStar_SMTEncoding_Term.mkExists
                     phi1.FStar_Syntax_Syntax.pos uu____11126
                    in
                 (uu____11125, decls))))
