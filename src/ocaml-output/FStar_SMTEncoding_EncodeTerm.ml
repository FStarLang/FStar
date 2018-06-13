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
      | FStar_Syntax_Syntax.Tm_refine uu____189 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____196 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____197 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____210 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____227 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____229 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____229 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____247;
             FStar_Syntax_Syntax.vars = uu____248;_},uu____249)
          ->
          let uu____270 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____270 FStar_Option.isNone
      | uu____287 -> false
  
let (head_redex :
  FStar_SMTEncoding_Env.env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____298 =
        let uu____299 = FStar_Syntax_Util.un_uinst t  in
        uu____299.FStar_Syntax_Syntax.n  in
      match uu____298 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____302,uu____303,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___339_324  ->
                  match uu___339_324 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____325 -> false) rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____327 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____327 FStar_Option.isSome
      | uu____344 -> false
  
let (whnf :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____355 = head_normal env t  in
      if uu____355
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
  fun env  ->
    fun t  ->
      FStar_TypeChecker_Normalize.normalize
        [FStar_TypeChecker_Env.Beta;
        FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
        FStar_TypeChecker_Env.Eager_unfolding;
        FStar_TypeChecker_Env.EraseUniverses] env.FStar_SMTEncoding_Env.tcenv
        t
  
let (trivial_post : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____372 =
      let uu____373 = FStar_Syntax_Syntax.null_binder t  in [uu____373]  in
    let uu____386 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    FStar_Syntax_Util.abs uu____372 uu____386 FStar_Pervasives_Native.None
  
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
                    let uu____430 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____430
                | s ->
                    let uu____433 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____433) e)
  
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
          let uu____481 =
            let uu____486 =
              let uu____487 = FStar_Util.string_of_int arity  in
              let uu____488 = FStar_Util.string_of_int n_args  in
              FStar_Util.format3
                "Head symbol %s expects at least %s arguments; got only %s"
                head1 uu____487 uu____488
               in
            (FStar_Errors.Fatal_SMTEncodingArityMismatch, uu____486)  in
          FStar_Errors.raise_error uu____481 rng
  
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
              (let uu____527 = FStar_Util.first_N arity args  in
               match uu____527 with
               | (args1,rest) ->
                   let head2 = FStar_SMTEncoding_Util.mkApp' (head1, args1)
                      in
                   mk_Apply_args head2 rest)
            else
              (let uu____550 = FStar_SMTEncoding_Term.op_to_string head1  in
               raise_arity_mismatch uu____550 arity n_args rng)
  
let (is_app : FStar_SMTEncoding_Term.op -> Prims.bool) =
  fun uu___340_559  ->
    match uu___340_559 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____560 -> false
  
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
                       FStar_SMTEncoding_Term.freevars = uu____606;
                       FStar_SMTEncoding_Term.rng = uu____607;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____630) ->
              let uu____639 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____650 -> false) args (FStar_List.rev xs))
                 in
              if uu____639
              then FStar_SMTEncoding_Env.tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____654,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t  in
              let uu____658 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____664 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars
                           in
                        Prims.op_Negation uu____664))
                 in
              if uu____658
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____668 -> FStar_Pervasives_Native.None  in
        check_partial_applications body (FStar_List.rev vars)
  
let check_pattern_vars :
  'Auu____685 'Auu____686 .
    FStar_SMTEncoding_Env.env_t ->
      (FStar_Syntax_Syntax.bv,'Auu____685) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____686) FStar_Pervasives_Native.tuple2
          Prims.list -> unit
  =
  fun env  ->
    fun vars  ->
      fun pats  ->
        let pats1 =
          FStar_All.pipe_right pats
            (FStar_List.map
               (fun uu____744  ->
                  match uu____744 with
                  | (x,uu____750) ->
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.AllowUnboundUniverses;
                        FStar_TypeChecker_Env.EraseUniverses]
                        env.FStar_SMTEncoding_Env.tcenv x))
           in
        match pats1 with
        | [] -> ()
        | hd1::tl1 ->
            let pat_vars =
              let uu____758 = FStar_Syntax_Free.names hd1  in
              FStar_List.fold_left
                (fun out  ->
                   fun x  ->
                     let uu____770 = FStar_Syntax_Free.names x  in
                     FStar_Util.set_union out uu____770) uu____758 tl1
               in
            let uu____773 =
              FStar_All.pipe_right vars
                (FStar_Util.find_opt
                   (fun uu____800  ->
                      match uu____800 with
                      | (b,uu____806) ->
                          let uu____807 = FStar_Util.set_mem b pat_vars  in
                          Prims.op_Negation uu____807))
               in
            (match uu____773 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some (x,uu____813) ->
                 let pos =
                   FStar_List.fold_left
                     (fun out  ->
                        fun t  ->
                          FStar_Range.union_ranges out
                            t.FStar_Syntax_Syntax.pos)
                     hd1.FStar_Syntax_Syntax.pos tl1
                    in
                 let uu____827 =
                   let uu____832 =
                     let uu____833 = FStar_Syntax_Print.bv_to_string x  in
                     FStar_Util.format1
                       "SMT pattern misses at least one bound variable: %s"
                       uu____833
                      in
                   (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                     uu____832)
                    in
                 FStar_Errors.log_issue pos uu____827)
  
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
        | FStar_Syntax_Syntax.Tm_arrow uu____1108 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____1121 ->
            let uu____1128 = FStar_Syntax_Util.unrefine t1  in
            aux true uu____1128
        | uu____1129 ->
            if norm1
            then let uu____1130 = whnf env t1  in aux false uu____1130
            else
              (let uu____1132 =
                 let uu____1133 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let uu____1134 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____1133 uu____1134
                  in
               failwith uu____1132)
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
    | FStar_Syntax_Syntax.Tm_refine (bv,uu____1168) ->
        curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort
    | uu____1173 ->
        let uu____1174 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____1174)
  
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
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun c  ->
    fun env  ->
      match c with
      | FStar_Const.Const_unit  -> (FStar_SMTEncoding_Term.mk_Term_unit, [])
      | FStar_Const.Const_bool (true ) ->
          let uu____1709 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue  in
          (uu____1709, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____1710 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse  in
          (uu____1710, [])
      | FStar_Const.Const_char c1 ->
          let uu____1713 =
            let uu____1714 =
              let uu____1721 =
                let uu____1724 =
                  let uu____1725 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1)
                     in
                  FStar_SMTEncoding_Term.boxInt uu____1725  in
                [uu____1724]  in
              ("FStar.Char.__char_of_int", uu____1721)  in
            FStar_SMTEncoding_Util.mkApp uu____1714  in
          (uu____1713, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____1739 =
            let uu____1740 = FStar_SMTEncoding_Util.mkInteger i  in
            FStar_SMTEncoding_Term.boxInt uu____1740  in
          (uu____1739, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.FStar_SMTEncoding_Env.tcenv).FStar_TypeChecker_Env.dsenv
              repr sw FStar_Range.dummyRange
             in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____1759) ->
          let uu____1760 =
            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.string_const s
             in
          (uu____1760, [])
      | FStar_Const.Const_range uu____1761 ->
          let uu____1762 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          (uu____1762, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | c1 ->
          let uu____1764 =
            let uu____1765 = FStar_Syntax_Print.const_to_string c1  in
            FStar_Util.format1 "Unhandled constant: %s" uu____1765  in
          failwith uu____1764

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
        (let uu____1792 =
           FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
             FStar_Options.Low
            in
         if uu____1792
         then
           let uu____1793 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____1793
         else ());
        (let uu____1795 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____1885  ->
                   fun b  ->
                     match uu____1885 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____1964 =
                           let x =
                             FStar_SMTEncoding_Env.unmangle
                               (FStar_Pervasives_Native.fst b)
                              in
                           let uu____1982 =
                             FStar_SMTEncoding_Env.gen_term_var env1 x  in
                           match uu____1982 with
                           | (xxsym,xx,env') ->
                               let uu____2008 =
                                 let uu____2013 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____2013 env1 xx
                                  in
                               (match uu____2008 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x))
                            in
                         (match uu____1964 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____1795 with
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
          let uu____2174 = encode_term t env  in
          match uu____2174 with
          | (t1,decls) ->
              let uu____2185 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____2185, decls)

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
          let uu____2196 = encode_term t env  in
          match uu____2196 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____2211 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____2211, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____2213 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____2213, decls))

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
        let uu____2219 = encode_args args_e env  in
        match uu____2219 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____2238 -> failwith "Impossible"  in
            let unary arg_tms1 =
              let uu____2249 = FStar_List.hd arg_tms1  in
              FStar_SMTEncoding_Term.unboxInt uu____2249  in
            let binary arg_tms1 =
              let uu____2264 =
                let uu____2265 = FStar_List.hd arg_tms1  in
                FStar_SMTEncoding_Term.unboxInt uu____2265  in
              let uu____2266 =
                let uu____2267 =
                  let uu____2268 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____2268  in
                FStar_SMTEncoding_Term.unboxInt uu____2267  in
              (uu____2264, uu____2266)  in
            let mk_default uu____2276 =
              let uu____2277 =
                FStar_SMTEncoding_Env.lookup_free_var_sym env
                  head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____2277 with
              | (fname,fuel_args,arity) ->
                  let args = FStar_List.append fuel_args arg_tms  in
                  maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity
                    args
               in
            let mk_l op mk_args ts =
              let uu____2339 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____2339
              then
                let uu____2340 =
                  let uu____2341 = mk_args ts  in op uu____2341  in
                FStar_All.pipe_right uu____2340 FStar_SMTEncoding_Term.boxInt
              else mk_default ()  in
            let mk_nl nm op ts =
              let uu____2376 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____2376
              then
                let uu____2377 = binary ts  in
                match uu____2377 with
                | (t1,t2) ->
                    let uu____2384 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____2384
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____2388 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____2388
                 then
                   let uu____2389 =
                     let uu____2390 = binary ts  in op uu____2390  in
                   FStar_All.pipe_right uu____2389
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
            let uu____2551 =
              let uu____2561 =
                FStar_List.tryFind
                  (fun uu____2585  ->
                     match uu____2585 with
                     | (l,uu____2595) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____2561 FStar_Util.must  in
            (match uu____2551 with
             | (uu____2639,op) ->
                 let uu____2651 = op arg_tms  in (uu____2651, decls))

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
        let uu____2659 = FStar_List.hd args_e  in
        match uu____2659 with
        | (tm_sz,uu____2667) ->
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let uu____2677 =
                FStar_Util.smap_try_find env.FStar_SMTEncoding_Env.cache
                  sz_key
                 in
              match uu____2677 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None  ->
                  let t_decls1 = FStar_SMTEncoding_Term.mkBvConstructor sz
                     in
                  ((let uu____2685 =
                      FStar_SMTEncoding_Env.mk_cache_entry env "" [] []  in
                    FStar_Util.smap_add env.FStar_SMTEncoding_Env.cache
                      sz_key uu____2685);
                   t_decls1)
               in
            let uu____2686 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____2708::(sz_arg,uu____2710)::uu____2711::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____2760 =
                    let uu____2761 = FStar_List.tail args_e  in
                    FStar_List.tail uu____2761  in
                  let uu____2764 =
                    let uu____2767 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____2767  in
                  (uu____2760, uu____2764)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____2771::(sz_arg,uu____2773)::uu____2774::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____2823 =
                    let uu____2824 = FStar_Syntax_Print.term_to_string sz_arg
                       in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____2824
                     in
                  failwith uu____2823
              | uu____2831 ->
                  let uu____2844 = FStar_List.tail args_e  in
                  (uu____2844, FStar_Pervasives_Native.None)
               in
            (match uu____2686 with
             | (arg_tms,ext_sz) ->
                 let uu____2859 = encode_args arg_tms env  in
                 (match uu____2859 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____2880 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____2891 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____2891  in
                      let unary_arith arg_tms2 =
                        let uu____2902 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____2902  in
                      let binary arg_tms2 =
                        let uu____2917 =
                          let uu____2918 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____2918
                           in
                        let uu____2919 =
                          let uu____2920 =
                            let uu____2921 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____2921  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____2920
                           in
                        (uu____2917, uu____2919)  in
                      let binary_arith arg_tms2 =
                        let uu____2938 =
                          let uu____2939 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____2939
                           in
                        let uu____2940 =
                          let uu____2941 =
                            let uu____2942 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____2942  in
                          FStar_SMTEncoding_Term.unboxInt uu____2941  in
                        (uu____2938, uu____2940)  in
                      let mk_bv op mk_args resBox ts =
                        let uu____3000 =
                          let uu____3001 = mk_args ts  in op uu____3001  in
                        FStar_All.pipe_right uu____3000 resBox  in
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
                        let uu____3133 =
                          let uu____3138 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____3138  in
                        let uu____3140 =
                          let uu____3145 =
                            let uu____3146 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____3146  in
                          FStar_SMTEncoding_Term.boxBitVec uu____3145  in
                        mk_bv uu____3133 unary uu____3140 arg_tms2  in
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
                      let uu____3379 =
                        let uu____3389 =
                          FStar_List.tryFind
                            (fun uu____3413  ->
                               match uu____3413 with
                               | (l,uu____3423) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____3389 FStar_Util.must  in
                      (match uu____3379 with
                       | (uu____3469,op) ->
                           let uu____3481 = op arg_tms1  in
                           (uu____3481, (FStar_List.append sz_decls decls)))))

and (encode_deeply_embedded_quantifier :
  FStar_Syntax_Syntax.term ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let env1 =
        let uu___344_3491 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___344_3491.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___344_3491.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___344_3491.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___344_3491.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___344_3491.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.cache =
            (uu___344_3491.FStar_SMTEncoding_Env.cache);
          FStar_SMTEncoding_Env.nolabels =
            (uu___344_3491.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name =
            (uu___344_3491.FStar_SMTEncoding_Env.use_zfuel_name);
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___344_3491.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___344_3491.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier = true
        }  in
      let uu____3492 = encode_term t env1  in
      match uu____3492 with
      | (tm,decls) ->
          let vars = FStar_SMTEncoding_Term.free_variables tm  in
          let valid_tm = FStar_SMTEncoding_Term.mk_Valid tm  in
          let key =
            FStar_SMTEncoding_Term.mkForall t.FStar_Syntax_Syntax.pos
              ([], vars, valid_tm)
             in
          let tkey_hash = FStar_SMTEncoding_Term.hash_of_term key  in
          let uu____3513 =
            FStar_Util.smap_try_find env1.FStar_SMTEncoding_Env.cache
              tkey_hash
             in
          (match uu____3513 with
           | FStar_Pervasives_Native.Some uu____3520 -> (tm, decls)
           | uu____3521 ->
               (match tm.FStar_SMTEncoding_Term.tm with
                | FStar_SMTEncoding_Term.App
                    (uu____3528,{
                                  FStar_SMTEncoding_Term.tm =
                                    FStar_SMTEncoding_Term.FreeV uu____3529;
                                  FStar_SMTEncoding_Term.freevars =
                                    uu____3530;
                                  FStar_SMTEncoding_Term.rng = uu____3531;_}::
                     {
                       FStar_SMTEncoding_Term.tm =
                         FStar_SMTEncoding_Term.FreeV uu____3532;
                       FStar_SMTEncoding_Term.freevars = uu____3533;
                       FStar_SMTEncoding_Term.rng = uu____3534;_}::[])
                    ->
                    (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                       (FStar_Errors.Warning_QuantifierWithoutPattern,
                         "Not encoding deeply embedded, unguarded quantifier to SMT");
                     (tm, decls))
                | uu____3562 ->
                    let uu____3563 = encode_formula t env1  in
                    (match uu____3563 with
                     | (phi,decls') ->
                         let interp =
                           match vars with
                           | [] ->
                               let uu____3579 =
                                 let uu____3584 =
                                   FStar_SMTEncoding_Term.mk_Valid tm  in
                                 (uu____3584, phi)  in
                               FStar_SMTEncoding_Util.mkIff uu____3579
                           | uu____3585 ->
                               let uu____3586 =
                                 let uu____3597 =
                                   let uu____3598 =
                                     let uu____3603 =
                                       FStar_SMTEncoding_Term.mk_Valid tm  in
                                     (uu____3603, phi)  in
                                   FStar_SMTEncoding_Util.mkIff uu____3598
                                    in
                                 ([[valid_tm]], vars, uu____3597)  in
                               FStar_SMTEncoding_Term.mkForall
                                 t.FStar_Syntax_Syntax.pos uu____3586
                            in
                         let ax =
                           let uu____3613 =
                             let uu____3620 =
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 "l_quant_interp"
                                in
                             (interp,
                               (FStar_Pervasives_Native.Some
                                  "Interpretation of deeply embedded quantifier"),
                               uu____3620)
                              in
                           FStar_SMTEncoding_Util.mkAssume uu____3613  in
                         ((let uu____3622 =
                             FStar_SMTEncoding_Env.mk_cache_entry env1 "" []
                               [ax]
                              in
                           FStar_Util.smap_add
                             env1.FStar_SMTEncoding_Env.cache tkey_hash
                             uu____3622);
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
      (let uu____3631 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____3631
       then
         let uu____3632 = FStar_Syntax_Print.tag_of_term t  in
         let uu____3633 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____3634 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____3632 uu____3633
           uu____3634
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____3640 ->
           let uu____3663 =
             let uu____3664 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____3665 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____3666 = FStar_Syntax_Print.term_to_string t0  in
             let uu____3667 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____3664
               uu____3665 uu____3666 uu____3667
              in
           failwith uu____3663
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____3672 =
             let uu____3673 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____3674 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____3675 = FStar_Syntax_Print.term_to_string t0  in
             let uu____3676 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____3673
               uu____3674 uu____3675 uu____3676
              in
           failwith uu____3672
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____3682 = FStar_Syntax_Util.unfold_lazy i  in
           encode_term uu____3682 env
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____3684 =
             let uu____3685 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____3685
              in
           failwith uu____3684
       | FStar_Syntax_Syntax.Tm_ascribed (t1,(k,uu____3692),uu____3693) ->
           let uu____3742 =
             match k with
             | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
             | uu____3750 -> false  in
           if uu____3742
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t1 env
       | FStar_Syntax_Syntax.Tm_quoted (qt,uu____3765) ->
           let tv =
             let uu____3771 = FStar_Reflection_Basic.inspect_ln qt  in
             FStar_Syntax_Embeddings.embed
               FStar_Reflection_Embeddings.e_term_view
               t.FStar_Syntax_Syntax.pos uu____3771
              in
           let t1 =
             let uu____3775 =
               let uu____3784 = FStar_Syntax_Syntax.as_arg tv  in
               [uu____3784]  in
             FStar_Syntax_Util.mk_app
               (FStar_Reflection_Data.refl_constant_term
                  FStar_Reflection_Data.fstar_refl_pack_ln) uu____3775
              in
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_pattern uu____3804) ->
           encode_term t1
             (let uu___345_3820 = env  in
              {
                FStar_SMTEncoding_Env.bvar_bindings =
                  (uu___345_3820.FStar_SMTEncoding_Env.bvar_bindings);
                FStar_SMTEncoding_Env.fvar_bindings =
                  (uu___345_3820.FStar_SMTEncoding_Env.fvar_bindings);
                FStar_SMTEncoding_Env.depth =
                  (uu___345_3820.FStar_SMTEncoding_Env.depth);
                FStar_SMTEncoding_Env.tcenv =
                  (uu___345_3820.FStar_SMTEncoding_Env.tcenv);
                FStar_SMTEncoding_Env.warn =
                  (uu___345_3820.FStar_SMTEncoding_Env.warn);
                FStar_SMTEncoding_Env.cache =
                  (uu___345_3820.FStar_SMTEncoding_Env.cache);
                FStar_SMTEncoding_Env.nolabels =
                  (uu___345_3820.FStar_SMTEncoding_Env.nolabels);
                FStar_SMTEncoding_Env.use_zfuel_name =
                  (uu___345_3820.FStar_SMTEncoding_Env.use_zfuel_name);
                FStar_SMTEncoding_Env.encode_non_total_function_typ =
                  (uu___345_3820.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                FStar_SMTEncoding_Env.current_module_name =
                  (uu___345_3820.FStar_SMTEncoding_Env.current_module_name);
                FStar_SMTEncoding_Env.encoding_quantifier = false
              })
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____3822) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = FStar_SMTEncoding_Env.lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____3830 = head_redex env t  in
           if uu____3830
           then let uu____3835 = whnf env t  in encode_term uu____3835 env
           else
             (let uu____3837 =
                FStar_SMTEncoding_Env.lookup_free_var_name env
                  v1.FStar_Syntax_Syntax.fv_name
                 in
              match uu____3837 with
              | (uu____3846,arity) ->
                  let tok =
                    FStar_SMTEncoding_Env.lookup_free_var env
                      v1.FStar_Syntax_Syntax.fv_name
                     in
                  let aux_decls =
                    if arity > (Prims.parse_int "0")
                    then
                      match tok.FStar_SMTEncoding_Term.tm with
                      | FStar_SMTEncoding_Term.FreeV uu____3850 ->
                          let uu____3855 =
                            let uu____3856 =
                              let uu____3863 =
                                FStar_SMTEncoding_Term.kick_partial_app tok
                                 in
                              let uu____3864 =
                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                  "@kick_partial_app"
                                 in
                              (uu____3863,
                                (FStar_Pervasives_Native.Some
                                   "kick_partial_app"), uu____3864)
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____3856  in
                          [uu____3855]
                      | FStar_SMTEncoding_Term.App (uu____3865,[]) ->
                          let uu____3868 =
                            let uu____3869 =
                              let uu____3876 =
                                FStar_SMTEncoding_Term.kick_partial_app tok
                                 in
                              let uu____3877 =
                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                  "@kick_partial_app"
                                 in
                              (uu____3876,
                                (FStar_Pervasives_Native.Some
                                   "kick_partial_app"), uu____3877)
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____3869  in
                          [uu____3868]
                      | uu____3878 -> []
                    else []  in
                  (tok, aux_decls))
       | FStar_Syntax_Syntax.Tm_type uu____3880 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3882) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.FStar_SMTEncoding_Env.current_module_name
              in
           let uu____3907 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____3907 with
            | (binders1,res) ->
                let uu____3918 =
                  (env.FStar_SMTEncoding_Env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____3918
                then
                  let uu____3923 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____3923 with
                   | (vars,guards,env',decls,uu____3948) ->
                       let fsym =
                         let uu____3966 =
                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                             "f"
                            in
                         (uu____3966, FStar_SMTEncoding_Term.Term_sort)  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____3969 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___346_3978 =
                              env.FStar_SMTEncoding_Env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___346_3978.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___346_3978.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___346_3978.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___346_3978.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___346_3978.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___346_3978.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___346_3978.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___346_3978.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___346_3978.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___346_3978.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___346_3978.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___346_3978.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___346_3978.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___346_3978.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___346_3978.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___346_3978.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___346_3978.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___346_3978.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___346_3978.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___346_3978.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___346_3978.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___346_3978.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___346_3978.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___346_3978.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___346_3978.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___346_3978.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___346_3978.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___346_3978.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___346_3978.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___346_3978.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___346_3978.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___346_3978.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___346_3978.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___346_3978.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___346_3978.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___346_3978.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___346_3978.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___346_3978.FStar_TypeChecker_Env.dep_graph);
                              FStar_TypeChecker_Env.nbe =
                                (uu___346_3978.FStar_TypeChecker_Env.nbe)
                            }) res
                          in
                       (match uu____3969 with
                        | (pre_opt,res_t) ->
                            let uu____3989 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____3989 with
                             | (res_pred,decls') ->
                                 let uu____4000 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____4013 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____4013, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____4017 =
                                         encode_formula pre env'  in
                                       (match uu____4017 with
                                        | (guard,decls0) ->
                                            let uu____4030 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____4030, decls0))
                                    in
                                 (match uu____4000 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____4044 =
                                          let uu____4055 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____4055)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t.FStar_Syntax_Syntax.pos
                                          uu____4044
                                         in
                                      let cvars =
                                        let uu____4071 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____4071
                                          (FStar_List.filter
                                             (fun uu____4097  ->
                                                match uu____4097 with
                                                | (x,uu____4103) ->
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
                                      let uu____4116 =
                                        FStar_Util.smap_try_find
                                          env.FStar_SMTEncoding_Env.cache
                                          tkey_hash
                                         in
                                      (match uu____4116 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____4124 =
                                             let uu____4125 =
                                               let uu____4132 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV)
                                                  in
                                               ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                                 uu____4132)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4125
                                              in
                                           (uu____4124,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (FStar_SMTEncoding_Env.use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____4150 =
                                               let uu____4151 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____4151
                                                in
                                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                               uu____4150
                                              in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars
                                              in
                                           let caption =
                                             let uu____4160 =
                                               FStar_Options.log_queries ()
                                                in
                                             if uu____4160
                                             then
                                               let uu____4161 =
                                                 let uu____4162 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env.FStar_SMTEncoding_Env.tcenv
                                                     t0
                                                    in
                                                 FStar_Util.replace_char
                                                   uu____4162 10 32
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____4161
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
                                             let uu____4170 =
                                               let uu____4177 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars
                                                  in
                                               (tsym, uu____4177)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4170
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
                                             let uu____4189 =
                                               let uu____4196 =
                                                 FStar_SMTEncoding_Term.mkForall
                                                   t0.FStar_Syntax_Syntax.pos
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind)
                                                  in
                                               (uu____4196,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name)
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4189
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
                                             let uu____4209 =
                                               let uu____4216 =
                                                 let uu____4217 =
                                                   let uu____4228 =
                                                     let uu____4229 =
                                                       let uu____4234 =
                                                         let uu____4235 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f
                                                            in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____4235
                                                          in
                                                       (f_has_t, uu____4234)
                                                        in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____4229
                                                      in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____4228)
                                                    in
                                                 let uu____4248 =
                                                   mkForall_fuel
                                                     t0.FStar_Syntax_Syntax.pos
                                                    in
                                                 uu____4248 uu____4217  in
                                               (uu____4216,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4209
                                              in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym
                                                in
                                             let uu____4265 =
                                               let uu____4272 =
                                                 let uu____4273 =
                                                   let uu____4284 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp)
                                                      in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____4284)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   t0.FStar_Syntax_Syntax.pos
                                                   uu____4273
                                                  in
                                               (uu____4272,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4265
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
                                           ((let uu____4301 =
                                               FStar_SMTEncoding_Env.mk_cache_entry
                                                 env tsym cvar_sorts t_decls1
                                                in
                                             FStar_Util.smap_add
                                               env.FStar_SMTEncoding_Env.cache
                                               tkey_hash uu____4301);
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
                     let uu____4312 =
                       let uu____4319 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____4319,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____4312  in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)  in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym  in
                     let uu____4329 =
                       let uu____4336 =
                         let uu____4337 =
                           let uu____4348 =
                             let uu____4349 =
                               let uu____4354 =
                                 let uu____4355 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____4355
                                  in
                               (f_has_t, uu____4354)  in
                             FStar_SMTEncoding_Util.mkImp uu____4349  in
                           ([[f_has_t]], [fsym], uu____4348)  in
                         let uu____4372 =
                           mkForall_fuel t0.FStar_Syntax_Syntax.pos  in
                         uu____4372 uu____4337  in
                       (uu____4336, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____4329  in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____4387 ->
           let uu____4394 =
             let uu____4399 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Env.Weak;
                 FStar_TypeChecker_Env.HNF;
                 FStar_TypeChecker_Env.EraseUniverses]
                 env.FStar_SMTEncoding_Env.tcenv t0
                in
             match uu____4399 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____4406;
                 FStar_Syntax_Syntax.vars = uu____4407;_} ->
                 let uu____4414 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____4414 with
                  | (b,f1) ->
                      let uu____4433 =
                        let uu____4434 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____4434  in
                      (uu____4433, f1))
             | uu____4443 -> failwith "impossible"  in
           (match uu____4394 with
            | (x,f) ->
                let uu____4454 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____4454 with
                 | (base_t,decls) ->
                     let uu____4465 =
                       FStar_SMTEncoding_Env.gen_term_var env x  in
                     (match uu____4465 with
                      | (x1,xtm,env') ->
                          let uu____4479 = encode_formula f env'  in
                          (match uu____4479 with
                           | (refinement,decls') ->
                               let uu____4490 =
                                 FStar_SMTEncoding_Env.fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____4490 with
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
                                      let uu____4510 =
                                        let uu____4517 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____4524 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____4517
                                          uu____4524
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____4510
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____4565  ->
                                              match uu____4565 with
                                              | (y,uu____4571) ->
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
                                    let uu____4598 =
                                      FStar_Util.smap_try_find
                                        env.FStar_SMTEncoding_Env.cache
                                        tkey_hash
                                       in
                                    (match uu____4598 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____4606 =
                                           let uu____4607 =
                                             let uu____4614 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV)
                                                in
                                             ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                               uu____4614)
                                              in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____4607
                                            in
                                         (uu____4606,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (FStar_SMTEncoding_Env.use_cache_entry
                                                    cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.FStar_SMTEncoding_Env.current_module_name
                                            in
                                         let tsym =
                                           let uu____4633 =
                                             let uu____4634 =
                                               let uu____4635 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____4635
                                                in
                                             Prims.strcat module_name
                                               uu____4634
                                              in
                                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                             uu____4633
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
                                           let uu____4647 =
                                             let uu____4654 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1
                                                in
                                             (tsym, uu____4654)  in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____4647
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
                                           let uu____4669 =
                                             let uu____4676 =
                                               let uu____4677 =
                                                 let uu____4688 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base)
                                                    in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____4688)
                                                  in
                                               FStar_SMTEncoding_Term.mkForall
                                                 t0.FStar_Syntax_Syntax.pos
                                                 uu____4677
                                                in
                                             (uu____4676,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4669
                                            in
                                         let t_kinding =
                                           let uu____4698 =
                                             let uu____4705 =
                                               FStar_SMTEncoding_Term.mkForall
                                                 t0.FStar_Syntax_Syntax.pos
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind)
                                                in
                                             (uu____4705,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4698
                                            in
                                         let t_interp =
                                           let uu____4715 =
                                             let uu____4722 =
                                               let uu____4723 =
                                                 let uu____4734 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding)
                                                    in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____4734)
                                                  in
                                               FStar_SMTEncoding_Term.mkForall
                                                 t0.FStar_Syntax_Syntax.pos
                                                 uu____4723
                                                in
                                             (uu____4722,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement_interpretation"),
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4715
                                            in
                                         let t_decls1 =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1])
                                            in
                                         ((let uu____4755 =
                                             FStar_SMTEncoding_Env.mk_cache_entry
                                               env tsym cvar_sorts t_decls1
                                              in
                                           FStar_Util.smap_add
                                             env.FStar_SMTEncoding_Env.cache
                                             tkey_hash uu____4755);
                                          (t1, t_decls1))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,uu____4757) ->
           let ttm =
             let uu____4775 =
               FStar_Syntax_Unionfind.uvar_id
                 uv.FStar_Syntax_Syntax.ctx_uvar_head
                in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____4775  in
           let uu____4776 =
             encode_term_pred FStar_Pervasives_Native.None
               uv.FStar_Syntax_Syntax.ctx_uvar_typ env ttm
              in
           (match uu____4776 with
            | (t_has_k,decls) ->
                let d =
                  let uu____4788 =
                    let uu____4795 =
                      let uu____4796 =
                        let uu____4797 =
                          let uu____4798 =
                            FStar_Syntax_Unionfind.uvar_id
                              uv.FStar_Syntax_Syntax.ctx_uvar_head
                             in
                          FStar_Util.string_of_int uu____4798  in
                        FStar_Util.format1 "uvar_typing_%s" uu____4797  in
                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                        uu____4796
                       in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____4795)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____4788  in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____4799 ->
           let uu____4814 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____4814 with
            | (head1,args_e) ->
                let uu____4855 =
                  let uu____4868 =
                    let uu____4869 = FStar_Syntax_Subst.compress head1  in
                    uu____4869.FStar_Syntax_Syntax.n  in
                  (uu____4868, args_e)  in
                (match uu____4855 with
                 | uu____4884 when head_redex env head1 ->
                     let uu____4897 = whnf env t  in
                     encode_term uu____4897 env
                 | uu____4898 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____4917 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4931) when
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
                       FStar_Syntax_Syntax.pos = uu____4949;
                       FStar_Syntax_Syntax.vars = uu____4950;_},uu____4951),uu____4952)
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
                       FStar_Syntax_Syntax.pos = uu____4974;
                       FStar_Syntax_Syntax.vars = uu____4975;_},uu____4976),
                    (v0,uu____4978)::(v1,uu____4980)::(v2,uu____4982)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____5031 = encode_term v0 env  in
                     (match uu____5031 with
                      | (v01,decls0) ->
                          let uu____5042 = encode_term v1 env  in
                          (match uu____5042 with
                           | (v11,decls1) ->
                               let uu____5053 = encode_term v2 env  in
                               (match uu____5053 with
                                | (v21,decls2) ->
                                    let uu____5064 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____5064,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(v0,uu____5067)::(v1,uu____5069)::(v2,uu____5071)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____5116 = encode_term v0 env  in
                     (match uu____5116 with
                      | (v01,decls0) ->
                          let uu____5127 = encode_term v1 env  in
                          (match uu____5127 with
                           | (v11,decls1) ->
                               let uu____5138 = encode_term v2 env  in
                               (match uu____5138 with
                                | (v21,decls2) ->
                                    let uu____5149 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____5149,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____5151)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____5177)::(rng,uu____5179)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____5214) ->
                     let e0 =
                       let uu____5232 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg
                         env.FStar_SMTEncoding_Env.tcenv head1 uu____5232
                        in
                     ((let uu____5240 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug
                              env.FStar_SMTEncoding_Env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____5240
                       then
                         let uu____5241 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____5241
                       else ());
                      (let e =
                         let uu____5246 =
                           let uu____5251 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____5252 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____5251
                             uu____5252
                            in
                         uu____5246 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____5261),(arg,uu____5263)::[]) -> encode_term arg env
                 | uu____5288 ->
                     let uu____5301 = encode_args args_e env  in
                     (match uu____5301 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____5358 = encode_term head1 env  in
                            match uu____5358 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____5422 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____5422 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____5500  ->
                                                 fun uu____5501  ->
                                                   match (uu____5500,
                                                           uu____5501)
                                                   with
                                                   | ((bv,uu____5523),
                                                      (a,uu____5525)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____5543 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____5543
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____5544 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm
                                             in
                                          (match uu____5544 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type
                                                  in
                                               let e_typing =
                                                 let uu____5559 =
                                                   let uu____5566 =
                                                     FStar_SMTEncoding_Term.mkForall
                                                       t0.FStar_Syntax_Syntax.pos
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____5575 =
                                                     let uu____5576 =
                                                       let uu____5577 =
                                                         let uu____5578 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm
                                                            in
                                                         FStar_Util.digest_of_string
                                                           uu____5578
                                                          in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____5577
                                                        in
                                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                       uu____5576
                                                      in
                                                   (uu____5566,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____5575)
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____5559
                                                  in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing])))))))
                             in
                          let encode_full_app fv =
                            let uu____5595 =
                              FStar_SMTEncoding_Env.lookup_free_var_sym env
                                fv
                               in
                            match uu____5595 with
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
                                   FStar_Syntax_Syntax.pos = uu____5623;
                                   FStar_Syntax_Syntax.vars = uu____5624;_},uu____5625)
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
                                   FStar_Syntax_Syntax.pos = uu____5632;
                                   FStar_Syntax_Syntax.vars = uu____5633;_},uu____5634)
                                ->
                                let uu____5639 =
                                  let uu____5640 =
                                    let uu____5645 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____5645
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____5640
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____5639
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____5675 =
                                  let uu____5676 =
                                    let uu____5681 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____5681
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____5676
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____5675
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____5710,(FStar_Util.Inl t1,uu____5712),uu____5713)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____5760,(FStar_Util.Inr c,uu____5762),uu____5763)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____5810 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____5829 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Env.Weak;
                                     FStar_TypeChecker_Env.HNF;
                                     FStar_TypeChecker_Env.EraseUniverses]
                                     env.FStar_SMTEncoding_Env.tcenv
                                     head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____5829
                                  in
                               let uu____5830 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____5830 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____5846;
                                            FStar_Syntax_Syntax.vars =
                                              uu____5847;_},uu____5848)
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
                                     | uu____5862 ->
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
           let uu____5927 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____5927 with
            | (bs1,body1,opening) ->
                let fallback uu____5952 =
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
                  let uu____5957 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort)
                     in
                  (uu____5957, [decl])  in
                let is_impure rc =
                  let uu____5966 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                      env.FStar_SMTEncoding_Env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____5966 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____5978 =
                          let uu____5991 =
                            FStar_TypeChecker_Env.get_range
                              env.FStar_SMTEncoding_Env.tcenv
                             in
                          FStar_TypeChecker_Util.new_implicit_var
                            "SMTEncoding codomain" uu____5991
                            env.FStar_SMTEncoding_Env.tcenv
                            FStar_Syntax_Util.ktype0
                           in
                        (match uu____5978 with
                         | (t1,uu____5993,uu____5994) -> t1)
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  let uu____6012 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                     in
                  if uu____6012
                  then
                    let uu____6015 = FStar_Syntax_Syntax.mk_Total res_typ  in
                    FStar_Pervasives_Native.Some uu____6015
                  else
                    (let uu____6017 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid
                        in
                     if uu____6017
                     then
                       let uu____6020 = FStar_Syntax_Syntax.mk_GTotal res_typ
                          in
                       FStar_Pervasives_Native.Some uu____6020
                     else FStar_Pervasives_Native.None)
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____6027 =
                         let uu____6032 =
                           let uu____6033 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____6033
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____6032)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____6027);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____6035 =
                       (is_impure rc) &&
                         (let uu____6037 =
                            FStar_TypeChecker_Env.is_reifiable
                              env.FStar_SMTEncoding_Env.tcenv rc
                             in
                          Prims.op_Negation uu____6037)
                        in
                     if uu____6035
                     then fallback ()
                     else
                       (let cache_size =
                          FStar_Util.smap_size
                            env.FStar_SMTEncoding_Env.cache
                           in
                        let uu____6044 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____6044 with
                        | (vars,guards,envbody,decls,uu____6069) ->
                            let body2 =
                              let uu____6083 =
                                FStar_TypeChecker_Env.is_reifiable
                                  env.FStar_SMTEncoding_Env.tcenv rc
                                 in
                              if uu____6083
                              then
                                FStar_TypeChecker_Util.reify_body
                                  env.FStar_SMTEncoding_Env.tcenv body1
                              else body1  in
                            let uu____6085 = encode_term body2 envbody  in
                            (match uu____6085 with
                             | (body3,decls') ->
                                 let uu____6096 =
                                   let uu____6105 = codomain_eff rc  in
                                   match uu____6105 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____6124 = encode_term tfun env
                                          in
                                       (match uu____6124 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____6096 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____6158 =
                                          let uu____6169 =
                                            let uu____6170 =
                                              let uu____6175 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____6175, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____6170
                                             in
                                          ([], vars, uu____6169)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t0.FStar_Syntax_Syntax.pos
                                          uu____6158
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
                                            let uu____6197 =
                                              let uu____6204 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1
                                                 in
                                              FStar_List.append uu____6204
                                                cvars
                                               in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____6197
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
                                      let uu____6227 =
                                        FStar_Util.smap_try_find
                                          env.FStar_SMTEncoding_Env.cache
                                          tkey_hash
                                         in
                                      (match uu____6227 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____6235 =
                                             let uu____6236 =
                                               let uu____6243 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1
                                                  in
                                               ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                                 uu____6243)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6236
                                              in
                                           (uu____6235,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (FStar_SMTEncoding_Env.use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____6252 =
                                             is_an_eta_expansion env vars
                                               body3
                                              in
                                           (match uu____6252 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____6261 =
                                                    let uu____6262 =
                                                      FStar_Util.smap_size
                                                        env.FStar_SMTEncoding_Env.cache
                                                       in
                                                    uu____6262 = cache_size
                                                     in
                                                  if uu____6261
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
                                                    let uu____6274 =
                                                      let uu____6275 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash
                                                         in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____6275
                                                       in
                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                      uu____6274
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
                                                  let uu____6280 =
                                                    let uu____6287 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    (fsym, uu____6287)  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____6280
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
                                                      let uu____6305 =
                                                        let uu____6306 =
                                                          let uu____6313 =
                                                            FStar_SMTEncoding_Term.mkForall
                                                              t0.FStar_Syntax_Syntax.pos
                                                              ([[f]], cvars1,
                                                                f_has_t)
                                                             in
                                                          (uu____6313,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name)
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____6306
                                                         in
                                                      [uu____6305]
                                                   in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym
                                                     in
                                                  let uu____6324 =
                                                    let uu____6331 =
                                                      let uu____6332 =
                                                        let uu____6343 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3)
                                                           in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____6343)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        t0.FStar_Syntax_Syntax.pos
                                                        uu____6332
                                                       in
                                                    (uu____6331,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____6324
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
                                                ((let uu____6356 =
                                                    FStar_SMTEncoding_Env.mk_cache_entry
                                                      env fsym cvar_sorts
                                                      f_decls
                                                     in
                                                  FStar_Util.smap_add
                                                    env.FStar_SMTEncoding_Env.cache
                                                    tkey_hash uu____6356);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____6357,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____6358;
                          FStar_Syntax_Syntax.lbunivs = uu____6359;
                          FStar_Syntax_Syntax.lbtyp = uu____6360;
                          FStar_Syntax_Syntax.lbeff = uu____6361;
                          FStar_Syntax_Syntax.lbdef = uu____6362;
                          FStar_Syntax_Syntax.lbattrs = uu____6363;
                          FStar_Syntax_Syntax.lbpos = uu____6364;_}::uu____6365),uu____6366)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____6396;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____6398;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____6400;
                FStar_Syntax_Syntax.lbpos = uu____6401;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____6425 ->
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
              let uu____6495 =
                let uu____6500 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____6500 env  in
              match uu____6495 with
              | (ee1,decls1) ->
                  let uu____6525 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____6525 with
                   | (xs,e21) ->
                       let uu____6544 = FStar_List.hd xs  in
                       (match uu____6544 with
                        | (x1,uu____6558) ->
                            let env' =
                              FStar_SMTEncoding_Env.push_term_var env x1 ee1
                               in
                            let uu____6560 = encode_body e21 env'  in
                            (match uu____6560 with
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
            let uu____6590 =
              let uu____6597 =
                let uu____6598 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____6598  in
              FStar_SMTEncoding_Env.gen_term_var env uu____6597  in
            match uu____6590 with
            | (scrsym,scr',env1) ->
                let uu____6606 = encode_term e env1  in
                (match uu____6606 with
                 | (scr,decls) ->
                     let uu____6617 =
                       let encode_branch b uu____6646 =
                         match uu____6646 with
                         | (else_case,decls1) ->
                             let uu____6665 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____6665 with
                              | (p,w,br) ->
                                  let uu____6691 = encode_pat env1 p  in
                                  (match uu____6691 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____6728  ->
                                                   match uu____6728 with
                                                   | (x,t) ->
                                                       FStar_SMTEncoding_Env.push_term_var
                                                         env2 x t) env1)
                                          in
                                       let uu____6735 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____6757 =
                                               encode_term w1 env2  in
                                             (match uu____6757 with
                                              | (w2,decls2) ->
                                                  let uu____6770 =
                                                    let uu____6771 =
                                                      let uu____6776 =
                                                        let uu____6777 =
                                                          let uu____6782 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____6782)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____6777
                                                         in
                                                      (guard, uu____6776)  in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____6771
                                                     in
                                                  (uu____6770, decls2))
                                          in
                                       (match uu____6735 with
                                        | (guard1,decls2) ->
                                            let uu____6797 =
                                              encode_br br env2  in
                                            (match uu____6797 with
                                             | (br1,decls3) ->
                                                 let uu____6810 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____6810,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____6617 with
                      | (match_tm,decls1) ->
                          let uu____6831 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange
                             in
                          (uu____6831, decls1)))

and (encode_pat :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.pat ->
      (FStar_SMTEncoding_Env.env_t,pattern) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun pat  ->
      (let uu____6853 =
         FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
           FStar_Options.Low
          in
       if uu____6853
       then
         let uu____6854 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____6854
       else ());
      (let uu____6856 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____6856 with
       | (vars,pat_term) ->
           let uu____6873 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____6926  ->
                     fun v1  ->
                       match uu____6926 with
                       | (env1,vars1) ->
                           let uu____6978 =
                             FStar_SMTEncoding_Env.gen_term_var env1 v1  in
                           (match uu____6978 with
                            | (xx,uu____7000,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, []))
              in
           (match uu____6873 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____7083 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____7084 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____7085 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____7093 = encode_const c env1  in
                      (match uu____7093 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____7101::uu____7102 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____7105 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon
                            env1.FStar_SMTEncoding_Env.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____7126 =
                          FStar_TypeChecker_Env.datacons_of_typ
                            env1.FStar_SMTEncoding_Env.tcenv tc_name
                           in
                        match uu____7126 with
                        | (uu____7133,uu____7134::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____7137 ->
                            FStar_SMTEncoding_Env.mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____7170  ->
                                  match uu____7170 with
                                  | (arg,uu____7178) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____7184 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____7184))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____7215) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____7246 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____7269 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____7313  ->
                                  match uu____7313 with
                                  | (arg,uu____7327) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____7333 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____7333))
                         in
                      FStar_All.pipe_right uu____7269 FStar_List.flatten
                   in
                let pat_term1 uu____7363 = encode_term pat_term env1  in
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
      let uu____7373 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____7417  ->
                fun uu____7418  ->
                  match (uu____7417, uu____7418) with
                  | ((tms,decls),(t,uu____7454)) ->
                      let uu____7475 = encode_term t env  in
                      (match uu____7475 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____7373 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____7532 = FStar_Syntax_Util.list_elements e  in
        match uu____7532 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____7559 =
          let uu____7574 = FStar_Syntax_Util.unmeta p  in
          FStar_All.pipe_right uu____7574 FStar_Syntax_Util.head_and_args  in
        match uu____7559 with
        | (head1,args) ->
            let uu____7617 =
              let uu____7630 =
                let uu____7631 = FStar_Syntax_Util.un_uinst head1  in
                uu____7631.FStar_Syntax_Syntax.n  in
              (uu____7630, args)  in
            (match uu____7617 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____7649,uu____7650)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____7688 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or t1 =
          let uu____7736 =
            let uu____7751 = FStar_Syntax_Util.unmeta t1  in
            FStar_All.pipe_right uu____7751 FStar_Syntax_Util.head_and_args
             in
          match uu____7736 with
          | (head1,args) ->
              let uu____7792 =
                let uu____7805 =
                  let uu____7806 = FStar_Syntax_Util.un_uinst head1  in
                  uu____7806.FStar_Syntax_Syntax.n  in
                (uu____7805, args)  in
              (match uu____7792 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____7823)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____7850 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____7876 = smt_pat_or t1  in
            (match uu____7876 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____7896 = list_elements1 e  in
                 FStar_All.pipe_right uu____7896
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____7922 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____7922
                           (FStar_List.map one_pat)))
             | uu____7941 ->
                 let uu____7946 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____7946])
        | uu____7987 ->
            let uu____7990 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____7990]
         in
      let uu____8031 =
        let uu____8046 =
          let uu____8047 = FStar_Syntax_Subst.compress t  in
          uu____8047.FStar_Syntax_Syntax.n  in
        match uu____8046 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____8082 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____8082 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____8117;
                        FStar_Syntax_Syntax.effect_name = uu____8118;
                        FStar_Syntax_Syntax.result_typ = uu____8119;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____8121)::(post,uu____8123)::(pats,uu____8125)::[];
                        FStar_Syntax_Syntax.flags = uu____8126;_}
                      ->
                      let uu____8167 = lemma_pats pats  in
                      (binders1, pre, post, uu____8167)
                  | uu____8178 -> failwith "impos"))
        | uu____8193 -> failwith "Impos"  in
      match uu____8031 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___347_8229 = env  in
            {
              FStar_SMTEncoding_Env.bvar_bindings =
                (uu___347_8229.FStar_SMTEncoding_Env.bvar_bindings);
              FStar_SMTEncoding_Env.fvar_bindings =
                (uu___347_8229.FStar_SMTEncoding_Env.fvar_bindings);
              FStar_SMTEncoding_Env.depth =
                (uu___347_8229.FStar_SMTEncoding_Env.depth);
              FStar_SMTEncoding_Env.tcenv =
                (uu___347_8229.FStar_SMTEncoding_Env.tcenv);
              FStar_SMTEncoding_Env.warn =
                (uu___347_8229.FStar_SMTEncoding_Env.warn);
              FStar_SMTEncoding_Env.cache =
                (uu___347_8229.FStar_SMTEncoding_Env.cache);
              FStar_SMTEncoding_Env.nolabels =
                (uu___347_8229.FStar_SMTEncoding_Env.nolabels);
              FStar_SMTEncoding_Env.use_zfuel_name = true;
              FStar_SMTEncoding_Env.encode_non_total_function_typ =
                (uu___347_8229.FStar_SMTEncoding_Env.encode_non_total_function_typ);
              FStar_SMTEncoding_Env.current_module_name =
                (uu___347_8229.FStar_SMTEncoding_Env.current_module_name);
              FStar_SMTEncoding_Env.encoding_quantifier =
                (uu___347_8229.FStar_SMTEncoding_Env.encoding_quantifier)
            }  in
          let uu____8230 =
            encode_binders FStar_Pervasives_Native.None binders env1  in
          (match uu____8230 with
           | (vars,guards,env2,decls,uu____8255) ->
               let uu____8268 = encode_smt_patterns patterns env2  in
               (match uu____8268 with
                | (pats,decls') ->
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
                    let env3 =
                      let uu___348_8301 = env2  in
                      {
                        FStar_SMTEncoding_Env.bvar_bindings =
                          (uu___348_8301.FStar_SMTEncoding_Env.bvar_bindings);
                        FStar_SMTEncoding_Env.fvar_bindings =
                          (uu___348_8301.FStar_SMTEncoding_Env.fvar_bindings);
                        FStar_SMTEncoding_Env.depth =
                          (uu___348_8301.FStar_SMTEncoding_Env.depth);
                        FStar_SMTEncoding_Env.tcenv =
                          (uu___348_8301.FStar_SMTEncoding_Env.tcenv);
                        FStar_SMTEncoding_Env.warn =
                          (uu___348_8301.FStar_SMTEncoding_Env.warn);
                        FStar_SMTEncoding_Env.cache =
                          (uu___348_8301.FStar_SMTEncoding_Env.cache);
                        FStar_SMTEncoding_Env.nolabels = true;
                        FStar_SMTEncoding_Env.use_zfuel_name =
                          (uu___348_8301.FStar_SMTEncoding_Env.use_zfuel_name);
                        FStar_SMTEncoding_Env.encode_non_total_function_typ =
                          (uu___348_8301.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                        FStar_SMTEncoding_Env.current_module_name =
                          (uu___348_8301.FStar_SMTEncoding_Env.current_module_name);
                        FStar_SMTEncoding_Env.encoding_quantifier =
                          (uu___348_8301.FStar_SMTEncoding_Env.encoding_quantifier)
                      }  in
                    let uu____8302 =
                      let uu____8307 = FStar_Syntax_Util.unmeta pre  in
                      encode_formula uu____8307 env3  in
                    (match uu____8302 with
                     | (pre1,decls'') ->
                         let uu____8314 =
                           let uu____8319 = FStar_Syntax_Util.unmeta post1
                              in
                           encode_formula uu____8319 env3  in
                         (match uu____8314 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append decls'
                                     (FStar_List.append decls'' decls'''))
                                 in
                              let uu____8329 =
                                let uu____8330 =
                                  let uu____8341 =
                                    let uu____8342 =
                                      let uu____8347 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards)
                                         in
                                      (uu____8347, post2)  in
                                    FStar_SMTEncoding_Util.mkImp uu____8342
                                     in
                                  (pats, vars, uu____8341)  in
                                FStar_SMTEncoding_Term.mkForall
                                  t.FStar_Syntax_Syntax.pos uu____8330
                                 in
                              (uu____8329, decls1)))))

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
        let uu___349_8369 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___349_8369.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___349_8369.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___349_8369.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___349_8369.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___349_8369.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.cache =
            (uu___349_8369.FStar_SMTEncoding_Env.cache);
          FStar_SMTEncoding_Env.nolabels =
            (uu___349_8369.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___349_8369.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___349_8369.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___349_8369.FStar_SMTEncoding_Env.encoding_quantifier)
        }  in
      let encode_smt_pattern t =
        let uu____8384 = FStar_Syntax_Util.head_and_args t  in
        match uu____8384 with
        | (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____8439::(x,uu____8441)::(t1,uu____8443)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____8490 = encode_term x env1  in
                 (match uu____8490 with
                  | (x1,decls) ->
                      let uu____8501 = encode_term t1 env1  in
                      (match uu____8501 with
                       | (t2,decls') ->
                           let uu____8512 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                           (uu____8512, (FStar_List.append decls decls'))))
             | uu____8513 -> encode_term t env1)
         in
      FStar_List.fold_right
        (fun pats  ->
           fun uu____8552  ->
             match uu____8552 with
             | (pats_l1,decls) ->
                 let uu____8595 =
                   FStar_List.fold_right
                     (fun uu____8628  ->
                        fun uu____8629  ->
                          match (uu____8628, uu____8629) with
                          | ((p,uu____8667),(pats1,decls1)) ->
                              let uu____8696 = encode_smt_pattern p  in
                              (match uu____8696 with
                               | (t,d) ->
                                   let uu____8711 =
                                     FStar_SMTEncoding_Term.check_pattern_ok
                                       t
                                      in
                                   (match uu____8711 with
                                    | FStar_Pervasives_Native.None  ->
                                        ((t :: pats1),
                                          (FStar_List.append d decls1))
                                    | FStar_Pervasives_Native.Some
                                        illegal_subterm ->
                                        ((let uu____8728 =
                                            let uu____8733 =
                                              let uu____8734 =
                                                FStar_Syntax_Print.term_to_string
                                                  p
                                                 in
                                              let uu____8735 =
                                                FStar_SMTEncoding_Term.print_smt_term
                                                  illegal_subterm
                                                 in
                                              FStar_Util.format2
                                                "Pattern %s contains illegal sub-term (%s); dropping it"
                                                uu____8734 uu____8735
                                               in
                                            (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                                              uu____8733)
                                             in
                                          FStar_Errors.log_issue
                                            p.FStar_Syntax_Syntax.pos
                                            uu____8728);
                                         (pats1,
                                           (FStar_List.append d decls1))))))
                     pats ([], decls)
                    in
                 (match uu____8595 with
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
        let uu____8792 =
          FStar_All.pipe_left
            (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____8792
        then
          let uu____8793 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____8794 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____8793 uu____8794
        else ()  in
      let enc f r l =
        let uu____8833 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____8861 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____8861 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____8833 with
        | (decls,args) ->
            let uu____8890 =
              let uu___350_8891 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___350_8891.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___350_8891.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____8890, decls)
         in
      let const_op f r uu____8926 = let uu____8939 = f r  in (uu____8939, [])
         in
      let un_op f l =
        let uu____8962 = FStar_List.hd l  in FStar_All.pipe_left f uu____8962
         in
      let bin_op f uu___341_8982 =
        match uu___341_8982 with
        | t1::t2::[] -> f (t1, t2)
        | uu____8993 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____9033 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____9056  ->
                 match uu____9056 with
                 | (t,uu____9070) ->
                     let uu____9071 = encode_formula t env  in
                     (match uu____9071 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____9033 with
        | (decls,phis) ->
            let uu____9100 =
              let uu___351_9101 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___351_9101.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___351_9101.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____9100, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____9164  ->
               match uu____9164 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____9183) -> false
                    | uu____9184 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____9199 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____9199
        else
          (let uu____9213 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____9213 r rf)
         in
      let mk_imp1 r uu___342_9248 =
        match uu___342_9248 with
        | (lhs,uu____9254)::(rhs,uu____9256)::[] ->
            let uu____9283 = encode_formula rhs env  in
            (match uu____9283 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____9298) ->
                      (l1, decls1)
                  | uu____9303 ->
                      let uu____9304 = encode_formula lhs env  in
                      (match uu____9304 with
                       | (l2,decls2) ->
                           let uu____9315 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____9315, (FStar_List.append decls1 decls2)))))
        | uu____9316 -> failwith "impossible"  in
      let mk_ite r uu___343_9343 =
        match uu___343_9343 with
        | (guard,uu____9349)::(_then,uu____9351)::(_else,uu____9353)::[] ->
            let uu____9390 = encode_formula guard env  in
            (match uu____9390 with
             | (g,decls1) ->
                 let uu____9401 = encode_formula _then env  in
                 (match uu____9401 with
                  | (t,decls2) ->
                      let uu____9412 = encode_formula _else env  in
                      (match uu____9412 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____9424 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____9453 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l  in
        f uu____9453  in
      let connectives =
        let uu____9483 =
          let uu____9508 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____9508)  in
        let uu____9551 =
          let uu____9578 =
            let uu____9603 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____9603)  in
          let uu____9646 =
            let uu____9673 =
              let uu____9700 =
                let uu____9725 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____9725)  in
              let uu____9768 =
                let uu____9795 =
                  let uu____9822 =
                    let uu____9847 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____9847)  in
                  [uu____9822;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____9795  in
              uu____9700 :: uu____9768  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____9673  in
          uu____9578 :: uu____9646  in
        uu____9483 :: uu____9551  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____10300 = encode_formula phi' env  in
            (match uu____10300 with
             | (phi2,decls) ->
                 let uu____10311 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____10311, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____10312 ->
            let uu____10319 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____10319 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____10358 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____10358 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____10370;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____10372;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____10374;
                 FStar_Syntax_Syntax.lbpos = uu____10375;_}::[]),e2)
            ->
            let uu____10399 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____10399 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____10446::(x,uu____10448)::(t,uu____10450)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____10497 = encode_term x env  in
                 (match uu____10497 with
                  | (x1,decls) ->
                      let uu____10508 = encode_term t env  in
                      (match uu____10508 with
                       | (t1,decls') ->
                           let uu____10519 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____10519, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____10522)::(msg,uu____10524)::(phi2,uu____10526)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____10571 =
                   let uu____10576 =
                     let uu____10577 = FStar_Syntax_Subst.compress r  in
                     uu____10577.FStar_Syntax_Syntax.n  in
                   let uu____10580 =
                     let uu____10581 = FStar_Syntax_Subst.compress msg  in
                     uu____10581.FStar_Syntax_Syntax.n  in
                   (uu____10576, uu____10580)  in
                 (match uu____10571 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____10590))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____10596 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____10603)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____10628 when head_redex env head2 ->
                 let uu____10641 = whnf env phi1  in
                 encode_formula uu____10641 env
             | uu____10642 ->
                 let uu____10655 = encode_term phi1 env  in
                 (match uu____10655 with
                  | (tt,decls) ->
                      let tt1 =
                        let uu____10667 =
                          let uu____10668 =
                            FStar_Range.use_range
                              tt.FStar_SMTEncoding_Term.rng
                             in
                          let uu____10669 =
                            FStar_Range.use_range
                              phi1.FStar_Syntax_Syntax.pos
                             in
                          FStar_Range.rng_included uu____10668 uu____10669
                           in
                        if uu____10667
                        then tt
                        else
                          (let uu___352_10671 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___352_10671.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___352_10671.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      let uu____10672 = FStar_SMTEncoding_Term.mk_Valid tt1
                         in
                      (uu____10672, decls)))
        | uu____10673 ->
            let uu____10674 = encode_term phi1 env  in
            (match uu____10674 with
             | (tt,decls) ->
                 let tt1 =
                   let uu____10686 =
                     let uu____10687 =
                       FStar_Range.use_range tt.FStar_SMTEncoding_Term.rng
                        in
                     let uu____10688 =
                       FStar_Range.use_range phi1.FStar_Syntax_Syntax.pos  in
                     FStar_Range.rng_included uu____10687 uu____10688  in
                   if uu____10686
                   then tt
                   else
                     (let uu___353_10690 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___353_10690.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___353_10690.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 let uu____10691 = FStar_SMTEncoding_Term.mk_Valid tt1  in
                 (uu____10691, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____10735 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____10735 with
        | (vars,guards,env2,decls,uu____10774) ->
            let uu____10787 = encode_smt_patterns ps env2  in
            (match uu____10787 with
             | (pats,decls') ->
                 let uu____10830 = encode_formula body env2  in
                 (match uu____10830 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____10862;
                             FStar_SMTEncoding_Term.rng = uu____10863;_}::[])::[]
                            when
                            let uu____10878 =
                              FStar_Ident.text_of_lid
                                FStar_Parser_Const.guard_free
                               in
                            uu____10878 = gf -> []
                        | uu____10879 -> guards  in
                      let uu____10884 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____10884, body1,
                        (FStar_List.append decls
                           (FStar_List.append decls' decls'')))))
         in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi  in
       let uu____10895 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____10895 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____10904 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____11010  ->
                     match uu____11010 with
                     | (l,uu____11034) -> FStar_Ident.lid_equals op l))
              in
           (match uu____10904 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____11103,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____11187 = encode_q_body env vars pats body  in
             match uu____11187 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____11232 =
                     let uu____11243 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____11243)  in
                   FStar_SMTEncoding_Term.mkForall
                     phi1.FStar_Syntax_Syntax.pos uu____11232
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____11266 = encode_q_body env vars pats body  in
             match uu____11266 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____11310 =
                   let uu____11311 =
                     let uu____11322 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____11322)  in
                   FStar_SMTEncoding_Term.mkExists
                     phi1.FStar_Syntax_Syntax.pos uu____11311
                    in
                 (uu____11310, decls))))
