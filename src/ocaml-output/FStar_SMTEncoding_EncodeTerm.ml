open Prims
let mkForall_fuel' :
  'Auu____7 .
    'Auu____7 ->
      (FStar_SMTEncoding_Term.pat Prims.list Prims.list,FStar_SMTEncoding_Term.fvs,
        FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
        FStar_SMTEncoding_Term.term
  =
  fun n1  ->
    fun uu____27  ->
      match uu____27 with
      | (pats,vars,body) ->
          let fallback uu____54 =
            FStar_SMTEncoding_Util.mkForall (pats, vars, body)  in
          let uu____59 = FStar_Options.unthrottle_inductives ()  in
          if uu____59
          then fallback ()
          else
            (let uu____61 =
               FStar_SMTEncoding_Env.fresh_fvar "f"
                 FStar_SMTEncoding_Term.Fuel_sort
                in
             match uu____61 with
             | (fsym,fterm) ->
                 let add_fuel1 tms =
                   FStar_All.pipe_right tms
                     (FStar_List.map
                        (fun p  ->
                           match p.FStar_SMTEncoding_Term.tm with
                           | FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var "HasType",args) ->
                               FStar_SMTEncoding_Util.mkApp
                                 ("HasTypeFuel", (fterm :: args))
                           | uu____94 -> p))
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
                             let uu____115 = add_fuel1 guards  in
                             FStar_SMTEncoding_Util.mk_and_l uu____115
                         | uu____118 ->
                             let uu____119 = add_fuel1 [guard]  in
                             FStar_All.pipe_right uu____119 FStar_List.hd
                          in
                       FStar_SMTEncoding_Util.mkImp (guard1, body')
                   | uu____124 -> body  in
                 let vars1 = (fsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars
                    in
                 FStar_SMTEncoding_Util.mkForall (pats1, vars1, body1))
  
let (mkForall_fuel :
  (FStar_SMTEncoding_Term.pat Prims.list Prims.list,FStar_SMTEncoding_Term.fvs,
    FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
    FStar_SMTEncoding_Term.term)
  = mkForall_fuel' (Prims.parse_int "1") 
let (head_normal :
  FStar_SMTEncoding_Env.env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
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
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____228 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____246;
             FStar_Syntax_Syntax.vars = uu____247;_},uu____248)
          ->
          let uu____269 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____269 FStar_Option.isNone
      | uu____286 -> false
  
let (head_redex :
  FStar_SMTEncoding_Env.env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____297 =
        let uu____298 = FStar_Syntax_Util.un_uinst t  in
        uu____298.FStar_Syntax_Syntax.n  in
      match uu____297 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____301,uu____302,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___70_323  ->
                  match uu___70_323 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____324 -> false) rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____326 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____326 FStar_Option.isSome
      | uu____343 -> false
  
let (whnf :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____354 = head_normal env t  in
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
    let uu____371 =
      let uu____372 = FStar_Syntax_Syntax.null_binder t  in [uu____372]  in
    let uu____373 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
       in
    FStar_Syntax_Util.abs uu____371 uu____373 FStar_Pervasives_Native.None
  
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
                    let uu____415 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____415
                | s ->
                    let uu____418 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____418) e)
  
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
          let uu____466 =
            let uu____471 =
              let uu____472 = FStar_Util.string_of_int arity  in
              let uu____473 = FStar_Util.string_of_int n_args  in
              FStar_Util.format3
                "Head symbol %s expects at least %s arguments; got only %s"
                head1 uu____472 uu____473
               in
            (FStar_Errors.Fatal_SMTEncodingArityMismatch, uu____471)  in
          FStar_Errors.raise_error uu____466 rng
  
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
              (let uu____512 = FStar_Util.first_N arity args  in
               match uu____512 with
               | (args1,rest) ->
                   let head2 = FStar_SMTEncoding_Util.mkApp' (head1, args1)
                      in
                   mk_Apply_args head2 rest)
            else
              (let uu____535 = FStar_SMTEncoding_Term.op_to_string head1  in
               raise_arity_mismatch uu____535 arity n_args rng)
  
let (is_app : FStar_SMTEncoding_Term.op -> Prims.bool) =
  fun uu___71_544  ->
    match uu___71_544 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____545 -> false
  
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
                       FStar_SMTEncoding_Term.freevars = uu____591;
                       FStar_SMTEncoding_Term.rng = uu____592;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____615) ->
              let uu____624 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____635 -> false) args (FStar_List.rev xs))
                 in
              if uu____624
              then FStar_SMTEncoding_Env.tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____639,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t  in
              let uu____643 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____647 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars
                           in
                        Prims.op_Negation uu____647))
                 in
              if uu____643
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____651 -> FStar_Pervasives_Native.None  in
        check_partial_applications body (FStar_List.rev vars)
  
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
        | FStar_Syntax_Syntax.Tm_arrow uu____932 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____945 ->
            let uu____952 = FStar_Syntax_Util.unrefine t1  in
            aux true uu____952
        | uu____953 ->
            if norm1
            then let uu____954 = whnf env t1  in aux false uu____954
            else
              (let uu____956 =
                 let uu____957 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let uu____958 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____957 uu____958
                  in
               failwith uu____956)
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
    | FStar_Syntax_Syntax.Tm_refine (bv,uu____992) ->
        curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort
    | uu____997 ->
        let uu____998 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____998)
  
let is_arithmetic_primitive :
  'Auu____1015 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____1015 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1037::uu____1038::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1042::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____1045 -> false
  
let (isInteger : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____1068 -> false
  
let (getInteger : FStar_Syntax_Syntax.term' -> Prims.int) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____1085 -> failwith "Expected an Integer term"
  
let is_BitVector_primitive :
  'Auu____1092 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____1092)
        FStar_Pervasives_Native.tuple2 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____1133)::uu____1134::uu____1135::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____1186)::uu____1187::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____1224 -> false
  
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
          let uu____1527 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue  in
          (uu____1527, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____1530 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse  in
          (uu____1530, [])
      | FStar_Const.Const_char c1 ->
          let uu____1534 =
            let uu____1535 =
              let uu____1542 =
                let uu____1545 =
                  let uu____1546 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1)
                     in
                  FStar_SMTEncoding_Term.boxInt uu____1546  in
                [uu____1545]  in
              ("FStar.Char.__char_of_int", uu____1542)  in
            FStar_SMTEncoding_Util.mkApp uu____1535  in
          (uu____1534, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____1562 =
            let uu____1563 = FStar_SMTEncoding_Util.mkInteger i  in
            FStar_SMTEncoding_Term.boxInt uu____1563  in
          (uu____1562, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.FStar_SMTEncoding_Env.tcenv).FStar_TypeChecker_Env.dsenv
              repr sw FStar_Range.dummyRange
             in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____1584) ->
          let uu____1585 =
            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.string_const s
             in
          (uu____1585, [])
      | FStar_Const.Const_range uu____1588 ->
          let uu____1589 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          (uu____1589, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | c1 ->
          let uu____1595 =
            let uu____1596 = FStar_Syntax_Print.const_to_string c1  in
            FStar_Util.format1 "Unhandled constant: %s" uu____1596  in
          failwith uu____1595

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
        (let uu____1625 =
           FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
             FStar_Options.Low
            in
         if uu____1625
         then
           let uu____1626 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____1626
         else ());
        (let uu____1628 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____1712  ->
                   fun b  ->
                     match uu____1712 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____1791 =
                           let x =
                             FStar_SMTEncoding_Env.unmangle
                               (FStar_Pervasives_Native.fst b)
                              in
                           let uu____1807 =
                             FStar_SMTEncoding_Env.gen_term_var env1 x  in
                           match uu____1807 with
                           | (xxsym,xx,env') ->
                               let uu____1831 =
                                 let uu____1836 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____1836 env1 xx
                                  in
                               (match uu____1831 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x))
                            in
                         (match uu____1791 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____1628 with
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
          let uu____1995 = encode_term t env  in
          match uu____1995 with
          | (t1,decls) ->
              let uu____2006 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____2006, decls)

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
          let uu____2017 = encode_term t env  in
          match uu____2017 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____2032 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____2032, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____2034 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____2034, decls))

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
        let uu____2040 = encode_args args_e env  in
        match uu____2040 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____2059 -> failwith "Impossible"  in
            let unary arg_tms1 =
              let uu____2070 = FStar_List.hd arg_tms1  in
              FStar_SMTEncoding_Term.unboxInt uu____2070  in
            let binary arg_tms1 =
              let uu____2085 =
                let uu____2086 = FStar_List.hd arg_tms1  in
                FStar_SMTEncoding_Term.unboxInt uu____2086  in
              let uu____2087 =
                let uu____2088 =
                  let uu____2089 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____2089  in
                FStar_SMTEncoding_Term.unboxInt uu____2088  in
              (uu____2085, uu____2087)  in
            let mk_default uu____2097 =
              let uu____2098 =
                FStar_SMTEncoding_Env.lookup_free_var_sym env
                  head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____2098 with
              | (fname,fuel_args,arity) ->
                  let args = FStar_List.append fuel_args arg_tms  in
                  maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity
                    args
               in
            let mk_l op mk_args ts =
              let uu____2160 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____2160
              then
                let uu____2161 =
                  let uu____2162 = mk_args ts  in op uu____2162  in
                FStar_All.pipe_right uu____2161 FStar_SMTEncoding_Term.boxInt
              else mk_default ()  in
            let mk_nl nm op ts =
              let uu____2197 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____2197
              then
                let uu____2198 = binary ts  in
                match uu____2198 with
                | (t1,t2) ->
                    let uu____2205 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____2205
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____2209 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____2209
                 then
                   let uu____2210 =
                     let uu____2211 = binary ts  in op uu____2211  in
                   FStar_All.pipe_right uu____2210
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
            let uu____2372 =
              let uu____2382 =
                FStar_List.tryFind
                  (fun uu____2406  ->
                     match uu____2406 with
                     | (l,uu____2416) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____2382 FStar_Util.must  in
            (match uu____2372 with
             | (uu____2460,op) ->
                 let uu____2472 = op arg_tms  in (uu____2472, decls))

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
        let uu____2480 = FStar_List.hd args_e  in
        match uu____2480 with
        | (tm_sz,uu____2488) ->
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let uu____2498 =
                FStar_Util.smap_try_find env.FStar_SMTEncoding_Env.cache
                  sz_key
                 in
              match uu____2498 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None  ->
                  let t_decls1 = FStar_SMTEncoding_Term.mkBvConstructor sz
                     in
                  ((let uu____2506 =
                      FStar_SMTEncoding_Env.mk_cache_entry env "" [] []  in
                    FStar_Util.smap_add env.FStar_SMTEncoding_Env.cache
                      sz_key uu____2506);
                   t_decls1)
               in
            let uu____2507 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____2527::(sz_arg,uu____2529)::uu____2530::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____2579 =
                    let uu____2582 = FStar_List.tail args_e  in
                    FStar_List.tail uu____2582  in
                  let uu____2585 =
                    let uu____2588 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____2588  in
                  (uu____2579, uu____2585)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____2594::(sz_arg,uu____2596)::uu____2597::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____2646 =
                    let uu____2647 = FStar_Syntax_Print.term_to_string sz_arg
                       in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____2647
                     in
                  failwith uu____2646
              | uu____2656 ->
                  let uu____2663 = FStar_List.tail args_e  in
                  (uu____2663, FStar_Pervasives_Native.None)
               in
            (match uu____2507 with
             | (arg_tms,ext_sz) ->
                 let uu____2686 = encode_args arg_tms env  in
                 (match uu____2686 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____2707 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____2718 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____2718  in
                      let unary_arith arg_tms2 =
                        let uu____2729 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____2729  in
                      let binary arg_tms2 =
                        let uu____2744 =
                          let uu____2745 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____2745
                           in
                        let uu____2746 =
                          let uu____2747 =
                            let uu____2748 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____2748  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____2747
                           in
                        (uu____2744, uu____2746)  in
                      let binary_arith arg_tms2 =
                        let uu____2765 =
                          let uu____2766 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____2766
                           in
                        let uu____2767 =
                          let uu____2768 =
                            let uu____2769 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____2769  in
                          FStar_SMTEncoding_Term.unboxInt uu____2768  in
                        (uu____2765, uu____2767)  in
                      let mk_bv op mk_args resBox ts =
                        let uu____2827 =
                          let uu____2828 = mk_args ts  in op uu____2828  in
                        FStar_All.pipe_right uu____2827 resBox  in
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
                        let uu____2960 =
                          let uu____2965 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____2965  in
                        let uu____2967 =
                          let uu____2972 =
                            let uu____2973 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____2973  in
                          FStar_SMTEncoding_Term.boxBitVec uu____2972  in
                        mk_bv uu____2960 unary uu____2967 arg_tms2  in
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
                      let uu____3206 =
                        let uu____3216 =
                          FStar_List.tryFind
                            (fun uu____3240  ->
                               match uu____3240 with
                               | (l,uu____3250) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____3216 FStar_Util.must  in
                      (match uu____3206 with
                       | (uu____3296,op) ->
                           let uu____3308 = op arg_tms1  in
                           (uu____3308, (FStar_List.append sz_decls decls)))))

and (encode_term :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____3319 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____3319
       then
         let uu____3320 = FStar_Syntax_Print.tag_of_term t  in
         let uu____3321 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____3322 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____3320 uu____3321
           uu____3322
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____3328 ->
           let uu____3353 =
             let uu____3354 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____3355 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____3356 = FStar_Syntax_Print.term_to_string t0  in
             let uu____3357 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____3354
               uu____3355 uu____3356 uu____3357
              in
           failwith uu____3353
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____3362 =
             let uu____3363 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____3364 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____3365 = FStar_Syntax_Print.term_to_string t0  in
             let uu____3366 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____3363
               uu____3364 uu____3365 uu____3366
              in
           failwith uu____3362
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____3372 = FStar_Syntax_Util.unfold_lazy i  in
           encode_term uu____3372 env
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____3374 =
             let uu____3375 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____3375
              in
           failwith uu____3374
       | FStar_Syntax_Syntax.Tm_ascribed (t1,(k,uu____3382),uu____3383) ->
           let uu____3432 =
             match k with
             | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
             | uu____3440 -> false  in
           if uu____3432
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t1 env
       | FStar_Syntax_Syntax.Tm_quoted (qt,uu____3457) ->
           let tv =
             let uu____3463 = FStar_Reflection_Basic.inspect_ln qt  in
             FStar_Syntax_Embeddings.embed
               FStar_Reflection_Embeddings.e_term_view
               t.FStar_Syntax_Syntax.pos uu____3463
              in
           let t1 =
             let uu____3467 =
               let uu____3476 = FStar_Syntax_Syntax.as_arg tv  in
               [uu____3476]  in
             FStar_Syntax_Util.mk_app
               (FStar_Reflection_Data.refl_constant_term
                  FStar_Reflection_Data.fstar_refl_pack_ln) uu____3467
              in
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____3478) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = FStar_SMTEncoding_Env.lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____3488 = head_redex env t  in
           if uu____3488
           then let uu____3493 = whnf env t  in encode_term uu____3493 env
           else
             (let uu____3495 =
                FStar_SMTEncoding_Env.lookup_free_var env
                  v1.FStar_Syntax_Syntax.fv_name
                 in
              (uu____3495, []))
       | FStar_Syntax_Syntax.Tm_type uu____3498 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3502) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.FStar_SMTEncoding_Env.current_module_name
              in
           let uu____3527 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____3527 with
            | (binders1,res) ->
                let uu____3538 =
                  (env.FStar_SMTEncoding_Env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____3538
                then
                  let uu____3543 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____3543 with
                   | (vars,guards,env',decls,uu____3568) ->
                       let fsym =
                         let uu____3586 =
                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                             "f"
                            in
                         (uu____3586, FStar_SMTEncoding_Term.Term_sort)  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____3589 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___75_3598 =
                              env.FStar_SMTEncoding_Env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___75_3598.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___75_3598.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___75_3598.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___75_3598.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___75_3598.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___75_3598.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___75_3598.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___75_3598.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___75_3598.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___75_3598.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___75_3598.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___75_3598.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___75_3598.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___75_3598.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___75_3598.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___75_3598.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___75_3598.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___75_3598.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___75_3598.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___75_3598.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___75_3598.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___75_3598.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___75_3598.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___75_3598.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___75_3598.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___75_3598.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___75_3598.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___75_3598.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___75_3598.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___75_3598.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___75_3598.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___75_3598.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___75_3598.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___75_3598.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___75_3598.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___75_3598.FStar_TypeChecker_Env.dep_graph)
                            }) res
                          in
                       (match uu____3589 with
                        | (pre_opt,res_t) ->
                            let uu____3609 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____3609 with
                             | (res_pred,decls') ->
                                 let uu____3620 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____3633 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____3633, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____3637 =
                                         encode_formula pre env'  in
                                       (match uu____3637 with
                                        | (guard,decls0) ->
                                            let uu____3650 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____3650, decls0))
                                    in
                                 (match uu____3620 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____3662 =
                                          let uu____3673 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____3673)  in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____3662
                                         in
                                      let cvars =
                                        let uu____3691 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____3691
                                          (FStar_List.filter
                                             (fun uu____3705  ->
                                                match uu____3705 with
                                                | (x,uu____3711) ->
                                                    x <>
                                                      (FStar_Pervasives_Native.fst
                                                         fsym)))
                                         in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp)
                                         in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey
                                         in
                                      let uu____3730 =
                                        FStar_Util.smap_try_find
                                          env.FStar_SMTEncoding_Env.cache
                                          tkey_hash
                                         in
                                      (match uu____3730 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____3738 =
                                             let uu____3739 =
                                               let uu____3746 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV)
                                                  in
                                               ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                                 uu____3746)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3739
                                              in
                                           (uu____3738,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (FStar_SMTEncoding_Env.use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____3766 =
                                               let uu____3767 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____3767
                                                in
                                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                               uu____3766
                                              in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars
                                              in
                                           let caption =
                                             let uu____3778 =
                                               FStar_Options.log_queries ()
                                                in
                                             if uu____3778
                                             then
                                               let uu____3781 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.FStar_SMTEncoding_Env.tcenv
                                                   t0
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____3781
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
                                             let uu____3789 =
                                               let uu____3796 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars
                                                  in
                                               (tsym, uu____3796)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3789
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
                                             let uu____3808 =
                                               let uu____3815 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind)
                                                  in
                                               (uu____3815,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name)
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3808
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
                                             let uu____3836 =
                                               let uu____3843 =
                                                 let uu____3844 =
                                                   let uu____3855 =
                                                     let uu____3856 =
                                                       let uu____3861 =
                                                         let uu____3862 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f
                                                            in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____3862
                                                          in
                                                       (f_has_t, uu____3861)
                                                        in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____3856
                                                      in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____3855)
                                                    in
                                                 mkForall_fuel uu____3844  in
                                               (uu____3843,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3836
                                              in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym
                                                in
                                             let uu____3885 =
                                               let uu____3892 =
                                                 let uu____3893 =
                                                   let uu____3904 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp)
                                                      in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____3904)
                                                    in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____3893
                                                  in
                                               (uu____3892,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3885
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
                                           ((let uu____3929 =
                                               FStar_SMTEncoding_Env.mk_cache_entry
                                                 env tsym cvar_sorts t_decls1
                                                in
                                             FStar_Util.smap_add
                                               env.FStar_SMTEncoding_Env.cache
                                               tkey_hash uu____3929);
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
                     let uu____3944 =
                       let uu____3951 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____3951,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____3944  in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)  in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym  in
                     let uu____3963 =
                       let uu____3970 =
                         let uu____3971 =
                           let uu____3982 =
                             let uu____3983 =
                               let uu____3988 =
                                 let uu____3989 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____3989
                                  in
                               (f_has_t, uu____3988)  in
                             FStar_SMTEncoding_Util.mkImp uu____3983  in
                           ([[f_has_t]], [fsym], uu____3982)  in
                         mkForall_fuel uu____3971  in
                       (uu____3970, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____3963  in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____4016 ->
           let uu____4023 =
             let uu____4028 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.Weak;
                 FStar_TypeChecker_Normalize.HNF;
                 FStar_TypeChecker_Normalize.EraseUniverses]
                 env.FStar_SMTEncoding_Env.tcenv t0
                in
             match uu____4028 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____4035;
                 FStar_Syntax_Syntax.vars = uu____4036;_} ->
                 let uu____4043 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____4043 with
                  | (b,f1) ->
                      let uu____4068 =
                        let uu____4069 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____4069  in
                      (uu____4068, f1))
             | uu____4078 -> failwith "impossible"  in
           (match uu____4023 with
            | (x,f) ->
                let uu____4089 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____4089 with
                 | (base_t,decls) ->
                     let uu____4100 =
                       FStar_SMTEncoding_Env.gen_term_var env x  in
                     (match uu____4100 with
                      | (x1,xtm,env') ->
                          let uu____4114 = encode_formula f env'  in
                          (match uu____4114 with
                           | (refinement,decls') ->
                               let uu____4125 =
                                 FStar_SMTEncoding_Env.fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____4125 with
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
                                      let uu____4141 =
                                        let uu____4144 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____4151 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____4144
                                          uu____4151
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____4141
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____4184  ->
                                              match uu____4184 with
                                              | (y,uu____4190) ->
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
                                      FStar_SMTEncoding_Util.mkForall
                                        ([], (ffv :: xfv :: cvars1),
                                          encoding)
                                       in
                                    let tkey_hash =
                                      FStar_SMTEncoding_Term.hash_of_term
                                        tkey
                                       in
                                    let uu____4223 =
                                      FStar_Util.smap_try_find
                                        env.FStar_SMTEncoding_Env.cache
                                        tkey_hash
                                       in
                                    (match uu____4223 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____4231 =
                                           let uu____4232 =
                                             let uu____4239 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV)
                                                in
                                             ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                               uu____4239)
                                              in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____4232
                                            in
                                         (uu____4231,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (FStar_SMTEncoding_Env.use_cache_entry
                                                    cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.FStar_SMTEncoding_Env.current_module_name
                                            in
                                         let tsym =
                                           let uu____4260 =
                                             let uu____4261 =
                                               let uu____4262 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____4262
                                                in
                                             Prims.strcat module_name
                                               uu____4261
                                              in
                                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                             uu____4260
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
                                           let uu____4276 =
                                             let uu____4283 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1
                                                in
                                             (tsym, uu____4283)  in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____4276
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
                                           let uu____4298 =
                                             let uu____4305 =
                                               let uu____4306 =
                                                 let uu____4317 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base)
                                                    in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____4317)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____4306
                                                in
                                             (uu____4305,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4298
                                            in
                                         let t_kinding =
                                           let uu____4335 =
                                             let uu____4342 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind)
                                                in
                                             (uu____4342,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4335
                                            in
                                         let t_interp =
                                           let uu____4360 =
                                             let uu____4367 =
                                               let uu____4368 =
                                                 let uu____4379 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding)
                                                    in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____4379)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____4368
                                                in
                                             let uu____4402 =
                                               let uu____4405 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____4405
                                                in
                                             (uu____4367, uu____4402,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4360
                                            in
                                         let t_decls1 =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1])
                                            in
                                         ((let uu____4412 =
                                             FStar_SMTEncoding_Env.mk_cache_entry
                                               env tsym cvar_sorts t_decls1
                                              in
                                           FStar_Util.smap_add
                                             env.FStar_SMTEncoding_Env.cache
                                             tkey_hash uu____4412);
                                          (t1, t_decls1))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____4442 = FStar_Syntax_Unionfind.uvar_id uv  in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____4442  in
           let uu____4443 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm  in
           (match uu____4443 with
            | (t_has_k,decls) ->
                let d =
                  let uu____4455 =
                    let uu____4462 =
                      let uu____4463 =
                        let uu____4464 =
                          let uu____4465 = FStar_Syntax_Unionfind.uvar_id uv
                             in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____4465
                           in
                        FStar_Util.format1 "uvar_typing_%s" uu____4464  in
                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                        uu____4463
                       in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____4462)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____4455  in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____4470 ->
           let uu____4485 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____4485 with
            | (head1,args_e) ->
                let uu____4526 =
                  let uu____4539 =
                    let uu____4540 = FStar_Syntax_Subst.compress head1  in
                    uu____4540.FStar_Syntax_Syntax.n  in
                  (uu____4539, args_e)  in
                (match uu____4526 with
                 | uu____4555 when head_redex env head1 ->
                     let uu____4568 = whnf env t  in
                     encode_term uu____4568 env
                 | uu____4569 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____4588 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____4602;
                       FStar_Syntax_Syntax.vars = uu____4603;_},uu____4604),uu____4605::
                    (v1,uu____4607)::(v2,uu____4609)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____4660 = encode_term v1 env  in
                     (match uu____4660 with
                      | (v11,decls1) ->
                          let uu____4671 = encode_term v2 env  in
                          (match uu____4671 with
                           | (v21,decls2) ->
                               let uu____4682 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21
                                  in
                               (uu____4682,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____4686::(v1,uu____4688)::(v2,uu____4690)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____4737 = encode_term v1 env  in
                     (match uu____4737 with
                      | (v11,decls1) ->
                          let uu____4748 = encode_term v2 env  in
                          (match uu____4748 with
                           | (v21,decls2) ->
                               let uu____4759 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21
                                  in
                               (uu____4759,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____4763)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____4789)::(rng,uu____4791)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____4826) ->
                     let e0 =
                       let uu____4844 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg
                         env.FStar_SMTEncoding_Env.tcenv head1 uu____4844
                        in
                     ((let uu____4852 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug
                              env.FStar_SMTEncoding_Env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____4852
                       then
                         let uu____4853 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____4853
                       else ());
                      (let e =
                         let uu____4858 =
                           let uu____4863 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____4864 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____4863
                             uu____4864
                            in
                         uu____4858 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____4873),(arg,uu____4875)::[]) -> encode_term arg env
                 | uu____4900 ->
                     let uu____4913 = encode_args args_e env  in
                     (match uu____4913 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____4970 = encode_term head1 env  in
                            match uu____4970 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____5034 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____5034 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____5112  ->
                                                 fun uu____5113  ->
                                                   match (uu____5112,
                                                           uu____5113)
                                                   with
                                                   | ((bv,uu____5135),
                                                      (a,uu____5137)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____5155 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____5155
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____5160 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm
                                             in
                                          (match uu____5160 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type
                                                  in
                                               let e_typing =
                                                 let uu____5175 =
                                                   let uu____5182 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____5191 =
                                                     let uu____5192 =
                                                       let uu____5193 =
                                                         let uu____5194 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm
                                                            in
                                                         FStar_Util.digest_of_string
                                                           uu____5194
                                                          in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____5193
                                                        in
                                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                       uu____5192
                                                      in
                                                   (uu____5182,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____5191)
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____5175
                                                  in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing])))))))
                             in
                          let encode_full_app fv =
                            let uu____5213 =
                              FStar_SMTEncoding_Env.lookup_free_var_sym env
                                fv
                               in
                            match uu____5213 with
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
                                   FStar_Syntax_Syntax.pos = uu____5245;
                                   FStar_Syntax_Syntax.vars = uu____5246;_},uu____5247)
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
                                   FStar_Syntax_Syntax.pos = uu____5258;
                                   FStar_Syntax_Syntax.vars = uu____5259;_},uu____5260)
                                ->
                                let uu____5265 =
                                  let uu____5266 =
                                    let uu____5271 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____5271
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____5266
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____5265
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____5301 =
                                  let uu____5302 =
                                    let uu____5307 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____5307
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____5302
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____5301
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____5336,(FStar_Util.Inl t1,uu____5338),uu____5339)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____5388,(FStar_Util.Inr c,uu____5390),uu____5391)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____5440 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____5467 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.Weak;
                                     FStar_TypeChecker_Normalize.HNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.FStar_SMTEncoding_Env.tcenv
                                     head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____5467
                                  in
                               let uu____5468 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____5468 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____5484;
                                            FStar_Syntax_Syntax.vars =
                                              uu____5485;_},uu____5486)
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
                                     | uu____5500 ->
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
           let uu____5549 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____5549 with
            | (bs1,body1,opening) ->
                let fallback uu____5574 =
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
                  let uu____5581 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort)
                     in
                  (uu____5581, [decl])  in
                let is_impure rc =
                  let uu____5590 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                      env.FStar_SMTEncoding_Env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____5590 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____5602 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_All.pipe_right uu____5602
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  let uu____5620 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                     in
                  if uu____5620
                  then
                    let uu____5623 = FStar_Syntax_Syntax.mk_Total res_typ  in
                    FStar_Pervasives_Native.Some uu____5623
                  else
                    (let uu____5625 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid
                        in
                     if uu____5625
                     then
                       let uu____5628 = FStar_Syntax_Syntax.mk_GTotal res_typ
                          in
                       FStar_Pervasives_Native.Some uu____5628
                     else FStar_Pervasives_Native.None)
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____5635 =
                         let uu____5640 =
                           let uu____5641 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____5641
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____5640)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____5635);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____5643 =
                       (is_impure rc) &&
                         (let uu____5645 =
                            FStar_TypeChecker_Env.is_reifiable
                              env.FStar_SMTEncoding_Env.tcenv rc
                             in
                          Prims.op_Negation uu____5645)
                        in
                     if uu____5643
                     then fallback ()
                     else
                       (let cache_size =
                          FStar_Util.smap_size
                            env.FStar_SMTEncoding_Env.cache
                           in
                        let uu____5652 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____5652 with
                        | (vars,guards,envbody,decls,uu____5677) ->
                            let body2 =
                              let uu____5691 =
                                FStar_TypeChecker_Env.is_reifiable
                                  env.FStar_SMTEncoding_Env.tcenv rc
                                 in
                              if uu____5691
                              then
                                FStar_TypeChecker_Util.reify_body
                                  env.FStar_SMTEncoding_Env.tcenv body1
                              else body1  in
                            let uu____5693 = encode_term body2 envbody  in
                            (match uu____5693 with
                             | (body3,decls') ->
                                 let uu____5704 =
                                   let uu____5713 = codomain_eff rc  in
                                   match uu____5713 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____5732 = encode_term tfun env
                                          in
                                       (match uu____5732 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____5704 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____5764 =
                                          let uu____5775 =
                                            let uu____5776 =
                                              let uu____5781 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____5781, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____5776
                                             in
                                          ([], vars, uu____5775)  in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____5764
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
                                            let uu____5793 =
                                              let uu____5796 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1
                                                 in
                                              FStar_List.append uu____5796
                                                cvars
                                               in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____5793
                                         in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body)
                                         in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey
                                         in
                                      let uu____5815 =
                                        FStar_Util.smap_try_find
                                          env.FStar_SMTEncoding_Env.cache
                                          tkey_hash
                                         in
                                      (match uu____5815 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____5823 =
                                             let uu____5824 =
                                               let uu____5831 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1
                                                  in
                                               ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                                 uu____5831)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____5824
                                              in
                                           (uu____5823,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (FStar_SMTEncoding_Env.use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____5842 =
                                             is_an_eta_expansion env vars
                                               body3
                                              in
                                           (match uu____5842 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____5853 =
                                                    let uu____5854 =
                                                      FStar_Util.smap_size
                                                        env.FStar_SMTEncoding_Env.cache
                                                       in
                                                    uu____5854 = cache_size
                                                     in
                                                  if uu____5853
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
                                                    let uu____5870 =
                                                      let uu____5871 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash
                                                         in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____5871
                                                       in
                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                      uu____5870
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
                                                  let uu____5878 =
                                                    let uu____5885 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    (fsym, uu____5885)  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____5878
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
                                                      let uu____5903 =
                                                        let uu____5904 =
                                                          let uu____5911 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t)
                                                             in
                                                          (uu____5911,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name)
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____5904
                                                         in
                                                      [uu____5903]
                                                   in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym
                                                     in
                                                  let uu____5924 =
                                                    let uu____5931 =
                                                      let uu____5932 =
                                                        let uu____5943 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3)
                                                           in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____5943)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____5932
                                                       in
                                                    (uu____5931,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____5924
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
                                                ((let uu____5960 =
                                                    FStar_SMTEncoding_Env.mk_cache_entry
                                                      env fsym cvar_sorts
                                                      f_decls
                                                     in
                                                  FStar_Util.smap_add
                                                    env.FStar_SMTEncoding_Env.cache
                                                    tkey_hash uu____5960);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____5963,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____5964;
                          FStar_Syntax_Syntax.lbunivs = uu____5965;
                          FStar_Syntax_Syntax.lbtyp = uu____5966;
                          FStar_Syntax_Syntax.lbeff = uu____5967;
                          FStar_Syntax_Syntax.lbdef = uu____5968;
                          FStar_Syntax_Syntax.lbattrs = uu____5969;
                          FStar_Syntax_Syntax.lbpos = uu____5970;_}::uu____5971),uu____5972)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____6002;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____6004;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____6006;
                FStar_Syntax_Syntax.lbpos = uu____6007;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____6031 ->
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
              let uu____6101 =
                let uu____6106 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____6106 env  in
              match uu____6101 with
              | (ee1,decls1) ->
                  let uu____6127 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____6127 with
                   | (xs,e21) ->
                       let uu____6152 = FStar_List.hd xs  in
                       (match uu____6152 with
                        | (x1,uu____6166) ->
                            let env' =
                              FStar_SMTEncoding_Env.push_term_var env x1 ee1
                               in
                            let uu____6168 = encode_body e21 env'  in
                            (match uu____6168 with
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
            let uu____6200 =
              let uu____6207 =
                let uu____6208 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____6208  in
              FStar_SMTEncoding_Env.gen_term_var env uu____6207  in
            match uu____6200 with
            | (scrsym,scr',env1) ->
                let uu____6216 = encode_term e env1  in
                (match uu____6216 with
                 | (scr,decls) ->
                     let uu____6227 =
                       let encode_branch b uu____6256 =
                         match uu____6256 with
                         | (else_case,decls1) ->
                             let uu____6275 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____6275 with
                              | (p,w,br) ->
                                  let uu____6301 = encode_pat env1 p  in
                                  (match uu____6301 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____6338  ->
                                                   match uu____6338 with
                                                   | (x,t) ->
                                                       FStar_SMTEncoding_Env.push_term_var
                                                         env2 x t) env1)
                                          in
                                       let uu____6345 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____6367 =
                                               encode_term w1 env2  in
                                             (match uu____6367 with
                                              | (w2,decls2) ->
                                                  let uu____6380 =
                                                    let uu____6381 =
                                                      let uu____6386 =
                                                        let uu____6387 =
                                                          let uu____6392 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____6392)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____6387
                                                         in
                                                      (guard, uu____6386)  in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____6381
                                                     in
                                                  (uu____6380, decls2))
                                          in
                                       (match uu____6345 with
                                        | (guard1,decls2) ->
                                            let uu____6405 =
                                              encode_br br env2  in
                                            (match uu____6405 with
                                             | (br1,decls3) ->
                                                 let uu____6418 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____6418,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____6227 with
                      | (match_tm,decls1) ->
                          let uu____6437 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange
                             in
                          (uu____6437, decls1)))

and (encode_pat :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.pat ->
      (FStar_SMTEncoding_Env.env_t,pattern) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun pat  ->
      (let uu____6477 =
         FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
           FStar_Options.Low
          in
       if uu____6477
       then
         let uu____6478 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____6478
       else ());
      (let uu____6480 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____6480 with
       | (vars,pat_term) ->
           let uu____6497 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____6550  ->
                     fun v1  ->
                       match uu____6550 with
                       | (env1,vars1) ->
                           let uu____6602 =
                             FStar_SMTEncoding_Env.gen_term_var env1 v1  in
                           (match uu____6602 with
                            | (xx,uu____6624,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, []))
              in
           (match uu____6497 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____6707 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____6708 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____6709 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____6717 = encode_const c env1  in
                      (match uu____6717 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____6731::uu____6732 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____6735 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon
                            env1.FStar_SMTEncoding_Env.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____6758 =
                          FStar_TypeChecker_Env.datacons_of_typ
                            env1.FStar_SMTEncoding_Env.tcenv tc_name
                           in
                        match uu____6758 with
                        | (uu____6765,uu____6766::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____6769 ->
                            FStar_SMTEncoding_Env.mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____6802  ->
                                  match uu____6802 with
                                  | (arg,uu____6810) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____6816 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____6816))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____6847) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____6878 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____6901 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____6945  ->
                                  match uu____6945 with
                                  | (arg,uu____6959) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____6965 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____6965))
                         in
                      FStar_All.pipe_right uu____6901 FStar_List.flatten
                   in
                let pat_term1 uu____6995 = encode_term pat_term env1  in
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
      let uu____7005 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____7043  ->
                fun uu____7044  ->
                  match (uu____7043, uu____7044) with
                  | ((tms,decls),(t,uu____7080)) ->
                      let uu____7101 = encode_term t env  in
                      (match uu____7101 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____7005 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____7160 = FStar_Syntax_Util.list_elements e  in
        match uu____7160 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____7183 =
          let uu____7198 = FStar_Syntax_Util.unmeta p  in
          FStar_All.pipe_right uu____7198 FStar_Syntax_Util.head_and_args  in
        match uu____7183 with
        | (head1,args) ->
            let uu____7237 =
              let uu____7250 =
                let uu____7251 = FStar_Syntax_Util.un_uinst head1  in
                uu____7251.FStar_Syntax_Syntax.n  in
              (uu____7250, args)  in
            (match uu____7237 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____7265,uu____7266)::(e,uu____7268)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____7303 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or t1 =
          let uu____7343 =
            let uu____7358 = FStar_Syntax_Util.unmeta t1  in
            FStar_All.pipe_right uu____7358 FStar_Syntax_Util.head_and_args
             in
          match uu____7343 with
          | (head1,args) ->
              let uu____7399 =
                let uu____7412 =
                  let uu____7413 = FStar_Syntax_Util.un_uinst head1  in
                  uu____7413.FStar_Syntax_Syntax.n  in
                (uu____7412, args)  in
              (match uu____7399 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____7430)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____7457 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____7479 = smt_pat_or t1  in
            (match uu____7479 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____7495 = list_elements1 e  in
                 FStar_All.pipe_right uu____7495
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____7513 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____7513
                           (FStar_List.map one_pat)))
             | uu____7524 ->
                 let uu____7529 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____7529])
        | uu____7550 ->
            let uu____7553 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____7553]
         in
      let uu____7574 =
        let uu____7593 =
          let uu____7594 = FStar_Syntax_Subst.compress t  in
          uu____7594.FStar_Syntax_Syntax.n  in
        match uu____7593 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____7633 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____7633 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____7676;
                        FStar_Syntax_Syntax.effect_name = uu____7677;
                        FStar_Syntax_Syntax.result_typ = uu____7678;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____7680)::(post,uu____7682)::(pats,uu____7684)::[];
                        FStar_Syntax_Syntax.flags = uu____7685;_}
                      ->
                      let uu____7726 = lemma_pats pats  in
                      (binders1, pre, post, uu____7726)
                  | uu____7743 -> failwith "impos"))
        | uu____7762 -> failwith "Impos"  in
      match uu____7574 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___76_7810 = env  in
            {
              FStar_SMTEncoding_Env.bindings =
                (uu___76_7810.FStar_SMTEncoding_Env.bindings);
              FStar_SMTEncoding_Env.depth =
                (uu___76_7810.FStar_SMTEncoding_Env.depth);
              FStar_SMTEncoding_Env.tcenv =
                (uu___76_7810.FStar_SMTEncoding_Env.tcenv);
              FStar_SMTEncoding_Env.warn =
                (uu___76_7810.FStar_SMTEncoding_Env.warn);
              FStar_SMTEncoding_Env.cache =
                (uu___76_7810.FStar_SMTEncoding_Env.cache);
              FStar_SMTEncoding_Env.nolabels =
                (uu___76_7810.FStar_SMTEncoding_Env.nolabels);
              FStar_SMTEncoding_Env.use_zfuel_name = true;
              FStar_SMTEncoding_Env.encode_non_total_function_typ =
                (uu___76_7810.FStar_SMTEncoding_Env.encode_non_total_function_typ);
              FStar_SMTEncoding_Env.current_module_name =
                (uu___76_7810.FStar_SMTEncoding_Env.current_module_name)
            }  in
          let uu____7811 =
            encode_binders FStar_Pervasives_Native.None binders env1  in
          (match uu____7811 with
           | (vars,guards,env2,decls,uu____7836) ->
               let uu____7849 =
                 let uu____7864 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____7918 =
                             let uu____7929 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_smt_pattern t1 env2))
                                in
                             FStar_All.pipe_right uu____7929 FStar_List.unzip
                              in
                           match uu____7918 with
                           | (pats,decls1) -> (pats, decls1)))
                    in
                 FStar_All.pipe_right uu____7864 FStar_List.unzip  in
               (match uu____7849 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls'  in
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
                    let env3 =
                      let uu___77_8081 = env2  in
                      {
                        FStar_SMTEncoding_Env.bindings =
                          (uu___77_8081.FStar_SMTEncoding_Env.bindings);
                        FStar_SMTEncoding_Env.depth =
                          (uu___77_8081.FStar_SMTEncoding_Env.depth);
                        FStar_SMTEncoding_Env.tcenv =
                          (uu___77_8081.FStar_SMTEncoding_Env.tcenv);
                        FStar_SMTEncoding_Env.warn =
                          (uu___77_8081.FStar_SMTEncoding_Env.warn);
                        FStar_SMTEncoding_Env.cache =
                          (uu___77_8081.FStar_SMTEncoding_Env.cache);
                        FStar_SMTEncoding_Env.nolabels = true;
                        FStar_SMTEncoding_Env.use_zfuel_name =
                          (uu___77_8081.FStar_SMTEncoding_Env.use_zfuel_name);
                        FStar_SMTEncoding_Env.encode_non_total_function_typ =
                          (uu___77_8081.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                        FStar_SMTEncoding_Env.current_module_name =
                          (uu___77_8081.FStar_SMTEncoding_Env.current_module_name)
                      }  in
                    let uu____8082 =
                      let uu____8087 = FStar_Syntax_Util.unmeta pre  in
                      encode_formula uu____8087 env3  in
                    (match uu____8082 with
                     | (pre1,decls'') ->
                         let uu____8094 =
                           let uu____8099 = FStar_Syntax_Util.unmeta post1
                              in
                           encode_formula uu____8099 env3  in
                         (match uu____8094 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls'''))
                                 in
                              let uu____8109 =
                                let uu____8110 =
                                  let uu____8121 =
                                    let uu____8122 =
                                      let uu____8127 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards)
                                         in
                                      (uu____8127, post2)  in
                                    FStar_SMTEncoding_Util.mkImp uu____8122
                                     in
                                  (pats, vars, uu____8121)  in
                                FStar_SMTEncoding_Util.mkForall uu____8110
                                 in
                              (uu____8109, decls1)))))

and (encode_smt_pattern :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.pat,FStar_SMTEncoding_Term.decl Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let uu____8140 = FStar_Syntax_Util.head_and_args t  in
      match uu____8140 with
      | (head1,args) ->
          let head2 = FStar_Syntax_Util.un_uinst head1  in
          (match ((head2.FStar_Syntax_Syntax.n), args) with
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,uu____8199::(x,uu____8201)::(t1,uu____8203)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.has_type_lid
               ->
               let uu____8250 = encode_term x env  in
               (match uu____8250 with
                | (x1,decls) ->
                    let uu____8263 = encode_term t1 env  in
                    (match uu____8263 with
                     | (t2,decls') ->
                         let uu____8276 =
                           FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                         (uu____8276, (FStar_List.append decls decls'))))
           | uu____8279 -> encode_term t env)

and (encode_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____8304 =
          FStar_All.pipe_left
            (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____8304
        then
          let uu____8305 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____8306 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____8305 uu____8306
        else ()  in
      let enc f r l =
        let uu____8345 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____8373 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____8373 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____8345 with
        | (decls,args) ->
            let uu____8402 =
              let uu___78_8403 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___78_8403.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___78_8403.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____8402, decls)
         in
      let const_op f r uu____8440 = let uu____8453 = f r  in (uu____8453, [])
         in
      let un_op f l =
        let uu____8476 = FStar_List.hd l  in FStar_All.pipe_left f uu____8476
         in
      let bin_op f uu___72_8496 =
        match uu___72_8496 with
        | t1::t2::[] -> f (t1, t2)
        | uu____8507 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____8547 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____8570  ->
                 match uu____8570 with
                 | (t,uu____8584) ->
                     let uu____8585 = encode_formula t env  in
                     (match uu____8585 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____8547 with
        | (decls,phis) ->
            let uu____8614 =
              let uu___79_8615 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___79_8615.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___79_8615.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____8614, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____8680  ->
               match uu____8680 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____8699) -> false
                    | uu____8700 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____8715 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____8715
        else
          (let uu____8729 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____8729 r rf)
         in
      let mk_imp1 r uu___73_8764 =
        match uu___73_8764 with
        | (lhs,uu____8770)::(rhs,uu____8772)::[] ->
            let uu____8799 = encode_formula rhs env  in
            (match uu____8799 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____8814) ->
                      (l1, decls1)
                  | uu____8819 ->
                      let uu____8820 = encode_formula lhs env  in
                      (match uu____8820 with
                       | (l2,decls2) ->
                           let uu____8831 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____8831, (FStar_List.append decls1 decls2)))))
        | uu____8834 -> failwith "impossible"  in
      let mk_ite r uu___74_8861 =
        match uu___74_8861 with
        | (guard,uu____8867)::(_then,uu____8869)::(_else,uu____8871)::[] ->
            let uu____8908 = encode_formula guard env  in
            (match uu____8908 with
             | (g,decls1) ->
                 let uu____8919 = encode_formula _then env  in
                 (match uu____8919 with
                  | (t,decls2) ->
                      let uu____8930 = encode_formula _else env  in
                      (match uu____8930 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____8944 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____8973 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l  in
        f uu____8973  in
      let connectives =
        let uu____8993 =
          let uu____9008 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____9008)  in
        let uu____9031 =
          let uu____9048 =
            let uu____9063 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____9063)  in
          let uu____9086 =
            let uu____9103 =
              let uu____9121 =
                let uu____9136 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____9136)  in
              let uu____9159 =
                let uu____9176 =
                  let uu____9194 =
                    let uu____9209 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____9209)  in
                  [uu____9194;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____9176  in
              uu____9121 :: uu____9159  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____9103  in
          uu____9048 :: uu____9086  in
        uu____8993 :: uu____9031  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____9576 = encode_formula phi' env  in
            (match uu____9576 with
             | (phi2,decls) ->
                 let uu____9587 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____9587, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____9588 ->
            let uu____9595 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____9595 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____9634 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____9634 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____9646;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____9648;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____9650;
                 FStar_Syntax_Syntax.lbpos = uu____9651;_}::[]),e2)
            ->
            let uu____9675 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____9675 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____9722::(x,uu____9724)::(t,uu____9726)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____9773 = encode_term x env  in
                 (match uu____9773 with
                  | (x1,decls) ->
                      let uu____9784 = encode_term t env  in
                      (match uu____9784 with
                       | (t1,decls') ->
                           let uu____9795 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____9795, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____9800)::(msg,uu____9802)::(phi2,uu____9804)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____9849 =
                   let uu____9854 =
                     let uu____9855 = FStar_Syntax_Subst.compress r  in
                     uu____9855.FStar_Syntax_Syntax.n  in
                   let uu____9858 =
                     let uu____9859 = FStar_Syntax_Subst.compress msg  in
                     uu____9859.FStar_Syntax_Syntax.n  in
                   (uu____9854, uu____9858)  in
                 (match uu____9849 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____9868))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____9874 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____9881)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____9906 when head_redex env head2 ->
                 let uu____9919 = whnf env phi1  in
                 encode_formula uu____9919 env
             | uu____9920 ->
                 let uu____9933 = encode_term phi1 env  in
                 (match uu____9933 with
                  | (tt,decls) ->
                      let uu____9944 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___80_9947 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___80_9947.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___80_9947.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      (uu____9944, decls)))
        | uu____9948 ->
            let uu____9949 = encode_term phi1 env  in
            (match uu____9949 with
             | (tt,decls) ->
                 let uu____9960 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___81_9963 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___81_9963.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___81_9963.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 (uu____9960, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____10007 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____10007 with
        | (vars,guards,env2,decls,uu____10046) ->
            let uu____10059 =
              let uu____10072 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____10124 =
                          let uu____10135 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____10175  ->
                                    match uu____10175 with
                                    | (t,uu____10189) ->
                                        encode_smt_pattern t
                                          (let uu___82_10195 = env2  in
                                           {
                                             FStar_SMTEncoding_Env.bindings =
                                               (uu___82_10195.FStar_SMTEncoding_Env.bindings);
                                             FStar_SMTEncoding_Env.depth =
                                               (uu___82_10195.FStar_SMTEncoding_Env.depth);
                                             FStar_SMTEncoding_Env.tcenv =
                                               (uu___82_10195.FStar_SMTEncoding_Env.tcenv);
                                             FStar_SMTEncoding_Env.warn =
                                               (uu___82_10195.FStar_SMTEncoding_Env.warn);
                                             FStar_SMTEncoding_Env.cache =
                                               (uu___82_10195.FStar_SMTEncoding_Env.cache);
                                             FStar_SMTEncoding_Env.nolabels =
                                               (uu___82_10195.FStar_SMTEncoding_Env.nolabels);
                                             FStar_SMTEncoding_Env.use_zfuel_name
                                               = true;
                                             FStar_SMTEncoding_Env.encode_non_total_function_typ
                                               =
                                               (uu___82_10195.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                             FStar_SMTEncoding_Env.current_module_name
                                               =
                                               (uu___82_10195.FStar_SMTEncoding_Env.current_module_name)
                                           })))
                             in
                          FStar_All.pipe_right uu____10135 FStar_List.unzip
                           in
                        match uu____10124 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1))))
                 in
              FStar_All.pipe_right uu____10072 FStar_List.unzip  in
            (match uu____10059 with
             | (pats,decls') ->
                 let uu____10304 = encode_formula body env2  in
                 (match uu____10304 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____10336;
                             FStar_SMTEncoding_Term.rng = uu____10337;_}::[])::[]
                            when
                            let uu____10352 =
                              FStar_Ident.text_of_lid
                                FStar_Parser_Const.guard_free
                               in
                            uu____10352 = gf -> []
                        | uu____10353 -> guards  in
                      let uu____10358 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____10358, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls'')))))
         in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi  in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____10422  ->
                   match uu____10422 with
                   | (x,uu____10428) ->
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
               let uu____10436 = FStar_Syntax_Free.names hd1  in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____10448 = FStar_Syntax_Free.names x  in
                      FStar_Util.set_union out uu____10448) uu____10436 tl1
                in
             let uu____10451 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____10478  ->
                       match uu____10478 with
                       | (b,uu____10484) ->
                           let uu____10485 = FStar_Util.set_mem b pat_vars
                              in
                           Prims.op_Negation uu____10485))
                in
             (match uu____10451 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____10491) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1
                     in
                  let uu____10505 =
                    let uu____10510 =
                      let uu____10511 = FStar_Syntax_Print.bv_to_string x  in
                      FStar_Util.format1
                        "SMT pattern misses at least one bound variable: %s"
                        uu____10511
                       in
                    (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                      uu____10510)
                     in
                  FStar_Errors.log_issue pos uu____10505)
          in
       let uu____10512 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____10512 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____10521 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____10587  ->
                     match uu____10587 with
                     | (l,uu____10601) -> FStar_Ident.lid_equals op l))
              in
           (match uu____10521 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____10640,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____10686 = encode_q_body env vars pats body  in
             match uu____10686 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____10731 =
                     let uu____10742 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____10742)  in
                   FStar_SMTEncoding_Term.mkForall uu____10731
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____10761 = encode_q_body env vars pats body  in
             match uu____10761 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____10805 =
                   let uu____10806 =
                     let uu____10817 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____10817)  in
                   FStar_SMTEncoding_Term.mkExists uu____10806
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (uu____10805, decls))))
