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
  fun mname  ->
    fun r  ->
      fun n1  ->
        fun uu____54  ->
          match uu____54 with
          | (pats,vars,body) ->
              let fallback uu____103 =
                FStar_SMTEncoding_Term.mkForall r (pats, vars, body)  in
              let uu____114 = FStar_Options.unthrottle_inductives ()  in
              if uu____114
              then fallback ()
              else
                (let uu____122 =
                   FStar_SMTEncoding_Env.fresh_fvar mname "f"
                     FStar_SMTEncoding_Term.Fuel_sort
                    in
                 match uu____122 with
                 | (fsym,fterm) ->
                     let add_fuel1 tms =
                       FStar_All.pipe_right tms
                         (FStar_List.map
                            (fun p  ->
                               match p.FStar_SMTEncoding_Term.tm with
                               | FStar_SMTEncoding_Term.App
                                   (FStar_SMTEncoding_Term.Var
                                    "HasType",args)
                                   ->
                                   FStar_SMTEncoding_Util.mkApp
                                     ("HasTypeFuel", (fterm :: args))
                               | uu____213 -> p))
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
                                 let uu____285 = add_fuel1 guards  in
                                 FStar_SMTEncoding_Util.mk_and_l uu____285
                             | uu____291 ->
                                 let uu____292 = add_fuel1 [guard]  in
                                 FStar_All.pipe_right uu____292 FStar_List.hd
                              in
                           FStar_SMTEncoding_Util.mkImp (guard1, body')
                       | uu____321 -> body  in
                     let vars1 =
                       let uu____333 =
                         FStar_SMTEncoding_Term.mk_fv
                           (fsym, FStar_SMTEncoding_Term.Fuel_sort)
                          in
                       uu____333 :: vars  in
                     FStar_SMTEncoding_Term.mkForall r (pats1, vars1, body1))
  
let (mkForall_fuel :
  Prims.string ->
    FStar_Range.range ->
      (FStar_SMTEncoding_Term.pat Prims.list Prims.list *
        FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term) ->
        FStar_SMTEncoding_Term.term)
  = fun mname  -> fun r  -> mkForall_fuel' mname r (Prims.parse_int "1") 
let (head_normal :
  FStar_SMTEncoding_Env.env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow uu____450 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____475 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____492 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____499 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____521 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____557 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____563 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only true]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____563 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____599;
             FStar_Syntax_Syntax.vars = uu____600;_},uu____601)
          ->
          let uu____645 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only true]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____645 FStar_Option.isNone
      | uu____680 -> false
  
let (head_redex :
  FStar_SMTEncoding_Env.env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____724 =
        let uu____725 = FStar_Syntax_Util.un_uinst t  in
        uu____725.FStar_Syntax_Syntax.n  in
      match uu____724 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____737,uu____738,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___0_802  ->
                  match uu___0_802 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____805 -> false) rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____811 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only true]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____811 FStar_Option.isSome
      | uu____846 -> false
  
let (whnf :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____893 = head_normal env t  in
      if uu____893
      then t
      else
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Weak;
          FStar_TypeChecker_Env.HNF;
          FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
          FStar_TypeChecker_Env.Eager_unfolding true;
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
        FStar_TypeChecker_Env.Eager_unfolding true;
        FStar_TypeChecker_Env.EraseUniverses] env.FStar_SMTEncoding_Env.tcenv
        t
  
let (trivial_post : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____971 =
      let uu____972 = FStar_Syntax_Syntax.null_binder t  in [uu____972]  in
    let uu____1006 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    FStar_Syntax_Util.abs uu____971 uu____1006 FStar_Pervasives_Native.None
  
let (mk_Apply :
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.fvs -> FStar_SMTEncoding_Term.term)
  =
  fun e  ->
    fun vars  ->
      FStar_All.pipe_right vars
        (FStar_List.fold_left
           (fun out  ->
              fun var  ->
                let uu____1061 = FStar_SMTEncoding_Term.fv_sort var  in
                match uu____1061 with
                | FStar_SMTEncoding_Term.Fuel_sort  ->
                    let uu____1065 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____1065
                | s ->
                    let uu____1074 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____1074) e)
  
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
          let uu____1163 =
            let uu____1169 =
              let uu____1171 = FStar_Util.string_of_int arity  in
              let uu____1173 = FStar_Util.string_of_int n_args  in
              FStar_Util.format3
                "Head symbol %s expects at least %s arguments; got only %s"
                head1 uu____1171 uu____1173
               in
            (FStar_Errors.Fatal_SMTEncodingArityMismatch, uu____1169)  in
          FStar_Errors.raise_error uu____1163 rng
  
let (maybe_curry_app :
  FStar_Range.range ->
    (FStar_SMTEncoding_Term.op,FStar_SMTEncoding_Term.term) FStar_Util.either
      ->
      Prims.int ->
        FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term)
  =
  fun rng  ->
    fun head1  ->
      fun arity  ->
        fun args  ->
          let n_args = FStar_List.length args  in
          match head1 with
          | FStar_Util.Inr head2 -> mk_Apply_args head2 args
          | FStar_Util.Inl head2 ->
              if n_args = arity
              then FStar_SMTEncoding_Util.mkApp' (head2, args)
              else
                if n_args > arity
                then
                  (let uu____1264 = FStar_Util.first_N arity args  in
                   match uu____1264 with
                   | (args1,rest) ->
                       let head3 =
                         FStar_SMTEncoding_Util.mkApp' (head2, args1)  in
                       mk_Apply_args head3 rest)
                else
                  (let uu____1321 = FStar_SMTEncoding_Term.op_to_string head2
                      in
                   raise_arity_mismatch uu____1321 arity n_args rng)
  
let (maybe_curry_fvb :
  FStar_Range.range ->
    FStar_SMTEncoding_Env.fvar_binding ->
      FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term)
  =
  fun rng  ->
    fun fvb  ->
      fun args  ->
        if fvb.FStar_SMTEncoding_Env.fvb_thunked
        then
          let uu____1379 = FStar_SMTEncoding_Env.force_thunk fvb  in
          mk_Apply_args uu____1379 args
        else
          maybe_curry_app rng
            (FStar_Util.Inl
               (FStar_SMTEncoding_Term.Var (fvb.FStar_SMTEncoding_Env.smt_id)))
            fvb.FStar_SMTEncoding_Env.smt_arity args
  
let (is_app : FStar_SMTEncoding_Term.op -> Prims.bool) =
  fun uu___1_1397  ->
    match uu___1_1397 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____1403 -> false
  
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
                       FStar_SMTEncoding_Term.freevars = uu____1494;
                       FStar_SMTEncoding_Term.rng = uu____1495;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____1541) ->
              let uu____1557 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____1583 -> false) args (FStar_List.rev xs))
                 in
              if uu____1557
              then FStar_SMTEncoding_Env.tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____1596,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t  in
              let uu____1600 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____1608 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars
                           in
                        Prims.op_Negation uu____1608))
                 in
              if uu____1600
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____1624 -> FStar_Pervasives_Native.None  in
        check_partial_applications body (FStar_List.rev vars)
  
let check_pattern_vars :
  'Auu____1645 'Auu____1646 .
    FStar_SMTEncoding_Env.env_t ->
      (FStar_Syntax_Syntax.bv * 'Auu____1645) Prims.list ->
        (FStar_Syntax_Syntax.term * 'Auu____1646) Prims.list -> unit
  =
  fun env  ->
    fun vars  ->
      fun pats  ->
        let pats1 =
          FStar_All.pipe_right pats
            (FStar_List.map
               (fun uu____1764  ->
                  match uu____1764 with
                  | (x,uu____1778) ->
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
              let uu____1815 = FStar_Syntax_Free.names hd1  in
              FStar_List.fold_left
                (fun out  ->
                   fun x  ->
                     let uu____1850 = FStar_Syntax_Free.names x  in
                     FStar_Util.set_union out uu____1850) uu____1815 tl1
               in
            let uu____1863 =
              FStar_All.pipe_right vars
                (FStar_Util.find_opt
                   (fun uu____1910  ->
                      match uu____1910 with
                      | (b,uu____1922) ->
                          let uu____1933 = FStar_Util.set_mem b pat_vars  in
                          Prims.op_Negation uu____1933))
               in
            (match uu____1863 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some (x,uu____1950) ->
                 let pos =
                   FStar_List.fold_left
                     (fun out  ->
                        fun t  ->
                          FStar_Range.union_ranges out
                            t.FStar_Syntax_Syntax.pos)
                     hd1.FStar_Syntax_Syntax.pos tl1
                    in
                 let uu____1987 =
                   let uu____1993 =
                     let uu____1995 = FStar_Syntax_Print.bv_to_string x  in
                     FStar_Util.format1
                       "SMT pattern misses at least one bound variable: %s"
                       uu____1995
                      in
                   (FStar_Errors.Warning_SMTPatternIllFormed, uu____1993)  in
                 FStar_Errors.log_issue pos uu____1987)
  
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
  fun projectee  ->
    match projectee with
    | { pat_vars; pat_term; guard; projections;_} -> pat_vars
  
let (__proj__Mkpattern__item__pat_term :
  pattern ->
    unit -> (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun projectee  ->
    match projectee with
    | { pat_vars; pat_term; guard; projections;_} -> pat_term
  
let (__proj__Mkpattern__item__guard :
  pattern -> FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term) =
  fun projectee  ->
    match projectee with
    | { pat_vars; pat_term; guard; projections;_} -> guard
  
let (__proj__Mkpattern__item__projections :
  pattern ->
    FStar_SMTEncoding_Term.term ->
      (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { pat_vars; pat_term; guard; projections;_} -> projections
  
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
        | FStar_Syntax_Syntax.Tm_arrow uu____2558 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____2582 ->
            let uu____2598 = FStar_Syntax_Util.unrefine t1  in
            aux true uu____2598
        | uu____2608 ->
            if norm1
            then let uu____2614 = whnf env t1  in aux false uu____2614
            else
              (let uu____2626 =
                 let uu____2628 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let uu____2630 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____2628 uu____2630
                  in
               failwith uu____2626)
         in
      aux true t0
  
let rec (curried_arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp))
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k  in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        FStar_Syntax_Subst.open_comp bs c
    | FStar_Syntax_Syntax.Tm_refine (bv,uu____2718) ->
        let uu____2741 =
          curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort  in
        (match uu____2741 with
         | (args,res) ->
             (match args with
              | [] ->
                  let uu____2787 = FStar_Syntax_Syntax.mk_Total k1  in
                  ([], uu____2787)
              | uu____2811 -> (args, res)))
    | uu____2816 ->
        let uu____2817 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____2817)
  
let is_arithmetic_primitive :
  'Auu____2848 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____2848 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2879::uu____2880::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2887::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____2893 -> false
  
let (isInteger : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____2924 -> false
  
let (getInteger : FStar_Syntax_Syntax.term' -> Prims.int) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____2947 -> failwith "Expected an Integer term"
  
let is_BitVector_primitive :
  'Auu____2957 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____2957)
        Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____3019)::uu____3020::uu____3021::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____3111)::uu____3112::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____3180 -> false
  
let rec (encode_const :
  FStar_Const.sconst ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun c  ->
    fun env  ->
      match c with
      | FStar_Const.Const_unit  -> (FStar_SMTEncoding_Term.mk_Term_unit, [])
      | FStar_Const.Const_bool (true ) ->
          let uu____3882 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue  in
          (uu____3882, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____3897 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse  in
          (uu____3897, [])
      | FStar_Const.Const_char c1 ->
          let uu____3913 =
            let uu____3920 =
              let uu____3931 =
                let uu____3937 =
                  let uu____3944 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1)
                     in
                  FStar_SMTEncoding_Term.boxInt uu____3944  in
                [uu____3937]  in
              ("FStar.Char.__char_of_int", uu____3931)  in
            FStar_SMTEncoding_Util.mkApp uu____3920  in
          (uu____3913, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____3984 =
            let uu____3991 = FStar_SMTEncoding_Util.mkInteger i  in
            FStar_SMTEncoding_Term.boxInt uu____3991  in
          (uu____3984, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.FStar_SMTEncoding_Env.tcenv).FStar_TypeChecker_Env.dsenv
              repr sw FStar_Range.dummyRange
             in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____4033) ->
          let uu____4036 =
            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.string_const s
             in
          (uu____4036, [])
      | FStar_Const.Const_range uu____4050 ->
          let uu____4051 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          (uu____4051, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | FStar_Const.Const_real r ->
          let uu____4074 =
            let uu____4081 = FStar_SMTEncoding_Util.mkReal r  in
            FStar_SMTEncoding_Term.boxReal uu____4081  in
          (uu____4074, [])
      | c1 ->
          let uu____4096 =
            let uu____4098 = FStar_Syntax_Print.const_to_string c1  in
            FStar_Util.format1 "Unhandled constant: %s" uu____4098  in
          failwith uu____4096

and (encode_binders :
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.binders ->
      FStar_SMTEncoding_Env.env_t ->
        (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term
          Prims.list * FStar_SMTEncoding_Env.env_t *
          FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list))
  =
  fun fuel_opt  ->
    fun bs  ->
      fun env  ->
        (let uu____4163 =
           FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
             FStar_Options.Medium
            in
         if uu____4163
         then
           let uu____4166 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____4166
         else ());
        (let uu____4172 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____4333  ->
                   fun b  ->
                     match uu____4333 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____4495 =
                           let x = FStar_Pervasives_Native.fst b  in
                           let uu____4549 =
                             FStar_SMTEncoding_Env.gen_term_var env1 x  in
                           match uu____4549 with
                           | (xxsym,xx,env') ->
                               let uu____4639 =
                                 let uu____4647 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____4647 env1 xx
                                  in
                               (match uu____4639 with
                                | (guard_x_t,decls') ->
                                    let uu____4699 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xxsym,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    (uu____4699, guard_x_t, env', decls', x))
                            in
                         (match uu____4495 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____4172 with
         | (vars,guards,env1,decls,names1) ->
             ((FStar_List.rev vars), (FStar_List.rev guards), env1, decls,
               (FStar_List.rev names1)))

and (encode_term_pred :
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.typ ->
      FStar_SMTEncoding_Env.env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____5077 = encode_term t env  in
          match uu____5077 with
          | (t1,decls) ->
              let uu____5100 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____5100, decls)

and (encode_term_pred' :
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.typ ->
      FStar_SMTEncoding_Env.env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____5144 = encode_term t env  in
          match uu____5144 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____5177 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____5177, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____5194 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____5194, decls))

and (encode_arith_term :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____5224 = encode_args args_e env  in
        match uu____5224 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____5267 -> failwith "Impossible"  in
            let unary unbox arg_tms1 =
              let uu____5313 = FStar_List.hd arg_tms1  in unbox uu____5313
               in
            let binary unbox arg_tms1 =
              let uu____5371 =
                let uu____5378 = FStar_List.hd arg_tms1  in unbox uu____5378
                 in
              let uu____5388 =
                let uu____5395 =
                  let uu____5402 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____5402  in
                unbox uu____5395  in
              (uu____5371, uu____5388)  in
            let mk_default uu____5428 =
              let uu____5429 =
                FStar_SMTEncoding_Env.lookup_free_var_sym env
                  head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____5429 with
              | (fname,fuel_args,arity) ->
                  let args = FStar_List.append fuel_args arg_tms  in
                  maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity
                    args
               in
            let mk_l box op mk_args ts =
              let uu____5578 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____5578
              then
                let uu____5584 =
                  let uu____5591 = mk_args ts  in op uu____5591  in
                FStar_All.pipe_right uu____5584 box
              else mk_default ()  in
            let mk_nl box unbox nm op ts =
              let uu____5706 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____5706
              then
                let uu____5712 = binary unbox ts  in
                match uu____5712 with
                | (t1,t2) ->
                    let uu____5740 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____5740 box
              else
                (let uu____5770 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____5770
                 then
                   let uu____5776 =
                     let uu____5783 = binary unbox ts  in op uu____5783  in
                   FStar_All.pipe_right uu____5776 box
                 else mk_default ())
               in
            let add1 box unbox =
              mk_l box FStar_SMTEncoding_Util.mkAdd (binary unbox)  in
            let sub1 box unbox =
              mk_l box FStar_SMTEncoding_Util.mkSub (binary unbox)  in
            let minus1 box unbox =
              mk_l box FStar_SMTEncoding_Util.mkMinus (unary unbox)  in
            let mul1 box unbox nm =
              mk_nl box unbox nm FStar_SMTEncoding_Util.mkMul  in
            let div1 box unbox nm =
              mk_nl box unbox nm FStar_SMTEncoding_Util.mkDiv  in
            let modulus box unbox =
              mk_nl box unbox "_mod" FStar_SMTEncoding_Util.mkMod  in
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
                   (binary FStar_SMTEncoding_Term.unboxReal)))]
               in
            let uu____6749 =
              let uu____6769 =
                FStar_List.tryFind
                  (fun uu____6813  ->
                     match uu____6813 with
                     | (l,uu____6834) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____6769 FStar_Util.must  in
            (match uu____6749 with
             | (uu____6931,op) ->
                 let uu____6963 = op arg_tms  in (uu____6963, decls))

and (encode_BitVector_term :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        Prims.list ->
        (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_elt
          Prims.list))
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____7007 = FStar_List.hd args_e  in
        match uu____7007 with
        | (tm_sz,uu____7034) ->
            let uu____7051 = uu____7007  in
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let t_decls1 = FStar_SMTEncoding_Term.mkBvConstructor sz  in
              FStar_SMTEncoding_Term.mk_decls "" sz_key t_decls1 []  in
            let uu____7066 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____7096::(sz_arg,uu____7098)::uu____7099::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____7205 =
                    let uu____7206 = FStar_List.tail args_e  in
                    FStar_List.tail uu____7206  in
                  let uu____7245 =
                    let uu____7249 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____7249  in
                  (uu____7205, uu____7245)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____7256::(sz_arg,uu____7258)::uu____7259::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____7365 =
                    let uu____7367 = FStar_Syntax_Print.term_to_string sz_arg
                       in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____7367
                     in
                  failwith uu____7365
              | uu____7377 ->
                  let uu____7396 = FStar_List.tail args_e  in
                  (uu____7396, FStar_Pervasives_Native.None)
               in
            (match uu____7066 with
             | (arg_tms,ext_sz) ->
                 let uu____7434 = encode_args arg_tms env  in
                 (match uu____7434 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____7483 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____7507 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____7507  in
                      let unary_arith arg_tms2 =
                        let uu____7536 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____7536  in
                      let binary arg_tms2 =
                        let uu____7572 =
                          let uu____7579 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____7579
                           in
                        let uu____7589 =
                          let uu____7596 =
                            let uu____7603 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____7603  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____7596
                           in
                        (uu____7572, uu____7589)  in
                      let binary_arith arg_tms2 =
                        let uu____7647 =
                          let uu____7654 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____7654
                           in
                        let uu____7664 =
                          let uu____7671 =
                            let uu____7678 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____7678  in
                          FStar_SMTEncoding_Term.unboxInt uu____7671  in
                        (uu____7647, uu____7664)  in
                      let mk_bv op mk_args resBox ts =
                        let uu____7784 =
                          let uu____7791 = mk_args ts  in op uu____7791  in
                        FStar_All.pipe_right uu____7784 resBox  in
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
                        let uu____8070 =
                          let uu____8081 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____8081  in
                        let uu____8090 =
                          let uu____8101 =
                            let uu____8103 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____8103  in
                          FStar_SMTEncoding_Term.boxBitVec uu____8101  in
                        mk_bv uu____8070 unary uu____8090 arg_tms2  in
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
                      let uu____8664 =
                        let uu____8684 =
                          FStar_List.tryFind
                            (fun uu____8728  ->
                               match uu____8728 with
                               | (l,uu____8749) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____8684 FStar_Util.must  in
                      (match uu____8664 with
                       | (uu____8852,op) ->
                           let uu____8884 = op arg_tms1  in
                           (uu____8884, (FStar_List.append sz_decls decls)))))

and (encode_deeply_embedded_quantifier :
  FStar_Syntax_Syntax.term ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let env1 =
        let uu___540_8951 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___540_8951.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___540_8951.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___540_8951.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___540_8951.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___540_8951.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___540_8951.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name =
            (uu___540_8951.FStar_SMTEncoding_Env.use_zfuel_name);
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___540_8951.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___540_8951.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier = true;
          FStar_SMTEncoding_Env.global_cache =
            (uu___540_8951.FStar_SMTEncoding_Env.global_cache)
        }  in
      let uu____8975 = encode_term t env1  in
      match uu____8975 with
      | (tm,decls) ->
          let vars = FStar_SMTEncoding_Term.free_variables tm  in
          let valid_tm = FStar_SMTEncoding_Term.mk_Valid tm  in
          let key =
            FStar_SMTEncoding_Term.mkForall t.FStar_Syntax_Syntax.pos
              ([], vars, valid_tm)
             in
          let tkey_hash = FStar_SMTEncoding_Term.hash_of_term key  in
          (match tm.FStar_SMTEncoding_Term.tm with
           | FStar_SMTEncoding_Term.App
               (uu____9037,{
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.FreeV uu____9038;
                             FStar_SMTEncoding_Term.freevars = uu____9039;
                             FStar_SMTEncoding_Term.rng = uu____9040;_}::
                {
                  FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV
                    uu____9041;
                  FStar_SMTEncoding_Term.freevars = uu____9042;
                  FStar_SMTEncoding_Term.rng = uu____9043;_}::[])
               ->
               (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                  (FStar_Errors.Warning_QuantifierWithoutPattern,
                    "Not encoding deeply embedded, unguarded quantifier to SMT");
                (tm, decls))
           | uu____9104 ->
               let uu____9105 = encode_formula t env1  in
               (match uu____9105 with
                | (phi,decls') ->
                    let interp =
                      match vars with
                      | [] ->
                          let uu____9146 =
                            let uu____9157 =
                              FStar_SMTEncoding_Term.mk_Valid tm  in
                            (uu____9157, phi)  in
                          FStar_SMTEncoding_Util.mkIff uu____9146
                      | uu____9170 ->
                          let uu____9171 =
                            let uu____9188 =
                              let uu____9195 =
                                let uu____9206 =
                                  FStar_SMTEncoding_Term.mk_Valid tm  in
                                (uu____9206, phi)  in
                              FStar_SMTEncoding_Util.mkIff uu____9195  in
                            ([[valid_tm]], vars, uu____9188)  in
                          FStar_SMTEncoding_Term.mkForall
                            t.FStar_Syntax_Syntax.pos uu____9171
                       in
                    let ax =
                      let uu____9246 =
                        let uu____9257 =
                          let uu____9259 =
                            FStar_Util.digest_of_string tkey_hash  in
                          Prims.op_Hat "l_quant_interp_" uu____9259  in
                        (interp,
                          (FStar_Pervasives_Native.Some
                             "Interpretation of deeply embedded quantifier"),
                          uu____9257)
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____9246  in
                    let uu____9268 =
                      let uu____9269 =
                        let uu____9276 =
                          FStar_SMTEncoding_Term.mk_decls "" tkey_hash 
                            [ax] (FStar_List.append decls decls')
                           in
                        FStar_List.append decls' uu____9276  in
                      FStar_List.append decls uu____9269  in
                    (tm, uu____9268)))

and (encode_term :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____9333 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____9333
       then
         let uu____9338 = FStar_Syntax_Print.tag_of_term t  in
         let uu____9340 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____9342 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____9338 uu____9340
           uu____9342
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____9354 ->
           let uu____9385 =
             let uu____9387 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____9390 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____9392 = FStar_Syntax_Print.term_to_string t0  in
             let uu____9394 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____9387
               uu____9390 uu____9392 uu____9394
              in
           failwith uu____9385
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____9404 =
             let uu____9406 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____9409 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____9411 = FStar_Syntax_Print.term_to_string t0  in
             let uu____9413 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____9406
               uu____9409 uu____9411 uu____9413
              in
           failwith uu____9404
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let e = FStar_Syntax_Util.unfold_lazy i  in
           ((let uu____9438 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____9438
             then
               let uu____9443 = FStar_Syntax_Print.term_to_string t0  in
               let uu____9445 = FStar_Syntax_Print.term_to_string e  in
               FStar_Util.print2 ">> Unfolded (%s) ~> (%s)\n" uu____9443
                 uu____9445
             else ());
            encode_term e env)
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____9456 =
             let uu____9458 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____9458
              in
           failwith uu____9456
       | FStar_Syntax_Syntax.Tm_ascribed (t1,(k,uu____9470),uu____9471) ->
           let uu____9572 =
             match k with
             | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
             | uu____9594 -> false  in
           if uu____9572
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t1 env
       | FStar_Syntax_Syntax.Tm_quoted (qt,uu____9630) ->
           let tv =
             let uu____9656 =
               let uu____9663 = FStar_Reflection_Basic.inspect_ln qt  in
               FStar_Syntax_Embeddings.embed
                 FStar_Reflection_Embeddings.e_term_view uu____9663
                in
             uu____9656 t.FStar_Syntax_Syntax.pos
               FStar_Pervasives_Native.None
               FStar_Syntax_Embeddings.id_norm_cb
              in
           ((let uu____9671 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____9671
             then
               let uu____9676 = FStar_Syntax_Print.term_to_string t0  in
               let uu____9678 = FStar_Syntax_Print.term_to_string tv  in
               FStar_Util.print2 ">> Inspected (%s) ~> (%s)\n" uu____9676
                 uu____9678
             else ());
            (let t1 =
               let uu____9694 =
                 let uu____9709 = FStar_Syntax_Syntax.as_arg tv  in
                 [uu____9709]  in
               FStar_Syntax_Util.mk_app
                 (FStar_Reflection_Data.refl_constant_term
                    FStar_Reflection_Data.fstar_refl_pack_ln) uu____9694
                in
             encode_term t1 env))
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_pattern uu____9747) ->
           encode_term t1
             (let uu___612_9789 = env  in
              {
                FStar_SMTEncoding_Env.bvar_bindings =
                  (uu___612_9789.FStar_SMTEncoding_Env.bvar_bindings);
                FStar_SMTEncoding_Env.fvar_bindings =
                  (uu___612_9789.FStar_SMTEncoding_Env.fvar_bindings);
                FStar_SMTEncoding_Env.depth =
                  (uu___612_9789.FStar_SMTEncoding_Env.depth);
                FStar_SMTEncoding_Env.tcenv =
                  (uu___612_9789.FStar_SMTEncoding_Env.tcenv);
                FStar_SMTEncoding_Env.warn =
                  (uu___612_9789.FStar_SMTEncoding_Env.warn);
                FStar_SMTEncoding_Env.nolabels =
                  (uu___612_9789.FStar_SMTEncoding_Env.nolabels);
                FStar_SMTEncoding_Env.use_zfuel_name =
                  (uu___612_9789.FStar_SMTEncoding_Env.use_zfuel_name);
                FStar_SMTEncoding_Env.encode_non_total_function_typ =
                  (uu___612_9789.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                FStar_SMTEncoding_Env.current_module_name =
                  (uu___612_9789.FStar_SMTEncoding_Env.current_module_name);
                FStar_SMTEncoding_Env.encoding_quantifier = false;
                FStar_SMTEncoding_Env.global_cache =
                  (uu___612_9789.FStar_SMTEncoding_Env.global_cache)
              })
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____9814) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = FStar_SMTEncoding_Env.lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____9851 = head_redex env t  in
           if uu____9851
           then let uu____9861 = whnf env t  in encode_term uu____9861 env
           else
             (let fvb =
                FStar_SMTEncoding_Env.lookup_free_var_name env
                  v1.FStar_Syntax_Syntax.fv_name
                 in
              let tok =
                FStar_SMTEncoding_Env.lookup_free_var env
                  v1.FStar_Syntax_Syntax.fv_name
                 in
              let tkey_hash = FStar_SMTEncoding_Term.hash_of_term tok  in
              let uu____9902 =
                if
                  fvb.FStar_SMTEncoding_Env.smt_arity > (Prims.parse_int "0")
                then
                  match tok.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.FreeV uu____9926 ->
                      let sym_name =
                        let uu____9937 =
                          FStar_Util.digest_of_string tkey_hash  in
                        Prims.op_Hat "@kick_partial_app_" uu____9937  in
                      let uu____9940 =
                        let uu____9943 =
                          let uu____9944 =
                            let uu____9955 =
                              FStar_SMTEncoding_Term.kick_partial_app tok  in
                            (uu____9955,
                              (FStar_Pervasives_Native.Some
                                 "kick_partial_app"), sym_name)
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____9944  in
                        [uu____9943]  in
                      (uu____9940, sym_name)
                  | FStar_SMTEncoding_Term.App (uu____9971,[]) ->
                      let sym_name =
                        let uu____9982 =
                          FStar_Util.digest_of_string tkey_hash  in
                        Prims.op_Hat "@kick_partial_app_" uu____9982  in
                      let uu____9985 =
                        let uu____9988 =
                          let uu____9989 =
                            let uu____10000 =
                              FStar_SMTEncoding_Term.kick_partial_app tok  in
                            (uu____10000,
                              (FStar_Pervasives_Native.Some
                                 "kick_partial_app"), sym_name)
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____9989  in
                        [uu____9988]  in
                      (uu____9985, sym_name)
                  | uu____10016 -> ([], "")
                else ([], "")  in
              match uu____9902 with
              | (aux_decls,sym_name) ->
                  let uu____10042 =
                    if aux_decls = []
                    then
                      FStar_All.pipe_right []
                        FStar_SMTEncoding_Term.mk_decls_trivial
                    else
                      FStar_SMTEncoding_Term.mk_decls sym_name tkey_hash
                        aux_decls []
                     in
                  (tok, uu____10042))
       | FStar_Syntax_Syntax.Tm_type uu____10057 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____10066) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.FStar_SMTEncoding_Env.current_module_name
              in
           let uu____10122 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____10122 with
            | (binders1,res) ->
                let uu____10148 =
                  (env.FStar_SMTEncoding_Env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____10148
                then
                  let uu____10158 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____10158 with
                   | (vars,guards,env',decls,uu____10208) ->
                       let fsym =
                         let uu____10260 =
                           let uu____10266 =
                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                               module_name "f"
                              in
                           (uu____10266, FStar_SMTEncoding_Term.Term_sort)
                            in
                         FStar_SMTEncoding_Term.mk_fv uu____10260  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____10284 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___666_10301 =
                              env.FStar_SMTEncoding_Env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___666_10301.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___666_10301.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___666_10301.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___666_10301.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___666_10301.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___666_10301.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___666_10301.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___666_10301.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___666_10301.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___666_10301.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___666_10301.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___666_10301.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___666_10301.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___666_10301.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___666_10301.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___666_10301.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___666_10301.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___666_10301.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___666_10301.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___666_10301.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___666_10301.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___666_10301.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___666_10301.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___666_10301.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___666_10301.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___666_10301.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___666_10301.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___666_10301.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___666_10301.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___666_10301.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___666_10301.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___666_10301.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___666_10301.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___666_10301.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___666_10301.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___666_10301.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___666_10301.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___666_10301.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___666_10301.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___666_10301.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___666_10301.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___666_10301.FStar_TypeChecker_Env.nbe)
                            }) res
                          in
                       (match uu____10284 with
                        | (pre_opt,res_t) ->
                            let uu____10440 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____10440 with
                             | (res_pred,decls') ->
                                 let uu____10466 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____10497 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____10497, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____10526 =
                                         encode_formula pre env'  in
                                       (match uu____10526 with
                                        | (guard,decls0) ->
                                            let uu____10555 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____10555, decls0))
                                    in
                                 (match uu____10466 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____10608 =
                                          let uu____10625 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____10625)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t.FStar_Syntax_Syntax.pos
                                          uu____10608
                                         in
                                      let cvars =
                                        let uu____10675 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____10675
                                          (FStar_List.filter
                                             (fun x  ->
                                                let uu____10694 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    x
                                                   in
                                                let uu____10696 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    fsym
                                                   in
                                                uu____10694 <> uu____10696))
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
                                      let tsym =
                                        let uu____10733 =
                                          FStar_Util.digest_of_string
                                            tkey_hash
                                           in
                                        Prims.op_Hat "Tm_arrow_" uu____10733
                                         in
                                      let cvar_sorts =
                                        FStar_List.map
                                          FStar_SMTEncoding_Term.fv_sort
                                          cvars
                                         in
                                      let caption =
                                        let uu____10748 =
                                          FStar_Options.log_queries ()  in
                                        if uu____10748
                                        then
                                          let uu____10751 =
                                            let uu____10753 =
                                              FStar_TypeChecker_Normalize.term_to_string
                                                env.FStar_SMTEncoding_Env.tcenv
                                                t0
                                               in
                                            FStar_Util.replace_char
                                              uu____10753 10 32
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____10751
                                        else FStar_Pervasives_Native.None  in
                                      let tdecl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (tsym, cvar_sorts,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            caption)
                                         in
                                      let t1 =
                                        let uu____10772 =
                                          let uu____10783 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              cvars
                                             in
                                          (tsym, uu____10783)  in
                                        FStar_SMTEncoding_Util.mkApp
                                          uu____10772
                                         in
                                      let t_has_kind =
                                        FStar_SMTEncoding_Term.mk_HasType t1
                                          FStar_SMTEncoding_Term.mk_Term_type
                                         in
                                      let k_assumption =
                                        let a_name =
                                          Prims.op_Hat "kinding_" tsym  in
                                        let uu____10817 =
                                          let uu____10828 =
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              ([[t_has_kind]], cvars,
                                                t_has_kind)
                                             in
                                          (uu____10828,
                                            (FStar_Pervasives_Native.Some
                                               a_name), a_name)
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____10817
                                         in
                                      let f_has_t =
                                        FStar_SMTEncoding_Term.mk_HasType f
                                          t1
                                         in
                                      let f_has_t_z =
                                        FStar_SMTEncoding_Term.mk_HasTypeZ f
                                          t1
                                         in
                                      let pre_typing =
                                        let a_name =
                                          Prims.op_Hat "pre_typing_" tsym  in
                                        let uu____10884 =
                                          let uu____10895 =
                                            let uu____10902 =
                                              let uu____10919 =
                                                let uu____10926 =
                                                  let uu____10937 =
                                                    let uu____10944 =
                                                      FStar_SMTEncoding_Term.mk_PreType
                                                        f
                                                       in
                                                    FStar_SMTEncoding_Term.mk_tester
                                                      "Tm_arrow" uu____10944
                                                     in
                                                  (f_has_t, uu____10937)  in
                                                FStar_SMTEncoding_Util.mkImp
                                                  uu____10926
                                                 in
                                              ([[f_has_t]], (fsym :: cvars),
                                                uu____10919)
                                               in
                                            let uu____10992 =
                                              mkForall_fuel module_name
                                                t0.FStar_Syntax_Syntax.pos
                                               in
                                            uu____10992 uu____10902  in
                                          (uu____10895,
                                            (FStar_Pervasives_Native.Some
                                               "pre-typing for functions"),
                                            (Prims.op_Hat module_name
                                               (Prims.op_Hat "_" a_name)))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____10884
                                         in
                                      let t_interp1 =
                                        let a_name =
                                          Prims.op_Hat "interpretation_" tsym
                                           in
                                        let uu____11027 =
                                          let uu____11038 =
                                            let uu____11045 =
                                              let uu____11062 =
                                                FStar_SMTEncoding_Util.mkIff
                                                  (f_has_t_z, t_interp)
                                                 in
                                              ([[f_has_t_z]], (fsym ::
                                                cvars), uu____11062)
                                               in
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              uu____11045
                                             in
                                          (uu____11038,
                                            (FStar_Pervasives_Native.Some
                                               a_name),
                                            (Prims.op_Hat module_name
                                               (Prims.op_Hat "_" a_name)))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____11027
                                         in
                                      let t_decls1 =
                                        [tdecl;
                                        k_assumption;
                                        pre_typing;
                                        t_interp1]  in
                                      let uu____11118 =
                                        let uu____11119 =
                                          let uu____11126 =
                                            let uu____11133 =
                                              FStar_SMTEncoding_Term.mk_decls
                                                tsym tkey_hash t_decls1
                                                (FStar_List.append decls
                                                   (FStar_List.append decls'
                                                      guard_decls))
                                               in
                                            FStar_List.append guard_decls
                                              uu____11133
                                             in
                                          FStar_List.append decls'
                                            uu____11126
                                           in
                                        FStar_List.append decls uu____11119
                                         in
                                      (t1, uu____11118)))))
                else
                  (let tsym =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                       module_name "Non_total_Tm_arrow"
                      in
                   let tdecl =
                     FStar_SMTEncoding_Term.DeclFun
                       (tsym, [], FStar_SMTEncoding_Term.Term_sort,
                         FStar_Pervasives_Native.None)
                      in
                   let t1 = FStar_SMTEncoding_Util.mkApp (tsym, [])  in
                   let t_kinding =
                     let a_name =
                       Prims.op_Hat "non_total_function_typing_" tsym  in
                     let uu____11193 =
                       let uu____11204 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____11204,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"), a_name)
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____11193  in
                   let fsym =
                     FStar_SMTEncoding_Term.mk_fv
                       ("f", FStar_SMTEncoding_Term.Term_sort)
                      in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.op_Hat "pre_typing_" tsym  in
                     let uu____11238 =
                       let uu____11249 =
                         let uu____11256 =
                           let uu____11273 =
                             let uu____11280 =
                               let uu____11291 =
                                 let uu____11298 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____11298
                                  in
                               (f_has_t, uu____11291)  in
                             FStar_SMTEncoding_Util.mkImp uu____11280  in
                           ([[f_has_t]], [fsym], uu____11273)  in
                         let uu____11354 =
                           mkForall_fuel module_name
                             t0.FStar_Syntax_Syntax.pos
                            in
                         uu____11354 uu____11256  in
                       (uu____11249, (FStar_Pervasives_Native.Some a_name),
                         a_name)
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____11238  in
                   let uu____11383 =
                     FStar_All.pipe_right [tdecl; t_kinding; t_interp]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                      in
                   (t1, uu____11383)))
       | FStar_Syntax_Syntax.Tm_refine uu____11389 ->
           let uu____11405 =
             let uu____11419 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Env.Weak;
                 FStar_TypeChecker_Env.HNF;
                 FStar_TypeChecker_Env.EraseUniverses]
                 env.FStar_SMTEncoding_Env.tcenv t0
                in
             match uu____11419 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____11443;
                 FStar_Syntax_Syntax.vars = uu____11444;_} ->
                 let uu____11473 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____11473 with
                  | (b,f1) ->
                      let uu____11534 =
                        let uu____11545 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____11545  in
                      (uu____11534, f1))
             | uu____11584 -> failwith "impossible"  in
           (match uu____11405 with
            | (x,f) ->
                let uu____11630 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____11630 with
                 | (base_t,decls) ->
                     let uu____11653 =
                       FStar_SMTEncoding_Env.gen_term_var env x  in
                     (match uu____11653 with
                      | (x1,xtm,env') ->
                          let uu____11715 = encode_formula f env'  in
                          (match uu____11715 with
                           | (refinement,decls') ->
                               let uu____11738 =
                                 FStar_SMTEncoding_Env.fresh_fvar
                                   env.FStar_SMTEncoding_Env.current_module_name
                                   "f" FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____11738 with
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
                                      let uu____11799 =
                                        let uu____11810 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____11821 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____11810
                                          uu____11821
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____11799
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun y  ->
                                              (let uu____11875 =
                                                 FStar_SMTEncoding_Term.fv_name
                                                   y
                                                  in
                                               uu____11875 <> x1) &&
                                                (let uu____11879 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     y
                                                    in
                                                 uu____11879 <> fsym)))
                                       in
                                    let xfv =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (x1,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    let ffv =
                                      FStar_SMTEncoding_Term.mk_fv
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
                                    let module_name =
                                      env.FStar_SMTEncoding_Env.current_module_name
                                       in
                                    let tsym =
                                      let uu____11930 =
                                        FStar_Util.digest_of_string tkey_hash
                                         in
                                      Prims.op_Hat "Tm_refine_" uu____11930
                                       in
                                    let cvar_sorts =
                                      FStar_List.map
                                        FStar_SMTEncoding_Term.fv_sort cvars1
                                       in
                                    let tdecl =
                                      FStar_SMTEncoding_Term.DeclFun
                                        (tsym, cvar_sorts,
                                          FStar_SMTEncoding_Term.Term_sort,
                                          FStar_Pervasives_Native.None)
                                       in
                                    let t1 =
                                      let uu____11956 =
                                        let uu____11967 =
                                          FStar_List.map
                                            FStar_SMTEncoding_Util.mkFreeV
                                            cvars1
                                           in
                                        (tsym, uu____11967)  in
                                      FStar_SMTEncoding_Util.mkApp
                                        uu____11956
                                       in
                                    let x_has_base_t =
                                      FStar_SMTEncoding_Term.mk_HasType xtm
                                        base_t
                                       in
                                    let x_has_t =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm t1
                                       in
                                    let t_has_kind =
                                      FStar_SMTEncoding_Term.mk_HasType t1
                                        FStar_SMTEncoding_Term.mk_Term_type
                                       in
                                    let t_haseq_base =
                                      FStar_SMTEncoding_Term.mk_haseq base_t
                                       in
                                    let t_haseq_ref =
                                      FStar_SMTEncoding_Term.mk_haseq t1  in
                                    let t_haseq1 =
                                      let uu____12029 =
                                        let uu____12040 =
                                          let uu____12047 =
                                            let uu____12064 =
                                              FStar_SMTEncoding_Util.mkIff
                                                (t_haseq_ref, t_haseq_base)
                                               in
                                            ([[t_haseq_ref]], cvars1,
                                              uu____12064)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            t0.FStar_Syntax_Syntax.pos
                                            uu____12047
                                           in
                                        (uu____12040,
                                          (FStar_Pervasives_Native.Some
                                             (Prims.op_Hat "haseq for " tsym)),
                                          (Prims.op_Hat "haseq" tsym))
                                         in
                                      FStar_SMTEncoding_Util.mkAssume
                                        uu____12029
                                       in
                                    let t_kinding =
                                      let uu____12111 =
                                        let uu____12122 =
                                          FStar_SMTEncoding_Term.mkForall
                                            t0.FStar_Syntax_Syntax.pos
                                            ([[t_has_kind]], cvars1,
                                              t_has_kind)
                                           in
                                        (uu____12122,
                                          (FStar_Pervasives_Native.Some
                                             "refinement kinding"),
                                          (Prims.op_Hat "refinement_kinding_"
                                             tsym))
                                         in
                                      FStar_SMTEncoding_Util.mkAssume
                                        uu____12111
                                       in
                                    let t_interp =
                                      let uu____12163 =
                                        let uu____12174 =
                                          let uu____12181 =
                                            let uu____12198 =
                                              FStar_SMTEncoding_Util.mkIff
                                                (x_has_t, encoding)
                                               in
                                            ([[x_has_t]], (ffv :: xfv ::
                                              cvars1), uu____12198)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            t0.FStar_Syntax_Syntax.pos
                                            uu____12181
                                           in
                                        (uu____12174,
                                          (FStar_Pervasives_Native.Some
                                             "refinement_interpretation"),
                                          (Prims.op_Hat
                                             "refinement_interpretation_"
                                             tsym))
                                         in
                                      FStar_SMTEncoding_Util.mkAssume
                                        uu____12163
                                       in
                                    let t_decls1 =
                                      [tdecl; t_kinding; t_interp; t_haseq1]
                                       in
                                    let uu____12263 =
                                      let uu____12264 =
                                        let uu____12271 =
                                          FStar_SMTEncoding_Term.mk_decls
                                            tsym tkey_hash t_decls1
                                            (FStar_List.append decls decls')
                                           in
                                        FStar_List.append decls' uu____12271
                                         in
                                      FStar_List.append decls uu____12264  in
                                    (t1, uu____12263))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,uu____12294) ->
           let ttm =
             let uu____12334 =
               FStar_Syntax_Unionfind.uvar_id
                 uv.FStar_Syntax_Syntax.ctx_uvar_head
                in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____12334  in
           let uu____12336 =
             encode_term_pred FStar_Pervasives_Native.None
               uv.FStar_Syntax_Syntax.ctx_uvar_typ env ttm
              in
           (match uu____12336 with
            | (t_has_k,decls) ->
                let d =
                  let uu____12363 =
                    let uu____12374 =
                      let uu____12376 =
                        let uu____12378 =
                          let uu____12380 =
                            FStar_Syntax_Unionfind.uvar_id
                              uv.FStar_Syntax_Syntax.ctx_uvar_head
                             in
                          FStar_Util.string_of_int uu____12380  in
                        FStar_Util.format1 "uvar_typing_%s" uu____12378  in
                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                        uu____12376
                       in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____12374)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____12363  in
                let uu____12389 =
                  let uu____12390 =
                    FStar_All.pipe_right [d]
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append decls uu____12390  in
                (ttm, uu____12389))
       | FStar_Syntax_Syntax.Tm_app uu____12412 ->
           let uu____12437 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____12437 with
            | (head1,args_e) ->
                let uu____12511 =
                  let uu____12530 =
                    let uu____12531 = FStar_Syntax_Subst.compress head1  in
                    uu____12531.FStar_Syntax_Syntax.n  in
                  (uu____12530, args_e)  in
                (match uu____12511 with
                 | uu____12563 when head_redex env head1 ->
                     let uu____12582 = whnf env t  in
                     encode_term uu____12582 env
                 | uu____12591 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____12622 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_fvar fv,uu____12644) when
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
                       FStar_Syntax_Syntax.pos = uu____12677;
                       FStar_Syntax_Syntax.vars = uu____12678;_},uu____12679),uu____12680)
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
                       FStar_Syntax_Syntax.pos = uu____12725;
                       FStar_Syntax_Syntax.vars = uu____12726;_},uu____12727),
                    (v0,uu____12729)::(v1,uu____12731)::(v2,uu____12733)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____12859 = encode_term v0 env  in
                     (match uu____12859 with
                      | (v01,decls0) ->
                          let uu____12882 = encode_term v1 env  in
                          (match uu____12882 with
                           | (v11,decls1) ->
                               let uu____12905 = encode_term v2 env  in
                               (match uu____12905 with
                                | (v21,decls2) ->
                                    let uu____12928 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____12928,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(v0,uu____12948)::(v1,uu____12950)::(v2,uu____12952)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____13066 = encode_term v0 env  in
                     (match uu____13066 with
                      | (v01,decls0) ->
                          let uu____13089 = encode_term v1 env  in
                          (match uu____13089 with
                           | (v11,decls1) ->
                               let uu____13112 = encode_term v2 env  in
                               (match uu____13112 with
                                | (v21,decls2) ->
                                    let uu____13135 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____13135,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____13154)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____13210)::(rng,uu____13212)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____13295) ->
                     let e0 =
                       let uu____13333 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg
                         env.FStar_SMTEncoding_Env.tcenv head1 uu____13333
                        in
                     ((let uu____13347 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug
                              env.FStar_SMTEncoding_Env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____13347
                       then
                         let uu____13352 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____13352
                       else ());
                      (let e =
                         let uu____13368 =
                           let uu____13373 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____13382 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____13373
                             uu____13382
                            in
                         uu____13368 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____13395),(arg,uu____13397)::[]) ->
                     encode_term arg env
                 | uu____13456 ->
                     let uu____13475 = encode_args args_e env  in
                     (match uu____13475 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____13573 = encode_term head1 env  in
                            match uu____13573 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____13721 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____13721 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____13874  ->
                                                 fun uu____13875  ->
                                                   match (uu____13874,
                                                           uu____13875)
                                                   with
                                                   | ((bv,uu____13923),
                                                      (a,uu____13925)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____13999 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____13999
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____14016 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm
                                             in
                                          (match uu____14016 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type
                                                  in
                                               let tkey_hash =
                                                 FStar_SMTEncoding_Term.hash_of_term
                                                   app_tm
                                                  in
                                               let e_typing =
                                                 let uu____14052 =
                                                   let uu____14063 =
                                                     FStar_SMTEncoding_Term.mkForall
                                                       t0.FStar_Syntax_Syntax.pos
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____14096 =
                                                     let uu____14098 =
                                                       let uu____14100 =
                                                         FStar_SMTEncoding_Term.hash_of_term
                                                           app_tm
                                                          in
                                                       FStar_Util.digest_of_string
                                                         uu____14100
                                                        in
                                                     Prims.op_Hat
                                                       "partial_app_typing_"
                                                       uu____14098
                                                      in
                                                   (uu____14063,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____14096)
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____14052
                                                  in
                                               let uu____14109 =
                                                 let uu____14116 =
                                                   let uu____14123 =
                                                     let uu____14130 =
                                                       FStar_SMTEncoding_Term.mk_decls
                                                         "" tkey_hash
                                                         [e_typing]
                                                         (FStar_List.append
                                                            decls
                                                            (FStar_List.append
                                                               decls' decls''))
                                                        in
                                                     FStar_List.append
                                                       decls'' uu____14130
                                                      in
                                                   FStar_List.append decls'
                                                     uu____14123
                                                    in
                                                 FStar_List.append decls
                                                   uu____14116
                                                  in
                                               (app_tm, uu____14109))))
                             in
                          let encode_full_app fv =
                            let uu____14195 =
                              FStar_SMTEncoding_Env.lookup_free_var_sym env
                                fv
                               in
                            match uu____14195 with
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
                                   FStar_Syntax_Syntax.pos = uu____14287;
                                   FStar_Syntax_Syntax.vars = uu____14288;_},uu____14289)
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
                                   FStar_Syntax_Syntax.pos = uu____14322;
                                   FStar_Syntax_Syntax.vars = uu____14323;_},uu____14324)
                                ->
                                let uu____14340 =
                                  let uu____14349 =
                                    let uu____14358 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____14358
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____14349
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____14340
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____14427 =
                                  let uu____14436 =
                                    let uu____14445 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____14445
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____14436
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____14427
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____14510,(FStar_Util.Inl t1,uu____14512),uu____14513)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____14620,(FStar_Util.Inr c,uu____14622),uu____14623)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____14730 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____14787 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Env.Weak;
                                     FStar_TypeChecker_Env.HNF;
                                     FStar_TypeChecker_Env.EraseUniverses]
                                     env.FStar_SMTEncoding_Env.tcenv
                                     head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____14787
                                  in
                               let uu____14804 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____14804 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____14838;
                                            FStar_Syntax_Syntax.vars =
                                              uu____14839;_},uu____14840)
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
                                     | uu____14888 ->
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
           let uu____15037 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____15037 with
            | (bs1,body1,opening) ->
                let fallback uu____15078 =
                  let f =
                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                      env.FStar_SMTEncoding_Env.current_module_name "Tm_abs"
                     in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding"))
                     in
                  let uu____15088 =
                    let uu____15095 =
                      FStar_SMTEncoding_Term.mk_fv
                        (f, FStar_SMTEncoding_Term.Term_sort)
                       in
                    FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV
                      uu____15095
                     in
                  let uu____15100 =
                    FStar_All.pipe_right [decl]
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  (uu____15088, uu____15100)  in
                let is_impure rc =
                  let uu____15127 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                      env.FStar_SMTEncoding_Env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____15127 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____15176 =
                          let uu____15205 =
                            FStar_TypeChecker_Env.get_range
                              env.FStar_SMTEncoding_Env.tcenv
                             in
                          FStar_TypeChecker_Util.new_implicit_var
                            "SMTEncoding codomain" uu____15205
                            env.FStar_SMTEncoding_Env.tcenv
                            FStar_Syntax_Util.ktype0
                           in
                        (match uu____15176 with
                         | (t1,uu____15212,uu____15213) -> t1)
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  let uu____15271 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                     in
                  if uu____15271
                  then
                    let uu____15280 = FStar_Syntax_Syntax.mk_Total res_typ
                       in
                    FStar_Pervasives_Native.Some uu____15280
                  else
                    (let uu____15295 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid
                        in
                     if uu____15295
                     then
                       let uu____15304 =
                         FStar_Syntax_Syntax.mk_GTotal res_typ  in
                       FStar_Pervasives_Native.Some uu____15304
                     else FStar_Pervasives_Native.None)
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____15338 =
                         let uu____15344 =
                           let uu____15346 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____15346
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____15344)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____15338);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____15365 =
                       (is_impure rc) &&
                         (let uu____15368 =
                            FStar_TypeChecker_Env.is_reifiable_rc
                              env.FStar_SMTEncoding_Env.tcenv rc
                             in
                          Prims.op_Negation uu____15368)
                        in
                     if uu____15365
                     then fallback ()
                     else
                       (let uu____15380 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____15380 with
                        | (vars,guards,envbody,decls,uu____15430) ->
                            let body2 =
                              let uu____15490 =
                                FStar_TypeChecker_Env.is_reifiable_rc
                                  env.FStar_SMTEncoding_Env.tcenv rc
                                 in
                              if uu____15490
                              then
                                FStar_TypeChecker_Util.reify_body
                                  env.FStar_SMTEncoding_Env.tcenv body1
                              else body1  in
                            let uu____15499 = encode_term body2 envbody  in
                            (match uu____15499 with
                             | (body3,decls') ->
                                 let uu____15522 =
                                   let uu____15538 = codomain_eff rc  in
                                   match uu____15538 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____15602 = encode_term tfun env
                                          in
                                       (match uu____15602 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____15522 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____15685 =
                                          let uu____15702 =
                                            let uu____15709 =
                                              let uu____15720 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____15720, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____15709
                                             in
                                          ([], vars, uu____15702)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t0.FStar_Syntax_Syntax.pos
                                          uu____15685
                                         in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body
                                         in
                                      let uu____15749 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            (cvars, key_body)
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____15783 =
                                              let uu____15786 =
                                                let uu____15797 =
                                                  FStar_SMTEncoding_Term.free_variables
                                                    t1
                                                   in
                                                FStar_List.append uu____15797
                                                  cvars
                                                 in
                                              FStar_Util.remove_dups
                                                FStar_SMTEncoding_Term.fv_eq
                                                uu____15786
                                               in
                                            let uu____15824 =
                                              FStar_SMTEncoding_Util.mkAnd
                                                (key_body, t1)
                                               in
                                            (uu____15783, uu____15824)
                                         in
                                      (match uu____15749 with
                                       | (cvars1,key_body1) ->
                                           let tkey =
                                             FStar_SMTEncoding_Term.mkForall
                                               t0.FStar_Syntax_Syntax.pos
                                               ([], cvars1, key_body1)
                                              in
                                           let tkey_hash =
                                             FStar_SMTEncoding_Term.hash_of_term
                                               tkey
                                              in
                                           let uu____15885 =
                                             is_an_eta_expansion env vars
                                               body3
                                              in
                                           (match uu____15885 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       decls'')
                                                   in
                                                (t1, decls1)
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                let cvar_sorts =
                                                  FStar_List.map
                                                    FStar_SMTEncoding_Term.fv_sort
                                                    cvars1
                                                   in
                                                let fsym =
                                                  let uu____15931 =
                                                    FStar_Util.digest_of_string
                                                      tkey_hash
                                                     in
                                                  Prims.op_Hat "Tm_abs_"
                                                    uu____15931
                                                   in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None)
                                                   in
                                                let f =
                                                  let uu____15946 =
                                                    let uu____15957 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    (fsym, uu____15957)  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____15946
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
                                                        Prims.op_Hat
                                                          "typing_" fsym
                                                         in
                                                      let uu____16007 =
                                                        let uu____16008 =
                                                          let uu____16019 =
                                                            FStar_SMTEncoding_Term.mkForall
                                                              t0.FStar_Syntax_Syntax.pos
                                                              ([[f]], cvars1,
                                                                f_has_t)
                                                             in
                                                          (uu____16019,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name)
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____16008
                                                         in
                                                      [uu____16007]
                                                   in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.op_Hat
                                                      "interpretation_" fsym
                                                     in
                                                  let uu____16061 =
                                                    let uu____16072 =
                                                      let uu____16079 =
                                                        let uu____16096 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3)
                                                           in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____16096)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        t0.FStar_Syntax_Syntax.pos
                                                        uu____16079
                                                       in
                                                    (uu____16072,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____16061
                                                   in
                                                let f_decls =
                                                  FStar_List.append (fdecl ::
                                                    typing_f) [interp_f]
                                                   in
                                                let uu____16143 =
                                                  let uu____16144 =
                                                    let uu____16151 =
                                                      let uu____16158 =
                                                        FStar_SMTEncoding_Term.mk_decls
                                                          fsym tkey_hash
                                                          f_decls
                                                          (FStar_List.append
                                                             decls
                                                             (FStar_List.append
                                                                decls'
                                                                decls''))
                                                         in
                                                      FStar_List.append
                                                        decls'' uu____16158
                                                       in
                                                    FStar_List.append decls'
                                                      uu____16151
                                                     in
                                                  FStar_List.append decls
                                                    uu____16144
                                                   in
                                                (f, uu____16143))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____16188,{
                           FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                             uu____16189;
                           FStar_Syntax_Syntax.lbunivs = uu____16190;
                           FStar_Syntax_Syntax.lbtyp = uu____16191;
                           FStar_Syntax_Syntax.lbeff = uu____16192;
                           FStar_Syntax_Syntax.lbdef = uu____16193;
                           FStar_Syntax_Syntax.lbattrs = uu____16194;
                           FStar_Syntax_Syntax.lbpos = uu____16195;_}::uu____16196),uu____16197)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____16299;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____16301;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____16303;
                FStar_Syntax_Syntax.lbpos = uu____16304;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____16398 ->
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
                 (FStar_SMTEncoding_Term.term *
                   FStar_SMTEncoding_Term.decls_t))
              ->
              (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun x  ->
    fun t1  ->
      fun e1  ->
        fun e2  ->
          fun env  ->
            fun encode_body  ->
              let uu____16560 =
                let uu____16568 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____16568 env  in
              match uu____16560 with
              | (ee1,decls1) ->
                  let uu____16634 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____16634 with
                   | (xs,e21) ->
                       let uu____16689 = FStar_List.hd xs  in
                       (match uu____16689 with
                        | (x1,uu____16720) ->
                            let env' =
                              FStar_SMTEncoding_Env.push_term_var env x1 ee1
                               in
                            let uu____16758 = encode_body e21 env'  in
                            (match uu____16758 with
                             | (ee2,decls2) ->
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
  fun e  ->
    fun pats  ->
      fun default_case  ->
        fun env  ->
          fun encode_br  ->
            let uu____16846 =
              let uu____16868 =
                let uu____16879 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____16879  in
              FStar_SMTEncoding_Env.gen_term_var env uu____16868  in
            match uu____16846 with
            | (scrsym,scr',env1) ->
                let uu____16928 = encode_term e env1  in
                (match uu____16928 with
                 | (scr,decls) ->
                     let uu____16951 =
                       let encode_branch b uu____17001 =
                         match uu____17001 with
                         | (else_case,decls1) ->
                             let uu____17048 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____17048 with
                              | (p,w,br) ->
                                  let uu____17103 = encode_pat env1 p  in
                                  (match uu____17103 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____17266  ->
                                                   match uu____17266 with
                                                   | (x,t) ->
                                                       FStar_SMTEncoding_Env.push_term_var
                                                         env2 x t) env1)
                                          in
                                       let uu____17319 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____17378 =
                                               encode_term w1 env2  in
                                             (match uu____17378 with
                                              | (w2,decls2) ->
                                                  let uu____17407 =
                                                    let uu____17414 =
                                                      let uu____17425 =
                                                        let uu____17432 =
                                                          let uu____17443 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____17443)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____17432
                                                         in
                                                      (guard, uu____17425)
                                                       in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____17414
                                                     in
                                                  (uu____17407, decls2))
                                          in
                                       (match uu____17319 with
                                        | (guard1,decls2) ->
                                            let uu____17504 =
                                              encode_br br env2  in
                                            (match uu____17504 with
                                             | (br1,decls3) ->
                                                 let uu____17533 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____17533,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____16951 with
                      | (match_tm,decls1) ->
                          let uu____17615 =
                            let uu____17622 =
                              let uu____17639 =
                                let uu____17649 =
                                  let uu____17657 =
                                    FStar_SMTEncoding_Term.mk_fv
                                      (scrsym,
                                        FStar_SMTEncoding_Term.Term_sort)
                                     in
                                  (uu____17657, scr)  in
                                [uu____17649]  in
                              (uu____17639, match_tm)  in
                            FStar_SMTEncoding_Term.mkLet' uu____17622
                              FStar_Range.dummyRange
                             in
                          (uu____17615, decls1)))

and (encode_pat :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.pat -> (FStar_SMTEncoding_Env.env_t * pattern))
  =
  fun env  ->
    fun pat  ->
      (let uu____17724 =
         FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
           FStar_Options.Medium
          in
       if uu____17724
       then
         let uu____17727 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____17727
       else ());
      (let uu____17732 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____17732 with
       | (vars,pat_term) ->
           let uu____17791 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____17891  ->
                     fun v1  ->
                       match uu____17891 with
                       | (env1,vars1) ->
                           let uu____17996 =
                             FStar_SMTEncoding_Env.gen_term_var env1 v1  in
                           (match uu____17996 with
                            | (xx,uu____18045,env2) ->
                                let uu____18077 =
                                  let uu____18089 =
                                    let uu____18099 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xx,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    (v1, uu____18099)  in
                                  uu____18089 :: vars1  in
                                (env2, uu____18077))) (env, []))
              in
           (match uu____17791 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____18263 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____18269 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____18275 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____18292 = encode_const c env1  in
                      (match uu____18292 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____18312::uu____18313 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____18329 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon
                            env1.FStar_SMTEncoding_Env.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____18388 =
                          FStar_TypeChecker_Env.datacons_of_typ
                            env1.FStar_SMTEncoding_Env.tcenv tc_name
                           in
                        match uu____18388 with
                        | (uu____18403,uu____18404::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____18425 ->
                            FStar_SMTEncoding_Env.mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____18495  ->
                                  match uu____18495 with
                                  | (arg,uu____18508) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____18527 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____18527))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____18602) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____18733 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____18778 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____18854  ->
                                  match uu____18854 with
                                  | (arg,uu____18878) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____18897 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____18897))
                         in
                      FStar_All.pipe_right uu____18778 FStar_List.flatten
                   in
                let pat_term1 uu____18970 = encode_term pat_term env1  in
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
      (FStar_SMTEncoding_Term.term Prims.list *
        FStar_SMTEncoding_Term.decls_t))
  =
  fun l  ->
    fun env  ->
      let uu____19017 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____19094  ->
                fun uu____19095  ->
                  match (uu____19094, uu____19095) with
                  | ((tms,decls),(t,uu____19164)) ->
                      let uu____19224 = encode_term t env  in
                      (match uu____19224 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____19017 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let universe_of_binders binders =
        FStar_List.map (fun uu____19402  -> FStar_Syntax_Syntax.U_zero)
          binders
         in
      let quant = FStar_Syntax_Util.smt_lemma_as_forall t universe_of_binders
         in
      let env1 =
        let uu___1241_19446 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___1241_19446.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___1241_19446.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___1241_19446.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___1241_19446.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___1241_19446.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___1241_19446.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___1241_19446.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___1241_19446.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___1241_19446.FStar_SMTEncoding_Env.encoding_quantifier);
          FStar_SMTEncoding_Env.global_cache =
            (uu___1241_19446.FStar_SMTEncoding_Env.global_cache)
        }  in
      encode_formula quant env1

and (encode_smt_patterns :
  FStar_Syntax_Syntax.arg Prims.list Prims.list ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term Prims.list Prims.list *
        FStar_SMTEncoding_Term.decls_t))
  =
  fun pats_l  ->
    fun env  ->
      let env1 =
        let uu___1246_19521 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___1246_19521.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___1246_19521.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___1246_19521.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___1246_19521.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___1246_19521.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___1246_19521.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___1246_19521.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___1246_19521.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___1246_19521.FStar_SMTEncoding_Env.encoding_quantifier);
          FStar_SMTEncoding_Env.global_cache =
            (uu___1246_19521.FStar_SMTEncoding_Env.global_cache)
        }  in
      let encode_smt_pattern t =
        let uu____19570 = FStar_Syntax_Util.head_and_args t  in
        match uu____19570 with
        | (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____19675::(x,uu____19677)::(t1,uu____19679)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____19789 = encode_term x env1  in
                 (match uu____19789 with
                  | (x1,decls) ->
                      let uu____19812 = encode_term t1 env1  in
                      (match uu____19812 with
                       | (t2,decls') ->
                           let uu____19835 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                           (uu____19835, (FStar_List.append decls decls'))))
             | uu____19849 -> encode_term t env1)
         in
      FStar_List.fold_right
        (fun pats  ->
           fun uu____19907  ->
             match uu____19907 with
             | (pats_l1,decls) ->
                 let uu____19984 =
                   FStar_List.fold_right
                     (fun uu____20037  ->
                        fun uu____20038  ->
                          match (uu____20037, uu____20038) with
                          | ((p,uu____20109),(pats1,decls1)) ->
                              let uu____20177 = encode_smt_pattern p  in
                              (match uu____20177 with
                               | (t,d) ->
                                   let uu____20208 =
                                     FStar_SMTEncoding_Term.check_pattern_ok
                                       t
                                      in
                                   (match uu____20208 with
                                    | FStar_Pervasives_Native.None  ->
                                        ((t :: pats1),
                                          (FStar_List.append d decls1))
                                    | FStar_Pervasives_Native.Some
                                        illegal_subterm ->
                                        ((let uu____20258 =
                                            let uu____20264 =
                                              let uu____20266 =
                                                FStar_Syntax_Print.term_to_string
                                                  p
                                                 in
                                              let uu____20268 =
                                                FStar_SMTEncoding_Term.print_smt_term
                                                  illegal_subterm
                                                 in
                                              FStar_Util.format2
                                                "Pattern %s contains illegal sub-term (%s); dropping it"
                                                uu____20266 uu____20268
                                               in
                                            (FStar_Errors.Warning_SMTPatternIllFormed,
                                              uu____20264)
                                             in
                                          FStar_Errors.log_issue
                                            p.FStar_Syntax_Syntax.pos
                                            uu____20258);
                                         (pats1,
                                           (FStar_List.append d decls1))))))
                     pats ([], decls)
                    in
                 (match uu____19984 with
                  | (pats1,decls1) -> ((pats1 :: pats_l1), decls1))) pats_l
        ([], [])

and (encode_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____20420 =
          FStar_All.pipe_left
            (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____20420
        then
          let uu____20425 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____20427 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____20425 uu____20427
        else ()  in
      let enc f r l =
        let uu____20487 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____20545 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____20545 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____20487 with
        | (decls,args) ->
            let uu____20628 =
              let uu___1310_20635 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___1310_20635.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___1310_20635.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____20628, decls)
         in
      let const_op f r uu____20693 =
        let uu____20713 = f r  in (uu____20713, [])  in
      let un_op f l =
        let uu____20774 = FStar_List.hd l  in
        FStar_All.pipe_left f uu____20774  in
      let bin_op f uu___2_20824 =
        match uu___2_20824 with
        | t1::t2::[] -> f (t1, t2)
        | uu____20871 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____20936 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____20979  ->
                 match uu____20979 with
                 | (t,uu____21010) ->
                     let uu____21023 = encode_formula t env  in
                     (match uu____21023 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____20936 with
        | (decls,phis) ->
            let uu____21100 =
              let uu___1340_21107 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___1340_21107.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___1340_21107.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____21100, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____21201  ->
               match uu____21201 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____21234) -> false
                    | uu____21237 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____21263 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____21263
        else
          (let uu____21287 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____21287 r rf)
         in
      let eq3_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____21379 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::t1::v0::v1::[] ->
                     let uu____21447 =
                       let uu____21458 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____21471 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____21458, uu____21471)  in
                     FStar_SMTEncoding_Util.mkAnd uu____21447
                 | uu____21490 -> failwith "Impossible")
             in
          uu____21379 r args
        else
          (let uu____21502 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____21502)
         in
      let h_equals_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____21588 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::v0::t1::v1::[] ->
                     let uu____21656 =
                       let uu____21667 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____21680 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____21667, uu____21680)  in
                     FStar_SMTEncoding_Util.mkAnd uu____21656
                 | uu____21699 -> failwith "Impossible")
             in
          uu____21588 r args
        else
          (let uu____21711 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____21711)
         in
      let mk_imp1 r uu___3_21749 =
        match uu___3_21749 with
        | (lhs,uu____21758)::(rhs,uu____21760)::[] ->
            let uu____21829 = encode_formula rhs env  in
            (match uu____21829 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____21859) ->
                      (l1, decls1)
                  | uu____21873 ->
                      let uu____21874 = encode_formula lhs env  in
                      (match uu____21874 with
                       | (l2,decls2) ->
                           let uu____21897 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____21897, (FStar_List.append decls1 decls2)))))
        | uu____21917 -> failwith "impossible"  in
      let mk_ite r uu___4_21954 =
        match uu___4_21954 with
        | (guard,uu____21963)::(_then,uu____21965)::(_else,uu____21967)::[]
            ->
            let uu____22064 = encode_formula guard env  in
            (match uu____22064 with
             | (g,decls1) ->
                 let uu____22087 = encode_formula _then env  in
                 (match uu____22087 with
                  | (t,decls2) ->
                      let uu____22110 = encode_formula _else env  in
                      (match uu____22110 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____22160 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____22214 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l
           in
        f uu____22214  in
      let connectives =
        let uu____22264 =
          let uu____22300 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____22300)  in
        let uu____22361 =
          let uu____22399 =
            let uu____22435 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____22435)  in
          let uu____22496 =
            let uu____22534 =
              let uu____22572 =
                let uu____22608 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____22608)  in
              let uu____22669 =
                let uu____22707 =
                  let uu____22745 =
                    let uu____22781 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____22781)  in
                  [uu____22745;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.c_eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq3_op);
                  (FStar_Parser_Const.c_eq3_lid, h_equals_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____22707  in
              uu____22572 :: uu____22669  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____22534  in
          uu____22399 :: uu____22496  in
        uu____22264 :: uu____22361  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____23597 = encode_formula phi' env  in
            (match uu____23597 with
             | (phi2,decls) ->
                 let uu____23620 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____23620, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____23634 ->
            let uu____23645 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____23645 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____23722 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____23722 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____23749;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____23751;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____23753;
                 FStar_Syntax_Syntax.lbpos = uu____23754;_}::[]),e2)
            ->
            let uu____23848 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____23848 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____23947::(x,uu____23949)::(t,uu____23951)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____24061 = encode_term x env  in
                 (match uu____24061 with
                  | (x1,decls) ->
                      let uu____24084 = encode_term t env  in
                      (match uu____24084 with
                       | (t1,decls') ->
                           let uu____24107 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____24107, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____24123)::(msg,uu____24125)::(phi2,uu____24127)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____24241 =
                   let uu____24246 =
                     let uu____24247 = FStar_Syntax_Subst.compress r  in
                     uu____24247.FStar_Syntax_Syntax.n  in
                   let uu____24258 =
                     let uu____24259 = FStar_Syntax_Subst.compress msg  in
                     uu____24259.FStar_Syntax_Syntax.n  in
                   (uu____24246, uu____24258)  in
                 (match uu____24241 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____24279))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____24302 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____24309)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____24367 when head_redex env head2 ->
                 let uu____24386 = whnf env phi1  in
                 encode_formula uu____24386 env
             | uu____24395 ->
                 let uu____24414 = encode_term phi1 env  in
                 (match uu____24414 with
                  | (tt,decls) ->
                      let tt1 =
                        let uu____24444 =
                          let uu____24446 =
                            FStar_Range.use_range
                              tt.FStar_SMTEncoding_Term.rng
                             in
                          let uu____24447 =
                            FStar_Range.use_range
                              phi1.FStar_Syntax_Syntax.pos
                             in
                          FStar_Range.rng_included uu____24446 uu____24447
                           in
                        if uu____24444
                        then tt
                        else
                          (let uu___1527_24454 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___1527_24454.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___1527_24454.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      let uu____24461 = FStar_SMTEncoding_Term.mk_Valid tt1
                         in
                      (uu____24461, decls)))
        | uu____24471 ->
            let uu____24472 = encode_term phi1 env  in
            (match uu____24472 with
             | (tt,decls) ->
                 let tt1 =
                   let uu____24502 =
                     let uu____24504 =
                       FStar_Range.use_range tt.FStar_SMTEncoding_Term.rng
                        in
                     let uu____24505 =
                       FStar_Range.use_range phi1.FStar_Syntax_Syntax.pos  in
                     FStar_Range.rng_included uu____24504 uu____24505  in
                   if uu____24502
                   then tt
                   else
                     (let uu___1535_24512 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___1535_24512.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___1535_24512.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 let uu____24519 = FStar_SMTEncoding_Term.mk_Valid tt1  in
                 (uu____24519, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____24615 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____24615 with
        | (vars,guards,env2,decls,uu____24689) ->
            let uu____24740 = encode_smt_patterns ps env2  in
            (match uu____24740 with
             | (pats,decls') ->
                 let uu____24799 = encode_formula body env2  in
                 (match uu____24799 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____24859;
                             FStar_SMTEncoding_Term.rng = uu____24860;_}::[])::[]
                            when
                            let uu____24904 =
                              FStar_Ident.text_of_lid
                                FStar_Parser_Const.guard_free
                               in
                            uu____24904 = gf -> []
                        | uu____24910 -> guards  in
                      let uu____24918 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____24918, body1,
                        (FStar_List.append decls
                           (FStar_List.append decls' decls'')))))
         in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi  in
       let uu____24964 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____24964 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____24984 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____25134  ->
                     match uu____25134 with
                     | (l,uu____25170) -> FStar_Ident.lid_equals op l))
              in
           (match uu____24984 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____25275,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____25416 = encode_q_body env vars pats body  in
             match uu____25416 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____25509 =
                     let uu____25526 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____25526)  in
                   FStar_SMTEncoding_Term.mkForall
                     phi1.FStar_Syntax_Syntax.pos uu____25509
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____25594 = encode_q_body env vars pats body  in
             match uu____25594 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____25680 =
                   let uu____25687 =
                     let uu____25704 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____25704)  in
                   FStar_SMTEncoding_Term.mkExists
                     phi1.FStar_Syntax_Syntax.pos uu____25687
                    in
                 (uu____25680, decls))))
