open Prims
let mkForall_fuel' :
  'Auu____71176 .
    Prims.string ->
      FStar_Range.range ->
        'Auu____71176 ->
          (FStar_SMTEncoding_Term.pat Prims.list Prims.list *
            FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term) ->
            FStar_SMTEncoding_Term.term
  =
  fun mname  ->
    fun r  ->
      fun n1  ->
        fun uu____71207  ->
          match uu____71207 with
          | (pats,vars,body) ->
              let fallback uu____71235 =
                FStar_SMTEncoding_Term.mkForall r (pats, vars, body)  in
              let uu____71240 = FStar_Options.unthrottle_inductives ()  in
              if uu____71240
              then fallback ()
              else
                (let uu____71245 =
                   FStar_SMTEncoding_Env.fresh_fvar mname "f"
                     FStar_SMTEncoding_Term.Fuel_sort
                    in
                 match uu____71245 with
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
                               | uu____71285 -> p))
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
                                 let uu____71306 = add_fuel1 guards  in
                                 FStar_SMTEncoding_Util.mk_and_l uu____71306
                             | uu____71309 ->
                                 let uu____71310 = add_fuel1 [guard]  in
                                 FStar_All.pipe_right uu____71310
                                   FStar_List.hd
                              in
                           FStar_SMTEncoding_Util.mkImp (guard1, body')
                       | uu____71315 -> body  in
                     let vars1 =
                       let uu____71327 =
                         FStar_SMTEncoding_Term.mk_fv
                           (fsym, FStar_SMTEncoding_Term.Fuel_sort)
                          in
                       uu____71327 :: vars  in
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
      | FStar_Syntax_Syntax.Tm_arrow uu____71391 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____71407 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____71415 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____71417 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____71431 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____71451 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____71454 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____71454 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____71473;
             FStar_Syntax_Syntax.vars = uu____71474;_},uu____71475)
          ->
          let uu____71500 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____71500 FStar_Option.isNone
      | uu____71518 -> false
  
let (head_redex :
  FStar_SMTEncoding_Env.env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____71532 =
        let uu____71533 = FStar_Syntax_Util.un_uinst t  in
        uu____71533.FStar_Syntax_Syntax.n  in
      match uu____71532 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____71537,uu____71538,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___630_71563  ->
                  match uu___630_71563 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____71566 -> false)
               rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____71569 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____71569 FStar_Option.isSome
      | uu____71587 -> false
  
let (whnf :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____71600 = head_normal env t  in
      if uu____71600
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
    let uu____71622 =
      let uu____71623 = FStar_Syntax_Syntax.null_binder t  in [uu____71623]
       in
    let uu____71642 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    FStar_Syntax_Util.abs uu____71622 uu____71642
      FStar_Pervasives_Native.None
  
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
                let uu____71664 = FStar_SMTEncoding_Term.fv_sort var  in
                match uu____71664 with
                | FStar_SMTEncoding_Term.Fuel_sort  ->
                    let uu____71665 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____71665
                | s ->
                    let uu____71668 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____71668) e)
  
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
          let uu____71724 =
            let uu____71730 =
              let uu____71732 = FStar_Util.string_of_int arity  in
              let uu____71734 = FStar_Util.string_of_int n_args  in
              FStar_Util.format3
                "Head symbol %s expects at least %s arguments; got only %s"
                head1 uu____71732 uu____71734
               in
            (FStar_Errors.Fatal_SMTEncodingArityMismatch, uu____71730)  in
          FStar_Errors.raise_error uu____71724 rng
  
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
                  (let uu____71793 = FStar_Util.first_N arity args  in
                   match uu____71793 with
                   | (args1,rest) ->
                       let head3 =
                         FStar_SMTEncoding_Util.mkApp' (head2, args1)  in
                       mk_Apply_args head3 rest)
                else
                  (let uu____71817 =
                     FStar_SMTEncoding_Term.op_to_string head2  in
                   raise_arity_mismatch uu____71817 arity n_args rng)
  
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
          let uu____71844 = FStar_SMTEncoding_Env.force_thunk fvb  in
          mk_Apply_args uu____71844 args
        else
          maybe_curry_app rng
            (FStar_Util.Inl
               (FStar_SMTEncoding_Term.Var (fvb.FStar_SMTEncoding_Env.smt_id)))
            fvb.FStar_SMTEncoding_Env.smt_arity args
  
let (is_app : FStar_SMTEncoding_Term.op -> Prims.bool) =
  fun uu___631_71853  ->
    match uu___631_71853 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____71859 -> false
  
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
                       FStar_SMTEncoding_Term.freevars = uu____71907;
                       FStar_SMTEncoding_Term.rng = uu____71908;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____71939) ->
              let uu____71949 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____71966 -> false) args (FStar_List.rev xs))
                 in
              if uu____71949
              then FStar_SMTEncoding_Env.tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____71973,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t  in
              let uu____71977 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____71985 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars
                           in
                        Prims.op_Negation uu____71985))
                 in
              if uu____71977
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____71992 -> FStar_Pervasives_Native.None  in
        check_partial_applications body (FStar_List.rev vars)
  
let check_pattern_vars :
  'Auu____72010 'Auu____72011 .
    FStar_SMTEncoding_Env.env_t ->
      (FStar_Syntax_Syntax.bv * 'Auu____72010) Prims.list ->
        (FStar_Syntax_Syntax.term * 'Auu____72011) Prims.list -> unit
  =
  fun env  ->
    fun vars  ->
      fun pats  ->
        let pats1 =
          FStar_All.pipe_right pats
            (FStar_List.map
               (fun uu____72069  ->
                  match uu____72069 with
                  | (x,uu____72075) ->
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
              let uu____72083 = FStar_Syntax_Free.names hd1  in
              FStar_List.fold_left
                (fun out  ->
                   fun x  ->
                     let uu____72095 = FStar_Syntax_Free.names x  in
                     FStar_Util.set_union out uu____72095) uu____72083 tl1
               in
            let uu____72098 =
              FStar_All.pipe_right vars
                (FStar_Util.find_opt
                   (fun uu____72125  ->
                      match uu____72125 with
                      | (b,uu____72132) ->
                          let uu____72133 = FStar_Util.set_mem b pat_vars  in
                          Prims.op_Negation uu____72133))
               in
            (match uu____72098 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some (x,uu____72140) ->
                 let pos =
                   FStar_List.fold_left
                     (fun out  ->
                        fun t  ->
                          FStar_Range.union_ranges out
                            t.FStar_Syntax_Syntax.pos)
                     hd1.FStar_Syntax_Syntax.pos tl1
                    in
                 let uu____72154 =
                   let uu____72160 =
                     let uu____72162 = FStar_Syntax_Print.bv_to_string x  in
                     FStar_Util.format1
                       "SMT pattern misses at least one bound variable: %s"
                       uu____72162
                      in
                   (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                     uu____72160)
                    in
                 FStar_Errors.log_issue pos uu____72154)
  
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
        | FStar_Syntax_Syntax.Tm_arrow uu____72448 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____72463 ->
            let uu____72470 = FStar_Syntax_Util.unrefine t1  in
            aux true uu____72470
        | uu____72472 ->
            if norm1
            then let uu____72474 = whnf env t1  in aux false uu____72474
            else
              (let uu____72478 =
                 let uu____72480 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let uu____72482 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____72480 uu____72482
                  in
               failwith uu____72478)
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
    | FStar_Syntax_Syntax.Tm_refine (bv,uu____72524) ->
        let uu____72529 =
          curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort  in
        (match uu____72529 with
         | (args,res) ->
             (match args with
              | [] ->
                  let uu____72550 = FStar_Syntax_Syntax.mk_Total k1  in
                  ([], uu____72550)
              | uu____72557 -> (args, res)))
    | uu____72558 ->
        let uu____72559 = FStar_Syntax_Syntax.mk_Total k1  in
        ([], uu____72559)
  
let is_arithmetic_primitive :
  'Auu____72573 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____72573 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____72596::uu____72597::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____72601::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____72604 -> false
  
let (isInteger : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____72635 -> false
  
let (getInteger : FStar_Syntax_Syntax.term' -> Prims.int) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____72658 -> failwith "Expected an Integer term"
  
let is_BitVector_primitive :
  'Auu____72668 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____72668)
        Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____72710)::uu____72711::uu____72712::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____72763)::uu____72764::[]) ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____72801 -> false
  
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
          let uu____73125 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue  in
          (uu____73125, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____73127 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse  in
          (uu____73127, [])
      | FStar_Const.Const_char c1 ->
          let uu____73130 =
            let uu____73131 =
              let uu____73139 =
                let uu____73142 =
                  let uu____73143 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1)
                     in
                  FStar_SMTEncoding_Term.boxInt uu____73143  in
                [uu____73142]  in
              ("FStar.Char.__char_of_int", uu____73139)  in
            FStar_SMTEncoding_Util.mkApp uu____73131  in
          (uu____73130, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____73161 =
            let uu____73162 = FStar_SMTEncoding_Util.mkInteger i  in
            FStar_SMTEncoding_Term.boxInt uu____73162  in
          (uu____73161, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.FStar_SMTEncoding_Env.tcenv).FStar_TypeChecker_Env.dsenv
              repr sw FStar_Range.dummyRange
             in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____73183) ->
          let uu____73186 =
            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.string_const s
             in
          (uu____73186, [])
      | FStar_Const.Const_range uu____73187 ->
          let uu____73188 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          (uu____73188, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | FStar_Const.Const_real r ->
          let uu____73191 =
            let uu____73192 = FStar_SMTEncoding_Util.mkReal r  in
            FStar_SMTEncoding_Term.boxReal uu____73192  in
          (uu____73191, [])
      | c1 ->
          let uu____73194 =
            let uu____73196 = FStar_Syntax_Print.const_to_string c1  in
            FStar_Util.format1 "Unhandled constant: %s" uu____73196  in
          failwith uu____73194

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
        (let uu____73225 =
           FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
             FStar_Options.Medium
            in
         if uu____73225
         then
           let uu____73228 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____73228
         else ());
        (let uu____73234 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____73316  ->
                   fun b  ->
                     match uu____73316 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____73381 =
                           let x = FStar_Pervasives_Native.fst b  in
                           let uu____73397 =
                             FStar_SMTEncoding_Env.gen_term_var env1 x  in
                           match uu____73397 with
                           | (xxsym,xx,env') ->
                               let uu____73422 =
                                 let uu____73427 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____73427 env1
                                   xx
                                  in
                               (match uu____73422 with
                                | (guard_x_t,decls') ->
                                    let uu____73442 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xxsym,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    (uu____73442, guard_x_t, env', decls', x))
                            in
                         (match uu____73381 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____73234 with
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
          let uu____73542 = encode_term t env  in
          match uu____73542 with
          | (t1,decls) ->
              let uu____73553 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____73553, decls)

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
          let uu____73564 = encode_term t env  in
          match uu____73564 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____73579 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____73579, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____73581 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____73581, decls))

and (encode_arith_term :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____73587 = encode_args args_e env  in
        match uu____73587 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____73606 -> failwith "Impossible"  in
            let unary unbox arg_tms1 =
              let uu____73628 = FStar_List.hd arg_tms1  in unbox uu____73628
               in
            let binary unbox arg_tms1 =
              let uu____73653 =
                let uu____73654 = FStar_List.hd arg_tms1  in
                unbox uu____73654  in
              let uu____73655 =
                let uu____73656 =
                  let uu____73657 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____73657  in
                unbox uu____73656  in
              (uu____73653, uu____73655)  in
            let mk_default uu____73665 =
              let uu____73666 =
                FStar_SMTEncoding_Env.lookup_free_var_sym env
                  head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____73666 with
              | (fname,fuel_args,arity) ->
                  let args = FStar_List.append fuel_args arg_tms  in
                  maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity
                    args
               in
            let mk_l box op mk_args ts =
              let uu____73755 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____73755
              then
                let uu____73758 =
                  let uu____73759 = mk_args ts  in op uu____73759  in
                FStar_All.pipe_right uu____73758 box
              else mk_default ()  in
            let mk_nl box unbox nm op ts =
              let uu____73817 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____73817
              then
                let uu____73820 = binary unbox ts  in
                match uu____73820 with
                | (t1,t2) ->
                    let uu____73827 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____73827 box
              else
                (let uu____73833 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____73833
                 then
                   let uu____73836 =
                     let uu____73837 = binary unbox ts  in op uu____73837  in
                   FStar_All.pipe_right uu____73836 box
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
            let uu____74272 =
              let uu____74282 =
                FStar_List.tryFind
                  (fun uu____74306  ->
                     match uu____74306 with
                     | (l,uu____74317) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____74282 FStar_Util.must  in
            (match uu____74272 with
             | (uu____74361,op) ->
                 let uu____74373 = op arg_tms  in (uu____74373, decls))

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
        let uu____74389 = FStar_List.hd args_e  in
        match uu____74389 with
        | (tm_sz,uu____74405) ->
            let uu____74414 = uu____74389  in
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let t_decls1 = FStar_SMTEncoding_Term.mkBvConstructor sz  in
              FStar_SMTEncoding_Term.mk_decls "" sz_key t_decls1 []  in
            let uu____74425 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____74451::(sz_arg,uu____74453)::uu____74454::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____74521 =
                    let uu____74522 = FStar_List.tail args_e  in
                    FStar_List.tail uu____74522  in
                  let uu____74549 =
                    let uu____74553 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____74553  in
                  (uu____74521, uu____74549)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____74560::(sz_arg,uu____74562)::uu____74563::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____74630 =
                    let uu____74632 =
                      FStar_Syntax_Print.term_to_string sz_arg  in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____74632
                     in
                  failwith uu____74630
              | uu____74642 ->
                  let uu____74657 = FStar_List.tail args_e  in
                  (uu____74657, FStar_Pervasives_Native.None)
               in
            (match uu____74425 with
             | (arg_tms,ext_sz) ->
                 let uu____74684 = encode_args arg_tms env  in
                 (match uu____74684 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____74705 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____74717 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____74717  in
                      let unary_arith arg_tms2 =
                        let uu____74728 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____74728  in
                      let binary arg_tms2 =
                        let uu____74743 =
                          let uu____74744 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____74744
                           in
                        let uu____74745 =
                          let uu____74746 =
                            let uu____74747 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____74747  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____74746
                           in
                        (uu____74743, uu____74745)  in
                      let binary_arith arg_tms2 =
                        let uu____74764 =
                          let uu____74765 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____74765
                           in
                        let uu____74766 =
                          let uu____74767 =
                            let uu____74768 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____74768  in
                          FStar_SMTEncoding_Term.unboxInt uu____74767  in
                        (uu____74764, uu____74766)  in
                      let mk_bv op mk_args resBox ts =
                        let uu____74826 =
                          let uu____74827 = mk_args ts  in op uu____74827  in
                        FStar_All.pipe_right uu____74826 resBox  in
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
                        let uu____74959 =
                          let uu____74964 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____74964  in
                        let uu____74973 =
                          let uu____74978 =
                            let uu____74980 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____74980  in
                          FStar_SMTEncoding_Term.boxBitVec uu____74978  in
                        mk_bv uu____74959 unary uu____74973 arg_tms2  in
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
                      let uu____75220 =
                        let uu____75230 =
                          FStar_List.tryFind
                            (fun uu____75254  ->
                               match uu____75254 with
                               | (l,uu____75265) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____75230 FStar_Util.must  in
                      (match uu____75220 with
                       | (uu____75311,op) ->
                           let uu____75323 = op arg_tms1  in
                           (uu____75323, (FStar_List.append sz_decls decls)))))

and (encode_deeply_embedded_quantifier :
  FStar_Syntax_Syntax.term ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let env1 =
        let uu___1170_75333 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___1170_75333.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___1170_75333.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___1170_75333.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___1170_75333.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___1170_75333.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___1170_75333.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name =
            (uu___1170_75333.FStar_SMTEncoding_Env.use_zfuel_name);
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___1170_75333.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___1170_75333.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier = true;
          FStar_SMTEncoding_Env.global_cache =
            (uu___1170_75333.FStar_SMTEncoding_Env.global_cache)
        }  in
      let uu____75335 = encode_term t env1  in
      match uu____75335 with
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
               (uu____75361,{
                              FStar_SMTEncoding_Term.tm =
                                FStar_SMTEncoding_Term.FreeV uu____75362;
                              FStar_SMTEncoding_Term.freevars = uu____75363;
                              FStar_SMTEncoding_Term.rng = uu____75364;_}::
                {
                  FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV
                    uu____75365;
                  FStar_SMTEncoding_Term.freevars = uu____75366;
                  FStar_SMTEncoding_Term.rng = uu____75367;_}::[])
               ->
               (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                  (FStar_Errors.Warning_QuantifierWithoutPattern,
                    "Not encoding deeply embedded, unguarded quantifier to SMT");
                (tm, decls))
           | uu____75413 ->
               let uu____75414 = encode_formula t env1  in
               (match uu____75414 with
                | (phi,decls') ->
                    let interp =
                      match vars with
                      | [] ->
                          let uu____75434 =
                            let uu____75439 =
                              FStar_SMTEncoding_Term.mk_Valid tm  in
                            (uu____75439, phi)  in
                          FStar_SMTEncoding_Util.mkIff uu____75434
                      | uu____75440 ->
                          let uu____75441 =
                            let uu____75452 =
                              let uu____75453 =
                                let uu____75458 =
                                  FStar_SMTEncoding_Term.mk_Valid tm  in
                                (uu____75458, phi)  in
                              FStar_SMTEncoding_Util.mkIff uu____75453  in
                            ([[valid_tm]], vars, uu____75452)  in
                          FStar_SMTEncoding_Term.mkForall
                            t.FStar_Syntax_Syntax.pos uu____75441
                       in
                    let ax =
                      let uu____75468 =
                        let uu____75476 =
                          let uu____75478 =
                            FStar_Util.digest_of_string tkey_hash  in
                          Prims.op_Hat "l_quant_interp_" uu____75478  in
                        (interp,
                          (FStar_Pervasives_Native.Some
                             "Interpretation of deeply embedded quantifier"),
                          uu____75476)
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____75468  in
                    let uu____75484 =
                      let uu____75485 =
                        let uu____75488 =
                          FStar_SMTEncoding_Term.mk_decls "" tkey_hash 
                            [ax] (FStar_List.append decls decls')
                           in
                        FStar_List.append decls' uu____75488  in
                      FStar_List.append decls uu____75485  in
                    (tm, uu____75484)))

and (encode_term :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____75500 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____75500
       then
         let uu____75505 = FStar_Syntax_Print.tag_of_term t  in
         let uu____75507 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____75509 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____75505 uu____75507
           uu____75509
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____75518 ->
           let uu____75541 =
             let uu____75543 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____75546 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____75548 = FStar_Syntax_Print.term_to_string t0  in
             let uu____75550 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____75543
               uu____75546 uu____75548 uu____75550
              in
           failwith uu____75541
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____75557 =
             let uu____75559 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____75562 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____75564 = FStar_Syntax_Print.term_to_string t0  in
             let uu____75566 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____75559
               uu____75562 uu____75564 uu____75566
              in
           failwith uu____75557
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let e = FStar_Syntax_Util.unfold_lazy i  in
           ((let uu____75576 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____75576
             then
               let uu____75581 = FStar_Syntax_Print.term_to_string t0  in
               let uu____75583 = FStar_Syntax_Print.term_to_string e  in
               FStar_Util.print2 ">> Unfolded (%s) ~> (%s)\n" uu____75581
                 uu____75583
             else ());
            encode_term e env)
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____75589 =
             let uu____75591 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____75591
              in
           failwith uu____75589
       | FStar_Syntax_Syntax.Tm_ascribed (t1,(k,uu____75600),uu____75601) ->
           let uu____75650 =
             match k with
             | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
             | uu____75660 -> false  in
           if uu____75650
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t1 env
       | FStar_Syntax_Syntax.Tm_quoted (qt,uu____75678) ->
           let tv =
             let uu____75684 =
               let uu____75691 = FStar_Reflection_Basic.inspect_ln qt  in
               FStar_Syntax_Embeddings.embed
                 FStar_Reflection_Embeddings.e_term_view uu____75691
                in
             uu____75684 t.FStar_Syntax_Syntax.pos
               FStar_Pervasives_Native.None
               FStar_Syntax_Embeddings.id_norm_cb
              in
           ((let uu____75718 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____75718
             then
               let uu____75723 = FStar_Syntax_Print.term_to_string t0  in
               let uu____75725 = FStar_Syntax_Print.term_to_string tv  in
               FStar_Util.print2 ">> Inspected (%s) ~> (%s)\n" uu____75723
                 uu____75725
             else ());
            (let t1 =
               let uu____75733 =
                 let uu____75744 = FStar_Syntax_Syntax.as_arg tv  in
                 [uu____75744]  in
               FStar_Syntax_Util.mk_app
                 (FStar_Reflection_Data.refl_constant_term
                    FStar_Reflection_Data.fstar_refl_pack_ln) uu____75733
                in
             encode_term t1 env))
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_pattern uu____75770) ->
           encode_term t1
             (let uu___1242_75788 = env  in
              {
                FStar_SMTEncoding_Env.bvar_bindings =
                  (uu___1242_75788.FStar_SMTEncoding_Env.bvar_bindings);
                FStar_SMTEncoding_Env.fvar_bindings =
                  (uu___1242_75788.FStar_SMTEncoding_Env.fvar_bindings);
                FStar_SMTEncoding_Env.depth =
                  (uu___1242_75788.FStar_SMTEncoding_Env.depth);
                FStar_SMTEncoding_Env.tcenv =
                  (uu___1242_75788.FStar_SMTEncoding_Env.tcenv);
                FStar_SMTEncoding_Env.warn =
                  (uu___1242_75788.FStar_SMTEncoding_Env.warn);
                FStar_SMTEncoding_Env.nolabels =
                  (uu___1242_75788.FStar_SMTEncoding_Env.nolabels);
                FStar_SMTEncoding_Env.use_zfuel_name =
                  (uu___1242_75788.FStar_SMTEncoding_Env.use_zfuel_name);
                FStar_SMTEncoding_Env.encode_non_total_function_typ =
                  (uu___1242_75788.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                FStar_SMTEncoding_Env.current_module_name =
                  (uu___1242_75788.FStar_SMTEncoding_Env.current_module_name);
                FStar_SMTEncoding_Env.encoding_quantifier = false;
                FStar_SMTEncoding_Env.global_cache =
                  (uu___1242_75788.FStar_SMTEncoding_Env.global_cache)
              })
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____75791) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = FStar_SMTEncoding_Env.lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____75799 = head_redex env t  in
           if uu____75799
           then let uu____75806 = whnf env t  in encode_term uu____75806 env
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
              let uu____75813 =
                if
                  fvb.FStar_SMTEncoding_Env.smt_arity > (Prims.parse_int "0")
                then
                  match tok.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.FreeV uu____75837 ->
                      let sym_name =
                        let uu____75848 =
                          FStar_Util.digest_of_string tkey_hash  in
                        Prims.op_Hat "@kick_partial_app_" uu____75848  in
                      let uu____75851 =
                        let uu____75854 =
                          let uu____75855 =
                            let uu____75863 =
                              FStar_SMTEncoding_Term.kick_partial_app tok  in
                            (uu____75863,
                              (FStar_Pervasives_Native.Some
                                 "kick_partial_app"), sym_name)
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____75855  in
                        [uu____75854]  in
                      (uu____75851, sym_name)
                  | FStar_SMTEncoding_Term.App (uu____75870,[]) ->
                      let sym_name =
                        let uu____75875 =
                          FStar_Util.digest_of_string tkey_hash  in
                        Prims.op_Hat "@kick_partial_app_" uu____75875  in
                      let uu____75878 =
                        let uu____75881 =
                          let uu____75882 =
                            let uu____75890 =
                              FStar_SMTEncoding_Term.kick_partial_app tok  in
                            (uu____75890,
                              (FStar_Pervasives_Native.Some
                                 "kick_partial_app"), sym_name)
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____75882  in
                        [uu____75881]  in
                      (uu____75878, sym_name)
                  | uu____75897 -> ([], "")
                else ([], "")  in
              match uu____75813 with
              | (aux_decls,sym_name) ->
                  let uu____75920 =
                    if aux_decls = []
                    then
                      FStar_All.pipe_right []
                        FStar_SMTEncoding_Term.mk_decls_trivial
                    else
                      FStar_SMTEncoding_Term.mk_decls sym_name tkey_hash
                        aux_decls []
                     in
                  (tok, uu____75920))
       | FStar_Syntax_Syntax.Tm_type uu____75928 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____75930) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.FStar_SMTEncoding_Env.current_module_name
              in
           let uu____75960 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____75960 with
            | (binders1,res) ->
                let uu____75971 =
                  (env.FStar_SMTEncoding_Env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____75971
                then
                  let uu____75978 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____75978 with
                   | (vars,guards,env',decls,uu____76003) ->
                       let fsym =
                         let uu____76017 =
                           let uu____76023 =
                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                               module_name "f"
                              in
                           (uu____76023, FStar_SMTEncoding_Term.Term_sort)
                            in
                         FStar_SMTEncoding_Term.mk_fv uu____76017  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____76029 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___1296_76038 =
                              env.FStar_SMTEncoding_Env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___1296_76038.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___1296_76038.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___1296_76038.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___1296_76038.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___1296_76038.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___1296_76038.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___1296_76038.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___1296_76038.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___1296_76038.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___1296_76038.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___1296_76038.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___1296_76038.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___1296_76038.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___1296_76038.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___1296_76038.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___1296_76038.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___1296_76038.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___1296_76038.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___1296_76038.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___1296_76038.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___1296_76038.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___1296_76038.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___1296_76038.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___1296_76038.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___1296_76038.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___1296_76038.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___1296_76038.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___1296_76038.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___1296_76038.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___1296_76038.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___1296_76038.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___1296_76038.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___1296_76038.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___1296_76038.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___1296_76038.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___1296_76038.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___1296_76038.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___1296_76038.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___1296_76038.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___1296_76038.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___1296_76038.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___1296_76038.FStar_TypeChecker_Env.nbe)
                            }) res
                          in
                       (match uu____76029 with
                        | (pre_opt,res_t) ->
                            let uu____76050 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____76050 with
                             | (res_pred,decls') ->
                                 let uu____76061 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____76074 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____76074, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____76078 =
                                         encode_formula pre env'  in
                                       (match uu____76078 with
                                        | (guard,decls0) ->
                                            let uu____76091 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____76091, decls0))
                                    in
                                 (match uu____76061 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____76105 =
                                          let uu____76116 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____76116)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t.FStar_Syntax_Syntax.pos
                                          uu____76105
                                         in
                                      let cvars =
                                        let uu____76136 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____76136
                                          (FStar_List.filter
                                             (fun x  ->
                                                let uu____76155 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    x
                                                   in
                                                let uu____76157 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    fsym
                                                   in
                                                uu____76155 <> uu____76157))
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
                                        let uu____76179 =
                                          FStar_Util.digest_of_string
                                            tkey_hash
                                           in
                                        Prims.op_Hat "Tm_arrow_" uu____76179
                                         in
                                      let cvar_sorts =
                                        FStar_List.map
                                          FStar_SMTEncoding_Term.fv_sort
                                          cvars
                                         in
                                      let caption =
                                        let uu____76194 =
                                          FStar_Options.log_queries ()  in
                                        if uu____76194
                                        then
                                          let uu____76197 =
                                            let uu____76199 =
                                              FStar_TypeChecker_Normalize.term_to_string
                                                env.FStar_SMTEncoding_Env.tcenv
                                                t0
                                               in
                                            FStar_Util.replace_char
                                              uu____76199 10 32
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____76197
                                        else FStar_Pervasives_Native.None  in
                                      let tdecl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (tsym, cvar_sorts,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            caption)
                                         in
                                      let t1 =
                                        let uu____76212 =
                                          let uu____76220 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              cvars
                                             in
                                          (tsym, uu____76220)  in
                                        FStar_SMTEncoding_Util.mkApp
                                          uu____76212
                                         in
                                      let t_has_kind =
                                        FStar_SMTEncoding_Term.mk_HasType t1
                                          FStar_SMTEncoding_Term.mk_Term_type
                                         in
                                      let k_assumption =
                                        let a_name =
                                          Prims.op_Hat "kinding_" tsym  in
                                        let uu____76239 =
                                          let uu____76247 =
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              ([[t_has_kind]], cvars,
                                                t_has_kind)
                                             in
                                          (uu____76247,
                                            (FStar_Pervasives_Native.Some
                                               a_name), a_name)
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____76239
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
                                        let uu____76264 =
                                          let uu____76272 =
                                            let uu____76273 =
                                              let uu____76284 =
                                                let uu____76285 =
                                                  let uu____76290 =
                                                    let uu____76291 =
                                                      FStar_SMTEncoding_Term.mk_PreType
                                                        f
                                                       in
                                                    FStar_SMTEncoding_Term.mk_tester
                                                      "Tm_arrow" uu____76291
                                                     in
                                                  (f_has_t, uu____76290)  in
                                                FStar_SMTEncoding_Util.mkImp
                                                  uu____76285
                                                 in
                                              ([[f_has_t]], (fsym :: cvars),
                                                uu____76284)
                                               in
                                            let uu____76309 =
                                              mkForall_fuel module_name
                                                t0.FStar_Syntax_Syntax.pos
                                               in
                                            uu____76309 uu____76273  in
                                          (uu____76272,
                                            (FStar_Pervasives_Native.Some
                                               "pre-typing for functions"),
                                            (Prims.op_Hat module_name
                                               (Prims.op_Hat "_" a_name)))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____76264
                                         in
                                      let t_interp1 =
                                        let a_name =
                                          Prims.op_Hat "interpretation_" tsym
                                           in
                                        let uu____76332 =
                                          let uu____76340 =
                                            let uu____76341 =
                                              let uu____76352 =
                                                FStar_SMTEncoding_Util.mkIff
                                                  (f_has_t_z, t_interp)
                                                 in
                                              ([[f_has_t_z]], (fsym ::
                                                cvars), uu____76352)
                                               in
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              uu____76341
                                             in
                                          (uu____76340,
                                            (FStar_Pervasives_Native.Some
                                               a_name),
                                            (Prims.op_Hat module_name
                                               (Prims.op_Hat "_" a_name)))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____76332
                                         in
                                      let t_decls1 =
                                        [tdecl;
                                        k_assumption;
                                        pre_typing;
                                        t_interp1]  in
                                      let uu____76375 =
                                        let uu____76376 =
                                          let uu____76379 =
                                            let uu____76382 =
                                              FStar_SMTEncoding_Term.mk_decls
                                                tsym tkey_hash t_decls1
                                                (FStar_List.append decls
                                                   (FStar_List.append decls'
                                                      guard_decls))
                                               in
                                            FStar_List.append guard_decls
                                              uu____76382
                                             in
                                          FStar_List.append decls'
                                            uu____76379
                                           in
                                        FStar_List.append decls uu____76376
                                         in
                                      (t1, uu____76375)))))
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
                     let uu____76403 =
                       let uu____76411 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____76411,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"), a_name)
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____76403  in
                   let fsym =
                     FStar_SMTEncoding_Term.mk_fv
                       ("f", FStar_SMTEncoding_Term.Term_sort)
                      in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.op_Hat "pre_typing_" tsym  in
                     let uu____76424 =
                       let uu____76432 =
                         let uu____76433 =
                           let uu____76444 =
                             let uu____76445 =
                               let uu____76450 =
                                 let uu____76451 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____76451
                                  in
                               (f_has_t, uu____76450)  in
                             FStar_SMTEncoding_Util.mkImp uu____76445  in
                           ([[f_has_t]], [fsym], uu____76444)  in
                         let uu____76477 =
                           mkForall_fuel module_name
                             t0.FStar_Syntax_Syntax.pos
                            in
                         uu____76477 uu____76433  in
                       (uu____76432, (FStar_Pervasives_Native.Some a_name),
                         a_name)
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____76424  in
                   let uu____76494 =
                     FStar_All.pipe_right [tdecl; t_kinding; t_interp]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                      in
                   (t1, uu____76494)))
       | FStar_Syntax_Syntax.Tm_refine uu____76497 ->
           let uu____76504 =
             let uu____76509 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Env.Weak;
                 FStar_TypeChecker_Env.HNF;
                 FStar_TypeChecker_Env.EraseUniverses]
                 env.FStar_SMTEncoding_Env.tcenv t0
                in
             match uu____76509 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____76516;
                 FStar_Syntax_Syntax.vars = uu____76517;_} ->
                 let uu____76524 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____76524 with
                  | (b,f1) ->
                      let uu____76549 =
                        let uu____76550 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____76550  in
                      (uu____76549, f1))
             | uu____76565 -> failwith "impossible"  in
           (match uu____76504 with
            | (x,f) ->
                let uu____76577 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____76577 with
                 | (base_t,decls) ->
                     let uu____76588 =
                       FStar_SMTEncoding_Env.gen_term_var env x  in
                     (match uu____76588 with
                      | (x1,xtm,env') ->
                          let uu____76605 = encode_formula f env'  in
                          (match uu____76605 with
                           | (refinement,decls') ->
                               let uu____76616 =
                                 FStar_SMTEncoding_Env.fresh_fvar
                                   env.FStar_SMTEncoding_Env.current_module_name
                                   "f" FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____76616 with
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
                                      let uu____76644 =
                                        let uu____76655 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____76666 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____76655
                                          uu____76666
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____76644
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun y  ->
                                              (let uu____76720 =
                                                 FStar_SMTEncoding_Term.fv_name
                                                   y
                                                  in
                                               uu____76720 <> x1) &&
                                                (let uu____76724 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     y
                                                    in
                                                 uu____76724 <> fsym)))
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
                                      let uu____76760 =
                                        FStar_Util.digest_of_string tkey_hash
                                         in
                                      Prims.op_Hat "Tm_refine_" uu____76760
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
                                      let uu____76780 =
                                        let uu____76788 =
                                          FStar_List.map
                                            FStar_SMTEncoding_Util.mkFreeV
                                            cvars1
                                           in
                                        (tsym, uu____76788)  in
                                      FStar_SMTEncoding_Util.mkApp
                                        uu____76780
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
                                      let uu____76808 =
                                        let uu____76816 =
                                          let uu____76817 =
                                            let uu____76828 =
                                              FStar_SMTEncoding_Util.mkIff
                                                (t_haseq_ref, t_haseq_base)
                                               in
                                            ([[t_haseq_ref]], cvars1,
                                              uu____76828)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            t0.FStar_Syntax_Syntax.pos
                                            uu____76817
                                           in
                                        (uu____76816,
                                          (FStar_Pervasives_Native.Some
                                             (Prims.op_Hat "haseq for " tsym)),
                                          (Prims.op_Hat "haseq" tsym))
                                         in
                                      FStar_SMTEncoding_Util.mkAssume
                                        uu____76808
                                       in
                                    let t_kinding =
                                      let uu____76842 =
                                        let uu____76850 =
                                          FStar_SMTEncoding_Term.mkForall
                                            t0.FStar_Syntax_Syntax.pos
                                            ([[t_has_kind]], cvars1,
                                              t_has_kind)
                                           in
                                        (uu____76850,
                                          (FStar_Pervasives_Native.Some
                                             "refinement kinding"),
                                          (Prims.op_Hat "refinement_kinding_"
                                             tsym))
                                         in
                                      FStar_SMTEncoding_Util.mkAssume
                                        uu____76842
                                       in
                                    let t_interp =
                                      let uu____76864 =
                                        let uu____76872 =
                                          let uu____76873 =
                                            let uu____76884 =
                                              FStar_SMTEncoding_Util.mkIff
                                                (x_has_t, encoding)
                                               in
                                            ([[x_has_t]], (ffv :: xfv ::
                                              cvars1), uu____76884)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            t0.FStar_Syntax_Syntax.pos
                                            uu____76873
                                           in
                                        (uu____76872,
                                          (FStar_Pervasives_Native.Some
                                             "refinement_interpretation"),
                                          (Prims.op_Hat
                                             "refinement_interpretation_"
                                             tsym))
                                         in
                                      FStar_SMTEncoding_Util.mkAssume
                                        uu____76864
                                       in
                                    let t_decls1 =
                                      [tdecl; t_kinding; t_interp; t_haseq1]
                                       in
                                    let uu____76916 =
                                      let uu____76917 =
                                        let uu____76920 =
                                          FStar_SMTEncoding_Term.mk_decls
                                            tsym tkey_hash t_decls1
                                            (FStar_List.append decls decls')
                                           in
                                        FStar_List.append decls' uu____76920
                                         in
                                      FStar_List.append decls uu____76917  in
                                    (t1, uu____76916))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,uu____76924) ->
           let ttm =
             let uu____76942 =
               FStar_Syntax_Unionfind.uvar_id
                 uv.FStar_Syntax_Syntax.ctx_uvar_head
                in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____76942  in
           let uu____76944 =
             encode_term_pred FStar_Pervasives_Native.None
               uv.FStar_Syntax_Syntax.ctx_uvar_typ env ttm
              in
           (match uu____76944 with
            | (t_has_k,decls) ->
                let d =
                  let uu____76956 =
                    let uu____76964 =
                      let uu____76966 =
                        let uu____76968 =
                          let uu____76970 =
                            FStar_Syntax_Unionfind.uvar_id
                              uv.FStar_Syntax_Syntax.ctx_uvar_head
                             in
                          FStar_Util.string_of_int uu____76970  in
                        FStar_Util.format1 "uvar_typing_%s" uu____76968  in
                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                        uu____76966
                       in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____76964)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____76956  in
                let uu____76976 =
                  let uu____76977 =
                    FStar_All.pipe_right [d]
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append decls uu____76977  in
                (ttm, uu____76976))
       | FStar_Syntax_Syntax.Tm_app uu____76984 ->
           let uu____77001 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____77001 with
            | (head1,args_e) ->
                let uu____77048 =
                  let uu____77063 =
                    let uu____77064 = FStar_Syntax_Subst.compress head1  in
                    uu____77064.FStar_Syntax_Syntax.n  in
                  (uu____77063, args_e)  in
                (match uu____77048 with
                 | uu____77081 when head_redex env head1 ->
                     let uu____77096 = whnf env t  in
                     encode_term uu____77096 env
                 | uu____77097 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____77120 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_fvar fv,uu____77138) when
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
                       FStar_Syntax_Syntax.pos = uu____77160;
                       FStar_Syntax_Syntax.vars = uu____77161;_},uu____77162),uu____77163)
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
                       FStar_Syntax_Syntax.pos = uu____77189;
                       FStar_Syntax_Syntax.vars = uu____77190;_},uu____77191),
                    (v0,uu____77193)::(v1,uu____77195)::(v2,uu____77197)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____77268 = encode_term v0 env  in
                     (match uu____77268 with
                      | (v01,decls0) ->
                          let uu____77279 = encode_term v1 env  in
                          (match uu____77279 with
                           | (v11,decls1) ->
                               let uu____77290 = encode_term v2 env  in
                               (match uu____77290 with
                                | (v21,decls2) ->
                                    let uu____77301 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____77301,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(v0,uu____77304)::(v1,uu____77306)::(v2,uu____77308)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____77375 = encode_term v0 env  in
                     (match uu____77375 with
                      | (v01,decls0) ->
                          let uu____77386 = encode_term v1 env  in
                          (match uu____77386 with
                           | (v11,decls1) ->
                               let uu____77397 = encode_term v2 env  in
                               (match uu____77397 with
                                | (v21,decls2) ->
                                    let uu____77408 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____77408,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____77410)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____77446)::(rng,uu____77448)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____77499) ->
                     let e0 =
                       let uu____77521 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg
                         env.FStar_SMTEncoding_Env.tcenv head1 uu____77521
                        in
                     ((let uu____77531 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug
                              env.FStar_SMTEncoding_Env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____77531
                       then
                         let uu____77536 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____77536
                       else ());
                      (let e =
                         let uu____77544 =
                           let uu____77549 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____77550 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____77549
                             uu____77550
                            in
                         uu____77544 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____77561),(arg,uu____77563)::[]) ->
                     encode_term arg env
                 | uu____77598 ->
                     let uu____77613 = encode_args args_e env  in
                     (match uu____77613 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____77674 = encode_term head1 env  in
                            match uu____77674 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____77746 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____77746 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____77844  ->
                                                 fun uu____77845  ->
                                                   match (uu____77844,
                                                           uu____77845)
                                                   with
                                                   | ((bv,uu____77875),
                                                      (a,uu____77877)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____77907 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____77907
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____77908 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm
                                             in
                                          (match uu____77908 with
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
                                                 let uu____77925 =
                                                   let uu____77933 =
                                                     FStar_SMTEncoding_Term.mkForall
                                                       t0.FStar_Syntax_Syntax.pos
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____77942 =
                                                     let uu____77944 =
                                                       let uu____77946 =
                                                         FStar_SMTEncoding_Term.hash_of_term
                                                           app_tm
                                                          in
                                                       FStar_Util.digest_of_string
                                                         uu____77946
                                                        in
                                                     Prims.op_Hat
                                                       "partial_app_typing_"
                                                       uu____77944
                                                      in
                                                   (uu____77933,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____77942)
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____77925
                                                  in
                                               let uu____77952 =
                                                 let uu____77955 =
                                                   let uu____77958 =
                                                     let uu____77961 =
                                                       FStar_SMTEncoding_Term.mk_decls
                                                         "" tkey_hash
                                                         [e_typing]
                                                         (FStar_List.append
                                                            decls
                                                            (FStar_List.append
                                                               decls' decls''))
                                                        in
                                                     FStar_List.append
                                                       decls'' uu____77961
                                                      in
                                                   FStar_List.append decls'
                                                     uu____77958
                                                    in
                                                 FStar_List.append decls
                                                   uu____77955
                                                  in
                                               (app_tm, uu____77952))))
                             in
                          let encode_full_app fv =
                            let uu____77981 =
                              FStar_SMTEncoding_Env.lookup_free_var_sym env
                                fv
                               in
                            match uu____77981 with
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
                                   FStar_Syntax_Syntax.pos = uu____78024;
                                   FStar_Syntax_Syntax.vars = uu____78025;_},uu____78026)
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
                                   FStar_Syntax_Syntax.pos = uu____78033;
                                   FStar_Syntax_Syntax.vars = uu____78034;_},uu____78035)
                                ->
                                let uu____78040 =
                                  let uu____78041 =
                                    let uu____78046 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____78046
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____78041
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____78040
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____78076 =
                                  let uu____78077 =
                                    let uu____78082 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____78082
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____78077
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____78076
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____78111,(FStar_Util.Inl t1,uu____78113),uu____78114)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____78161,(FStar_Util.Inr c,uu____78163),uu____78164)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____78211 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____78232 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Env.Weak;
                                     FStar_TypeChecker_Env.HNF;
                                     FStar_TypeChecker_Env.EraseUniverses]
                                     env.FStar_SMTEncoding_Env.tcenv
                                     head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____78232
                                  in
                               let uu____78233 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____78233 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____78249;
                                            FStar_Syntax_Syntax.vars =
                                              uu____78250;_},uu____78251)
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
                                     | uu____78269 ->
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
           let uu____78348 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____78348 with
            | (bs1,body1,opening) ->
                let fallback uu____78371 =
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
                  let uu____78381 =
                    let uu____78382 =
                      FStar_SMTEncoding_Term.mk_fv
                        (f, FStar_SMTEncoding_Term.Term_sort)
                       in
                    FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV
                      uu____78382
                     in
                  let uu____78384 =
                    FStar_All.pipe_right [decl]
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  (uu____78381, uu____78384)  in
                let is_impure rc =
                  let uu____78394 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                      env.FStar_SMTEncoding_Env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____78394 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____78409 =
                          let uu____78422 =
                            FStar_TypeChecker_Env.get_range
                              env.FStar_SMTEncoding_Env.tcenv
                             in
                          FStar_TypeChecker_Util.new_implicit_var
                            "SMTEncoding codomain" uu____78422
                            env.FStar_SMTEncoding_Env.tcenv
                            FStar_Syntax_Util.ktype0
                           in
                        (match uu____78409 with
                         | (t1,uu____78425,uu____78426) -> t1)
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  let uu____78444 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                     in
                  if uu____78444
                  then
                    let uu____78449 = FStar_Syntax_Syntax.mk_Total res_typ
                       in
                    FStar_Pervasives_Native.Some uu____78449
                  else
                    (let uu____78452 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid
                        in
                     if uu____78452
                     then
                       let uu____78457 =
                         FStar_Syntax_Syntax.mk_GTotal res_typ  in
                       FStar_Pervasives_Native.Some uu____78457
                     else FStar_Pervasives_Native.None)
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____78465 =
                         let uu____78471 =
                           let uu____78473 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____78473
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____78471)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____78465);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____78478 =
                       (is_impure rc) &&
                         (let uu____78481 =
                            FStar_TypeChecker_Env.is_reifiable_rc
                              env.FStar_SMTEncoding_Env.tcenv rc
                             in
                          Prims.op_Negation uu____78481)
                        in
                     if uu____78478
                     then fallback ()
                     else
                       (let uu____78490 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____78490 with
                        | (vars,guards,envbody,decls,uu____78515) ->
                            let body2 =
                              let uu____78529 =
                                FStar_TypeChecker_Env.is_reifiable_rc
                                  env.FStar_SMTEncoding_Env.tcenv rc
                                 in
                              if uu____78529
                              then
                                FStar_TypeChecker_Util.reify_body
                                  env.FStar_SMTEncoding_Env.tcenv body1
                              else body1  in
                            let uu____78534 = encode_term body2 envbody  in
                            (match uu____78534 with
                             | (body3,decls') ->
                                 let uu____78545 =
                                   let uu____78554 = codomain_eff rc  in
                                   match uu____78554 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____78573 = encode_term tfun env
                                          in
                                       (match uu____78573 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____78545 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____78607 =
                                          let uu____78618 =
                                            let uu____78619 =
                                              let uu____78624 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____78624, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____78619
                                             in
                                          ([], vars, uu____78618)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t0.FStar_Syntax_Syntax.pos
                                          uu____78607
                                         in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body
                                         in
                                      let uu____78632 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            (cvars, key_body)
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____78648 =
                                              let uu____78651 =
                                                let uu____78662 =
                                                  FStar_SMTEncoding_Term.free_variables
                                                    t1
                                                   in
                                                FStar_List.append uu____78662
                                                  cvars
                                                 in
                                              FStar_Util.remove_dups
                                                FStar_SMTEncoding_Term.fv_eq
                                                uu____78651
                                               in
                                            let uu____78689 =
                                              FStar_SMTEncoding_Util.mkAnd
                                                (key_body, t1)
                                               in
                                            (uu____78648, uu____78689)
                                         in
                                      (match uu____78632 with
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
                                           let uu____78711 =
                                             is_an_eta_expansion env vars
                                               body3
                                              in
                                           (match uu____78711 with
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
                                                  let uu____78727 =
                                                    FStar_Util.digest_of_string
                                                      tkey_hash
                                                     in
                                                  Prims.op_Hat "Tm_abs_"
                                                    uu____78727
                                                   in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None)
                                                   in
                                                let f =
                                                  let uu____78736 =
                                                    let uu____78744 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    (fsym, uu____78744)  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____78736
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
                                                      let uu____78761 =
                                                        let uu____78762 =
                                                          let uu____78770 =
                                                            FStar_SMTEncoding_Term.mkForall
                                                              t0.FStar_Syntax_Syntax.pos
                                                              ([[f]], cvars1,
                                                                f_has_t)
                                                             in
                                                          (uu____78770,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name)
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____78762
                                                         in
                                                      [uu____78761]
                                                   in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.op_Hat
                                                      "interpretation_" fsym
                                                     in
                                                  let uu____78785 =
                                                    let uu____78793 =
                                                      let uu____78794 =
                                                        let uu____78805 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3)
                                                           in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____78805)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        t0.FStar_Syntax_Syntax.pos
                                                        uu____78794
                                                       in
                                                    (uu____78793,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____78785
                                                   in
                                                let f_decls =
                                                  FStar_List.append (fdecl ::
                                                    typing_f) [interp_f]
                                                   in
                                                let uu____78819 =
                                                  let uu____78820 =
                                                    let uu____78823 =
                                                      let uu____78826 =
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
                                                        decls'' uu____78826
                                                       in
                                                    FStar_List.append decls'
                                                      uu____78823
                                                     in
                                                  FStar_List.append decls
                                                    uu____78820
                                                   in
                                                (f, uu____78819))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____78829,{
                           FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                             uu____78830;
                           FStar_Syntax_Syntax.lbunivs = uu____78831;
                           FStar_Syntax_Syntax.lbtyp = uu____78832;
                           FStar_Syntax_Syntax.lbeff = uu____78833;
                           FStar_Syntax_Syntax.lbdef = uu____78834;
                           FStar_Syntax_Syntax.lbattrs = uu____78835;
                           FStar_Syntax_Syntax.lbpos = uu____78836;_}::uu____78837),uu____78838)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____78872;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____78874;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____78876;
                FStar_Syntax_Syntax.lbpos = uu____78877;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____78904 ->
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
              let uu____78976 =
                let uu____78981 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____78981 env  in
              match uu____78976 with
              | (ee1,decls1) ->
                  let uu____79006 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____79006 with
                   | (xs,e21) ->
                       let uu____79031 = FStar_List.hd xs  in
                       (match uu____79031 with
                        | (x1,uu____79049) ->
                            let env' =
                              FStar_SMTEncoding_Env.push_term_var env x1 ee1
                               in
                            let uu____79055 = encode_body e21 env'  in
                            (match uu____79055 with
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
            let uu____79085 =
              let uu____79093 =
                let uu____79094 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____79094  in
              FStar_SMTEncoding_Env.gen_term_var env uu____79093  in
            match uu____79085 with
            | (scrsym,scr',env1) ->
                let uu____79104 = encode_term e env1  in
                (match uu____79104 with
                 | (scr,decls) ->
                     let uu____79115 =
                       let encode_branch b uu____79144 =
                         match uu____79144 with
                         | (else_case,decls1) ->
                             let uu____79163 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____79163 with
                              | (p,w,br) ->
                                  let uu____79189 = encode_pat env1 p  in
                                  (match uu____79189 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____79226  ->
                                                   match uu____79226 with
                                                   | (x,t) ->
                                                       FStar_SMTEncoding_Env.push_term_var
                                                         env2 x t) env1)
                                          in
                                       let uu____79233 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____79255 =
                                               encode_term w1 env2  in
                                             (match uu____79255 with
                                              | (w2,decls2) ->
                                                  let uu____79268 =
                                                    let uu____79269 =
                                                      let uu____79274 =
                                                        let uu____79275 =
                                                          let uu____79280 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____79280)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____79275
                                                         in
                                                      (guard, uu____79274)
                                                       in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____79269
                                                     in
                                                  (uu____79268, decls2))
                                          in
                                       (match uu____79233 with
                                        | (guard1,decls2) ->
                                            let uu____79295 =
                                              encode_br br env2  in
                                            (match uu____79295 with
                                             | (br1,decls3) ->
                                                 let uu____79308 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____79308,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____79115 with
                      | (match_tm,decls1) ->
                          let uu____79329 =
                            let uu____79330 =
                              let uu____79341 =
                                let uu____79348 =
                                  let uu____79353 =
                                    FStar_SMTEncoding_Term.mk_fv
                                      (scrsym,
                                        FStar_SMTEncoding_Term.Term_sort)
                                     in
                                  (uu____79353, scr)  in
                                [uu____79348]  in
                              (uu____79341, match_tm)  in
                            FStar_SMTEncoding_Term.mkLet' uu____79330
                              FStar_Range.dummyRange
                             in
                          (uu____79329, decls1)))

and (encode_pat :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.pat -> (FStar_SMTEncoding_Env.env_t * pattern))
  =
  fun env  ->
    fun pat  ->
      (let uu____79376 =
         FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
           FStar_Options.Medium
          in
       if uu____79376
       then
         let uu____79379 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____79379
       else ());
      (let uu____79384 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____79384 with
       | (vars,pat_term) ->
           let uu____79401 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____79443  ->
                     fun v1  ->
                       match uu____79443 with
                       | (env1,vars1) ->
                           let uu____79479 =
                             FStar_SMTEncoding_Env.gen_term_var env1 v1  in
                           (match uu____79479 with
                            | (xx,uu____79498,env2) ->
                                let uu____79502 =
                                  let uu____79509 =
                                    let uu____79514 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xx,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    (v1, uu____79514)  in
                                  uu____79509 :: vars1  in
                                (env2, uu____79502))) (env, []))
              in
           (match uu____79401 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____79569 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____79570 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____79571 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____79579 = encode_const c env1  in
                      (match uu____79579 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____79587::uu____79588 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____79592 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon
                            env1.FStar_SMTEncoding_Env.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____79615 =
                          FStar_TypeChecker_Env.datacons_of_typ
                            env1.FStar_SMTEncoding_Env.tcenv tc_name
                           in
                        match uu____79615 with
                        | (uu____79623,uu____79624::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____79629 ->
                            FStar_SMTEncoding_Env.mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____79665  ->
                                  match uu____79665 with
                                  | (arg,uu____79675) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____79684 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____79684))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____79716) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____79747 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____79772 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____79818  ->
                                  match uu____79818 with
                                  | (arg,uu____79834) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____79843 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____79843))
                         in
                      FStar_All.pipe_right uu____79772 FStar_List.flatten
                   in
                let pat_term1 uu____79874 = encode_term pat_term env1  in
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
      let uu____79884 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____79932  ->
                fun uu____79933  ->
                  match (uu____79932, uu____79933) with
                  | ((tms,decls),(t,uu____79973)) ->
                      let uu____80000 = encode_term t env  in
                      (match uu____80000 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____79884 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____80057 = FStar_Syntax_Util.list_elements e  in
        match uu____80057 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____80088 =
          let uu____80105 = FStar_Syntax_Util.unmeta p  in
          FStar_All.pipe_right uu____80105 FStar_Syntax_Util.head_and_args
           in
        match uu____80088 with
        | (head1,args) ->
            let uu____80156 =
              let uu____80171 =
                let uu____80172 = FStar_Syntax_Util.un_uinst head1  in
                uu____80172.FStar_Syntax_Syntax.n  in
              (uu____80171, args)  in
            (match uu____80156 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____80194,uu____80195)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____80247 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or1 t1 =
          let uu____80302 =
            let uu____80319 = FStar_Syntax_Util.unmeta t1  in
            FStar_All.pipe_right uu____80319 FStar_Syntax_Util.head_and_args
             in
          match uu____80302 with
          | (head1,args) ->
              let uu____80366 =
                let uu____80381 =
                  let uu____80382 = FStar_Syntax_Util.un_uinst head1  in
                  uu____80382.FStar_Syntax_Syntax.n  in
                (uu____80381, args)  in
              (match uu____80366 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____80401)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____80438 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____80468 = smt_pat_or1 t1  in
            (match uu____80468 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____80490 = list_elements1 e  in
                 FStar_All.pipe_right uu____80490
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____80520 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____80520
                           (FStar_List.map one_pat)))
             | uu____80543 ->
                 let uu____80548 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____80548])
        | uu____80599 ->
            let uu____80602 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____80602]
         in
      let uu____80653 =
        let uu____80668 =
          let uu____80669 = FStar_Syntax_Subst.compress t  in
          uu____80669.FStar_Syntax_Syntax.n  in
        match uu____80668 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____80708 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____80708 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____80743;
                        FStar_Syntax_Syntax.effect_name = uu____80744;
                        FStar_Syntax_Syntax.result_typ = uu____80745;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____80747)::(post,uu____80749)::(pats,uu____80751)::[];
                        FStar_Syntax_Syntax.flags = uu____80752;_}
                      ->
                      let uu____80813 = lemma_pats pats  in
                      (binders1, pre, post, uu____80813)
                  | uu____80824 -> failwith "impos"))
        | uu____80840 -> failwith "Impos"  in
      match uu____80653 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___1940_80877 = env  in
            {
              FStar_SMTEncoding_Env.bvar_bindings =
                (uu___1940_80877.FStar_SMTEncoding_Env.bvar_bindings);
              FStar_SMTEncoding_Env.fvar_bindings =
                (uu___1940_80877.FStar_SMTEncoding_Env.fvar_bindings);
              FStar_SMTEncoding_Env.depth =
                (uu___1940_80877.FStar_SMTEncoding_Env.depth);
              FStar_SMTEncoding_Env.tcenv =
                (uu___1940_80877.FStar_SMTEncoding_Env.tcenv);
              FStar_SMTEncoding_Env.warn =
                (uu___1940_80877.FStar_SMTEncoding_Env.warn);
              FStar_SMTEncoding_Env.nolabels =
                (uu___1940_80877.FStar_SMTEncoding_Env.nolabels);
              FStar_SMTEncoding_Env.use_zfuel_name = true;
              FStar_SMTEncoding_Env.encode_non_total_function_typ =
                (uu___1940_80877.FStar_SMTEncoding_Env.encode_non_total_function_typ);
              FStar_SMTEncoding_Env.current_module_name =
                (uu___1940_80877.FStar_SMTEncoding_Env.current_module_name);
              FStar_SMTEncoding_Env.encoding_quantifier =
                (uu___1940_80877.FStar_SMTEncoding_Env.encoding_quantifier);
              FStar_SMTEncoding_Env.global_cache =
                (uu___1940_80877.FStar_SMTEncoding_Env.global_cache)
            }  in
          let uu____80879 =
            encode_binders FStar_Pervasives_Native.None binders env1  in
          (match uu____80879 with
           | (vars,guards,env2,decls,uu____80904) ->
               let uu____80917 = encode_smt_patterns patterns env2  in
               (match uu____80917 with
                | (pats,decls') ->
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
                    let env3 =
                      let uu___1953_80944 = env2  in
                      {
                        FStar_SMTEncoding_Env.bvar_bindings =
                          (uu___1953_80944.FStar_SMTEncoding_Env.bvar_bindings);
                        FStar_SMTEncoding_Env.fvar_bindings =
                          (uu___1953_80944.FStar_SMTEncoding_Env.fvar_bindings);
                        FStar_SMTEncoding_Env.depth =
                          (uu___1953_80944.FStar_SMTEncoding_Env.depth);
                        FStar_SMTEncoding_Env.tcenv =
                          (uu___1953_80944.FStar_SMTEncoding_Env.tcenv);
                        FStar_SMTEncoding_Env.warn =
                          (uu___1953_80944.FStar_SMTEncoding_Env.warn);
                        FStar_SMTEncoding_Env.nolabels = true;
                        FStar_SMTEncoding_Env.use_zfuel_name =
                          (uu___1953_80944.FStar_SMTEncoding_Env.use_zfuel_name);
                        FStar_SMTEncoding_Env.encode_non_total_function_typ =
                          (uu___1953_80944.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                        FStar_SMTEncoding_Env.current_module_name =
                          (uu___1953_80944.FStar_SMTEncoding_Env.current_module_name);
                        FStar_SMTEncoding_Env.encoding_quantifier =
                          (uu___1953_80944.FStar_SMTEncoding_Env.encoding_quantifier);
                        FStar_SMTEncoding_Env.global_cache =
                          (uu___1953_80944.FStar_SMTEncoding_Env.global_cache)
                      }  in
                    let uu____80946 =
                      let uu____80951 = FStar_Syntax_Util.unmeta pre  in
                      encode_formula uu____80951 env3  in
                    (match uu____80946 with
                     | (pre1,decls'') ->
                         let uu____80958 =
                           let uu____80963 = FStar_Syntax_Util.unmeta post1
                              in
                           encode_formula uu____80963 env3  in
                         (match uu____80958 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append decls'
                                     (FStar_List.append decls'' decls'''))
                                 in
                              let uu____80973 =
                                let uu____80974 =
                                  let uu____80985 =
                                    let uu____80986 =
                                      let uu____80991 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards)
                                         in
                                      (uu____80991, post2)  in
                                    FStar_SMTEncoding_Util.mkImp uu____80986
                                     in
                                  (pats, vars, uu____80985)  in
                                FStar_SMTEncoding_Term.mkForall
                                  t.FStar_Syntax_Syntax.pos uu____80974
                                 in
                              (uu____80973, decls1)))))

and (encode_smt_patterns :
  FStar_Syntax_Syntax.arg Prims.list Prims.list ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term Prims.list Prims.list *
        FStar_SMTEncoding_Term.decls_t))
  =
  fun pats_l  ->
    fun env  ->
      let env1 =
        let uu___1965_81011 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___1965_81011.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___1965_81011.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___1965_81011.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___1965_81011.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___1965_81011.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___1965_81011.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___1965_81011.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___1965_81011.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___1965_81011.FStar_SMTEncoding_Env.encoding_quantifier);
          FStar_SMTEncoding_Env.global_cache =
            (uu___1965_81011.FStar_SMTEncoding_Env.global_cache)
        }  in
      let encode_smt_pattern t =
        let uu____81027 = FStar_Syntax_Util.head_and_args t  in
        match uu____81027 with
        | (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____81090::(x,uu____81092)::(t1,uu____81094)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____81161 = encode_term x env1  in
                 (match uu____81161 with
                  | (x1,decls) ->
                      let uu____81172 = encode_term t1 env1  in
                      (match uu____81172 with
                       | (t2,decls') ->
                           let uu____81183 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                           (uu____81183, (FStar_List.append decls decls'))))
             | uu____81184 -> encode_term t env1)
         in
      FStar_List.fold_right
        (fun pats  ->
           fun uu____81227  ->
             match uu____81227 with
             | (pats_l1,decls) ->
                 let uu____81272 =
                   FStar_List.fold_right
                     (fun uu____81307  ->
                        fun uu____81308  ->
                          match (uu____81307, uu____81308) with
                          | ((p,uu____81350),(pats1,decls1)) ->
                              let uu____81385 = encode_smt_pattern p  in
                              (match uu____81385 with
                               | (t,d) ->
                                   let uu____81400 =
                                     FStar_SMTEncoding_Term.check_pattern_ok
                                       t
                                      in
                                   (match uu____81400 with
                                    | FStar_Pervasives_Native.None  ->
                                        ((t :: pats1),
                                          (FStar_List.append d decls1))
                                    | FStar_Pervasives_Native.Some
                                        illegal_subterm ->
                                        ((let uu____81417 =
                                            let uu____81423 =
                                              let uu____81425 =
                                                FStar_Syntax_Print.term_to_string
                                                  p
                                                 in
                                              let uu____81427 =
                                                FStar_SMTEncoding_Term.print_smt_term
                                                  illegal_subterm
                                                 in
                                              FStar_Util.format2
                                                "Pattern %s contains illegal sub-term (%s); dropping it"
                                                uu____81425 uu____81427
                                               in
                                            (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                                              uu____81423)
                                             in
                                          FStar_Errors.log_issue
                                            p.FStar_Syntax_Syntax.pos
                                            uu____81417);
                                         (pats1,
                                           (FStar_List.append d decls1))))))
                     pats ([], decls)
                    in
                 (match uu____81272 with
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
        let uu____81487 =
          FStar_All.pipe_left
            (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____81487
        then
          let uu____81492 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____81494 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____81492 uu____81494
        else ()  in
      let enc f r l =
        let uu____81536 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____81568 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____81568 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____81536 with
        | (decls,args) ->
            let uu____81599 =
              let uu___2029_81600 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___2029_81600.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___2029_81600.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____81599, decls)
         in
      let const_op f r uu____81635 =
        let uu____81648 = f r  in (uu____81648, [])  in
      let un_op f l =
        let uu____81671 = FStar_List.hd l  in
        FStar_All.pipe_left f uu____81671  in
      let bin_op f uu___632_81691 =
        match uu___632_81691 with
        | t1::t2::[] -> f (t1, t2)
        | uu____81702 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____81743 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____81768  ->
                 match uu____81768 with
                 | (t,uu____81784) ->
                     let uu____81789 = encode_formula t env  in
                     (match uu____81789 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____81743 with
        | (decls,phis) ->
            let uu____81818 =
              let uu___2059_81819 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___2059_81819.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___2059_81819.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____81818, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____81882  ->
               match uu____81882 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____81903) -> false
                    | uu____81906 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____81925 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____81925
        else
          (let uu____81942 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____81942 r rf)
         in
      let eq3_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____82014 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::t1::v0::v1::[] ->
                     let uu____82046 =
                       let uu____82051 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____82052 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____82051, uu____82052)  in
                     FStar_SMTEncoding_Util.mkAnd uu____82046
                 | uu____82053 -> failwith "Impossible")
             in
          uu____82014 r args
        else
          (let uu____82059 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____82059)
         in
      let h_equals_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____82131 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::v0::t1::v1::[] ->
                     let uu____82163 =
                       let uu____82168 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____82169 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____82168, uu____82169)  in
                     FStar_SMTEncoding_Util.mkAnd uu____82163
                 | uu____82170 -> failwith "Impossible")
             in
          uu____82131 r args
        else
          (let uu____82176 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____82176)
         in
      let mk_imp1 r uu___633_82211 =
        match uu___633_82211 with
        | (lhs,uu____82217)::(rhs,uu____82219)::[] ->
            let uu____82260 = encode_formula rhs env  in
            (match uu____82260 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____82275) ->
                      (l1, decls1)
                  | uu____82280 ->
                      let uu____82281 = encode_formula lhs env  in
                      (match uu____82281 with
                       | (l2,decls2) ->
                           let uu____82292 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____82292, (FStar_List.append decls1 decls2)))))
        | uu____82293 -> failwith "impossible"  in
      let mk_ite r uu___634_82321 =
        match uu___634_82321 with
        | (guard,uu____82327)::(_then,uu____82329)::(_else,uu____82331)::[]
            ->
            let uu____82388 = encode_formula guard env  in
            (match uu____82388 with
             | (g,decls1) ->
                 let uu____82399 = encode_formula _then env  in
                 (match uu____82399 with
                  | (t,decls2) ->
                      let uu____82410 = encode_formula _else env  in
                      (match uu____82410 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____82422 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____82452 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l
           in
        f uu____82452  in
      let connectives =
        let uu____82482 =
          let uu____82507 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____82507)  in
        let uu____82550 =
          let uu____82577 =
            let uu____82602 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____82602)  in
          let uu____82645 =
            let uu____82672 =
              let uu____82699 =
                let uu____82724 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____82724)  in
              let uu____82767 =
                let uu____82794 =
                  let uu____82821 =
                    let uu____82846 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____82846)  in
                  [uu____82821;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.c_eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq3_op);
                  (FStar_Parser_Const.c_eq3_lid, h_equals_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____82794  in
              uu____82699 :: uu____82767  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____82672  in
          uu____82577 :: uu____82645  in
        uu____82482 :: uu____82550  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____83391 = encode_formula phi' env  in
            (match uu____83391 with
             | (phi2,decls) ->
                 let uu____83402 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____83402, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____83404 ->
            let uu____83411 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____83411 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____83450 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____83450 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____83462;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____83464;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____83466;
                 FStar_Syntax_Syntax.lbpos = uu____83467;_}::[]),e2)
            ->
            let uu____83494 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____83494 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____83547::(x,uu____83549)::(t,uu____83551)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____83618 = encode_term x env  in
                 (match uu____83618 with
                  | (x1,decls) ->
                      let uu____83629 = encode_term t env  in
                      (match uu____83629 with
                       | (t1,decls') ->
                           let uu____83640 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____83640, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____83643)::(msg,uu____83645)::(phi2,uu____83647)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____83714 =
                   let uu____83719 =
                     let uu____83720 = FStar_Syntax_Subst.compress r  in
                     uu____83720.FStar_Syntax_Syntax.n  in
                   let uu____83723 =
                     let uu____83724 = FStar_Syntax_Subst.compress msg  in
                     uu____83724.FStar_Syntax_Syntax.n  in
                   (uu____83719, uu____83723)  in
                 (match uu____83714 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____83733))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____83744 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____83751)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____83786 when head_redex env head2 ->
                 let uu____83801 = whnf env phi1  in
                 encode_formula uu____83801 env
             | uu____83802 ->
                 let uu____83817 = encode_term phi1 env  in
                 (match uu____83817 with
                  | (tt,decls) ->
                      let tt1 =
                        let uu____83829 =
                          let uu____83831 =
                            FStar_Range.use_range
                              tt.FStar_SMTEncoding_Term.rng
                             in
                          let uu____83832 =
                            FStar_Range.use_range
                              phi1.FStar_Syntax_Syntax.pos
                             in
                          FStar_Range.rng_included uu____83831 uu____83832
                           in
                        if uu____83829
                        then tt
                        else
                          (let uu___2246_83836 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___2246_83836.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___2246_83836.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      let uu____83837 = FStar_SMTEncoding_Term.mk_Valid tt1
                         in
                      (uu____83837, decls)))
        | uu____83838 ->
            let uu____83839 = encode_term phi1 env  in
            (match uu____83839 with
             | (tt,decls) ->
                 let tt1 =
                   let uu____83851 =
                     let uu____83853 =
                       FStar_Range.use_range tt.FStar_SMTEncoding_Term.rng
                        in
                     let uu____83854 =
                       FStar_Range.use_range phi1.FStar_Syntax_Syntax.pos  in
                     FStar_Range.rng_included uu____83853 uu____83854  in
                   if uu____83851
                   then tt
                   else
                     (let uu___2254_83858 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___2254_83858.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___2254_83858.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 let uu____83859 = FStar_SMTEncoding_Term.mk_Valid tt1  in
                 (uu____83859, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____83903 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____83903 with
        | (vars,guards,env2,decls,uu____83942) ->
            let uu____83955 = encode_smt_patterns ps env2  in
            (match uu____83955 with
             | (pats,decls') ->
                 let uu____83992 = encode_formula body env2  in
                 (match uu____83992 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____84024;
                             FStar_SMTEncoding_Term.rng = uu____84025;_}::[])::[]
                            when
                            let uu____84045 =
                              FStar_Ident.text_of_lid
                                FStar_Parser_Const.guard_free
                               in
                            uu____84045 = gf -> []
                        | uu____84048 -> guards  in
                      let uu____84053 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____84053, body1,
                        (FStar_List.append decls
                           (FStar_List.append decls' decls'')))))
         in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi  in
       let uu____84064 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____84064 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____84073 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____84179  ->
                     match uu____84179 with
                     | (l,uu____84204) -> FStar_Ident.lid_equals op l))
              in
           (match uu____84073 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____84273,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____84365 = encode_q_body env vars pats body  in
             match uu____84365 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____84410 =
                     let uu____84421 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____84421)  in
                   FStar_SMTEncoding_Term.mkForall
                     phi1.FStar_Syntax_Syntax.pos uu____84410
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____84452 = encode_q_body env vars pats body  in
             match uu____84452 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____84496 =
                   let uu____84497 =
                     let uu____84508 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____84508)  in
                   FStar_SMTEncoding_Term.mkExists
                     phi1.FStar_Syntax_Syntax.pos uu____84497
                    in
                 (uu____84496, decls))))
