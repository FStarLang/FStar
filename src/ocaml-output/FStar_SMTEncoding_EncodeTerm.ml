open Prims
let mkForall_fuel' :
  'Auu____11 .
    Prims.string ->
      FStar_Range.range ->
        'Auu____11 ->
          (FStar_SMTEncoding_Term.pat Prims.list Prims.list *
            FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term) ->
            FStar_SMTEncoding_Term.term
  =
  fun mname  ->
    fun r  ->
      fun n1  ->
        fun uu____42  ->
          match uu____42 with
          | (pats,vars,body) ->
              let fallback uu____70 =
                FStar_SMTEncoding_Term.mkForall r (pats, vars, body)  in
              let uu____75 = FStar_Options.unthrottle_inductives ()  in
              if uu____75
              then fallback ()
              else
                (let uu____80 =
                   FStar_SMTEncoding_Env.fresh_fvar mname "f"
                     FStar_SMTEncoding_Term.Fuel_sort
                    in
                 match uu____80 with
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
                               | uu____120 -> p))
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
                                 let uu____141 = add_fuel1 guards  in
                                 FStar_SMTEncoding_Util.mk_and_l uu____141
                             | uu____144 ->
                                 let uu____145 = add_fuel1 [guard]  in
                                 FStar_All.pipe_right uu____145 FStar_List.hd
                              in
                           FStar_SMTEncoding_Util.mkImp (guard1, body')
                       | uu____150 -> body  in
                     let vars1 =
                       let uu____162 =
                         FStar_SMTEncoding_Term.mk_fv
                           (fsym, FStar_SMTEncoding_Term.Fuel_sort)
                          in
                       uu____162 :: vars  in
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
      | FStar_Syntax_Syntax.Tm_arrow uu____226 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____242 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____250 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____252 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____266 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____286 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____289 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____289 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____308;
             FStar_Syntax_Syntax.vars = uu____309;_},uu____310)
          ->
          let uu____335 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____335 FStar_Option.isNone
      | uu____353 -> false
  
let (head_redex :
  FStar_SMTEncoding_Env.env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____367 =
        let uu____368 = FStar_Syntax_Util.un_uinst t  in
        uu____368.FStar_Syntax_Syntax.n  in
      match uu____367 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____372,uu____373,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___11_398  ->
                  match uu___11_398 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____401 -> false) rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____404 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____404 FStar_Option.isSome
      | uu____422 -> false
  
let (whnf :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____435 = head_normal env t  in
      if uu____435
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
    let uu____457 =
      let uu____458 = FStar_Syntax_Syntax.null_binder t  in [uu____458]  in
    let uu____477 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    FStar_Syntax_Util.abs uu____457 uu____477 FStar_Pervasives_Native.None
  
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
                let uu____499 = FStar_SMTEncoding_Term.fv_sort var  in
                match uu____499 with
                | FStar_SMTEncoding_Term.Fuel_sort  ->
                    let uu____500 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____500
                | s ->
                    let uu____503 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____503) e)
  
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
          let uu____559 =
            let uu____565 =
              let uu____567 = FStar_Util.string_of_int arity  in
              let uu____569 = FStar_Util.string_of_int n_args  in
              FStar_Util.format3
                "Head symbol %s expects at least %s arguments; got only %s"
                head1 uu____567 uu____569
               in
            (FStar_Errors.Fatal_SMTEncodingArityMismatch, uu____565)  in
          FStar_Errors.raise_error uu____559 rng
  
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
                  (let uu____628 = FStar_Util.first_N arity args  in
                   match uu____628 with
                   | (args1,rest) ->
                       let head3 =
                         FStar_SMTEncoding_Util.mkApp' (head2, args1)  in
                       mk_Apply_args head3 rest)
                else
                  (let uu____652 = FStar_SMTEncoding_Term.op_to_string head2
                      in
                   raise_arity_mismatch uu____652 arity n_args rng)
  
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
          let uu____679 = FStar_SMTEncoding_Env.force_thunk fvb  in
          mk_Apply_args uu____679 args
        else
          maybe_curry_app rng
            (FStar_Util.Inl
               (FStar_SMTEncoding_Term.Var (fvb.FStar_SMTEncoding_Env.smt_id)))
            fvb.FStar_SMTEncoding_Env.smt_arity args
  
let (is_app : FStar_SMTEncoding_Term.op -> Prims.bool) =
  fun uu___12_688  ->
    match uu___12_688 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____694 -> false
  
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
                       FStar_SMTEncoding_Term.freevars = uu____742;
                       FStar_SMTEncoding_Term.rng = uu____743;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____774) ->
              let uu____784 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____801 -> false) args (FStar_List.rev xs))
                 in
              if uu____784
              then FStar_SMTEncoding_Env.tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____808,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t  in
              let uu____812 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____820 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars
                           in
                        Prims.op_Negation uu____820))
                 in
              if uu____812
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____827 -> FStar_Pervasives_Native.None  in
        check_partial_applications body (FStar_List.rev vars)
  
let check_pattern_vars :
  'Auu____845 'Auu____846 .
    FStar_SMTEncoding_Env.env_t ->
      (FStar_Syntax_Syntax.bv * 'Auu____845) Prims.list ->
        (FStar_Syntax_Syntax.term * 'Auu____846) Prims.list -> unit
  =
  fun env  ->
    fun vars  ->
      fun pats  ->
        let pats1 =
          FStar_All.pipe_right pats
            (FStar_List.map
               (fun uu____904  ->
                  match uu____904 with
                  | (x,uu____910) ->
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
              let uu____918 = FStar_Syntax_Free.names hd1  in
              FStar_List.fold_left
                (fun out  ->
                   fun x  ->
                     let uu____930 = FStar_Syntax_Free.names x  in
                     FStar_Util.set_union out uu____930) uu____918 tl1
               in
            let uu____933 =
              FStar_All.pipe_right vars
                (FStar_Util.find_opt
                   (fun uu____960  ->
                      match uu____960 with
                      | (b,uu____967) ->
                          let uu____968 = FStar_Util.set_mem b pat_vars  in
                          Prims.op_Negation uu____968))
               in
            (match uu____933 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some (x,uu____975) ->
                 let pos =
                   FStar_List.fold_left
                     (fun out  ->
                        fun t  ->
                          FStar_Range.union_ranges out
                            t.FStar_Syntax_Syntax.pos)
                     hd1.FStar_Syntax_Syntax.pos tl1
                    in
                 let uu____989 =
                   let uu____995 =
                     let uu____997 = FStar_Syntax_Print.bv_to_string x  in
                     FStar_Util.format1
                       "SMT pattern misses at least one bound variable: %s"
                       uu____997
                      in
                   (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                     uu____995)
                    in
                 FStar_Errors.log_issue pos uu____989)
  
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
        | FStar_Syntax_Syntax.Tm_arrow uu____1283 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____1298 ->
            let uu____1305 = FStar_Syntax_Util.unrefine t1  in
            aux true uu____1305
        | uu____1307 ->
            if norm1
            then let uu____1309 = whnf env t1  in aux false uu____1309
            else
              (let uu____1313 =
                 let uu____1315 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let uu____1317 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____1315 uu____1317
                  in
               failwith uu____1313)
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
    | FStar_Syntax_Syntax.Tm_refine (bv,uu____1359) ->
        let uu____1364 =
          curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort  in
        (match uu____1364 with
         | (args,res) ->
             (match args with
              | [] ->
                  let uu____1385 = FStar_Syntax_Syntax.mk_Total k1  in
                  ([], uu____1385)
              | uu____1392 -> (args, res)))
    | uu____1393 ->
        let uu____1394 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____1394)
  
let is_arithmetic_primitive :
  'Auu____1408 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____1408 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1431::uu____1432::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1436::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____1439 -> false
  
let (isInteger : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____1470 -> false
  
let (getInteger : FStar_Syntax_Syntax.term' -> Prims.int) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____1493 -> failwith "Expected an Integer term"
  
let is_BitVector_primitive :
  'Auu____1503 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____1503)
        Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____1545)::uu____1546::uu____1547::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____1598)::uu____1599::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____1636 -> false
  
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
          let uu____1960 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue  in
          (uu____1960, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____1962 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse  in
          (uu____1962, [])
      | FStar_Const.Const_char c1 ->
          let uu____1965 =
            let uu____1966 =
              let uu____1974 =
                let uu____1977 =
                  let uu____1978 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1)
                     in
                  FStar_SMTEncoding_Term.boxInt uu____1978  in
                [uu____1977]  in
              ("FStar.Char.__char_of_int", uu____1974)  in
            FStar_SMTEncoding_Util.mkApp uu____1966  in
          (uu____1965, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____1996 =
            let uu____1997 = FStar_SMTEncoding_Util.mkInteger i  in
            FStar_SMTEncoding_Term.boxInt uu____1997  in
          (uu____1996, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.FStar_SMTEncoding_Env.tcenv).FStar_TypeChecker_Env.dsenv
              repr sw FStar_Range.dummyRange
             in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____2018) ->
          let uu____2021 =
            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.string_const s
             in
          (uu____2021, [])
      | FStar_Const.Const_range uu____2022 ->
          let uu____2023 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          (uu____2023, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | c1 ->
          let uu____2025 =
            let uu____2027 = FStar_Syntax_Print.const_to_string c1  in
            FStar_Util.format1 "Unhandled constant: %s" uu____2027  in
          failwith uu____2025

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
        (let uu____2056 =
           FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
             FStar_Options.Medium
            in
         if uu____2056
         then
           let uu____2059 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____2059
         else ());
        (let uu____2065 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2147  ->
                   fun b  ->
                     match uu____2147 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2212 =
                           let x = FStar_Pervasives_Native.fst b  in
                           let uu____2228 =
                             FStar_SMTEncoding_Env.gen_term_var env1 x  in
                           match uu____2228 with
                           | (xxsym,xx,env') ->
                               let uu____2253 =
                                 let uu____2258 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____2258 env1 xx
                                  in
                               (match uu____2253 with
                                | (guard_x_t,decls') ->
                                    let uu____2273 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xxsym,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    (uu____2273, guard_x_t, env', decls', x))
                            in
                         (match uu____2212 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____2065 with
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
          let uu____2373 = encode_term t env  in
          match uu____2373 with
          | (t1,decls) ->
              let uu____2384 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____2384, decls)

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
          let uu____2395 = encode_term t env  in
          match uu____2395 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____2410 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____2410, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____2412 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____2412, decls))

and (encode_arith_term :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____2418 = encode_args args_e env  in
        match uu____2418 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____2437 -> failwith "Impossible"  in
            let unary arg_tms1 =
              let uu____2449 = FStar_List.hd arg_tms1  in
              FStar_SMTEncoding_Term.unboxInt uu____2449  in
            let binary arg_tms1 =
              let uu____2464 =
                let uu____2465 = FStar_List.hd arg_tms1  in
                FStar_SMTEncoding_Term.unboxInt uu____2465  in
              let uu____2466 =
                let uu____2467 =
                  let uu____2468 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____2468  in
                FStar_SMTEncoding_Term.unboxInt uu____2467  in
              (uu____2464, uu____2466)  in
            let mk_default uu____2476 =
              let uu____2477 =
                FStar_SMTEncoding_Env.lookup_free_var_sym env
                  head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____2477 with
              | (fname,fuel_args,arity) ->
                  let args = FStar_List.append fuel_args arg_tms  in
                  maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity
                    args
               in
            let mk_l op mk_args ts =
              let uu____2554 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____2554
              then
                let uu____2557 =
                  let uu____2558 = mk_args ts  in op uu____2558  in
                FStar_All.pipe_right uu____2557 FStar_SMTEncoding_Term.boxInt
              else mk_default ()  in
            let mk_nl nm op ts =
              let uu____2596 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____2596
              then
                let uu____2599 = binary ts  in
                match uu____2599 with
                | (t1,t2) ->
                    let uu____2606 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____2606
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____2612 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____2612
                 then
                   let uu____2615 =
                     let uu____2616 = binary ts  in op uu____2616  in
                   FStar_All.pipe_right uu____2615
                     FStar_SMTEncoding_Term.boxInt
                 else mk_default ())
               in
            let add1 = mk_l FStar_SMTEncoding_Util.mkAdd binary  in
            let sub1 = mk_l FStar_SMTEncoding_Util.mkSub binary  in
            let minus1 = mk_l FStar_SMTEncoding_Util.mkMinus unary  in
            let mul1 = mk_nl "_mul" FStar_SMTEncoding_Util.mkMul  in
            let div1 = mk_nl "_div" FStar_SMTEncoding_Util.mkDiv  in
            let modulus = mk_nl "_mod" FStar_SMTEncoding_Util.mkMod  in
            let ops =
              [(FStar_Parser_Const.op_Addition, add1);
              (FStar_Parser_Const.op_Subtraction, sub1);
              (FStar_Parser_Const.op_Multiply, mul1);
              (FStar_Parser_Const.op_Division, div1);
              (FStar_Parser_Const.op_Modulus, modulus);
              (FStar_Parser_Const.op_Minus, minus1)]  in
            let uu____2781 =
              let uu____2791 =
                FStar_List.tryFind
                  (fun uu____2815  ->
                     match uu____2815 with
                     | (l,uu____2826) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____2791 FStar_Util.must  in
            (match uu____2781 with
             | (uu____2870,op) ->
                 let uu____2882 = op arg_tms  in (uu____2882, decls))

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
        let uu____2898 = FStar_List.hd args_e  in
        match uu____2898 with
        | (tm_sz,uu____2914) ->
            let uu____2923 = uu____2898  in
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let t_decls1 = FStar_SMTEncoding_Term.mkBvConstructor sz  in
              FStar_SMTEncoding_Term.mk_decls "" sz_key t_decls1 []  in
            let uu____2934 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____2960::(sz_arg,uu____2962)::uu____2963::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____3030 =
                    let uu____3031 = FStar_List.tail args_e  in
                    FStar_List.tail uu____3031  in
                  let uu____3058 =
                    let uu____3062 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____3062  in
                  (uu____3030, uu____3058)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____3069::(sz_arg,uu____3071)::uu____3072::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____3139 =
                    let uu____3141 = FStar_Syntax_Print.term_to_string sz_arg
                       in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____3141
                     in
                  failwith uu____3139
              | uu____3151 ->
                  let uu____3166 = FStar_List.tail args_e  in
                  (uu____3166, FStar_Pervasives_Native.None)
               in
            (match uu____2934 with
             | (arg_tms,ext_sz) ->
                 let uu____3193 = encode_args arg_tms env  in
                 (match uu____3193 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____3214 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____3226 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____3226  in
                      let unary_arith arg_tms2 =
                        let uu____3237 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____3237  in
                      let binary arg_tms2 =
                        let uu____3252 =
                          let uu____3253 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3253
                           in
                        let uu____3254 =
                          let uu____3255 =
                            let uu____3256 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____3256  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3255
                           in
                        (uu____3252, uu____3254)  in
                      let binary_arith arg_tms2 =
                        let uu____3273 =
                          let uu____3274 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3274
                           in
                        let uu____3275 =
                          let uu____3276 =
                            let uu____3277 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____3277  in
                          FStar_SMTEncoding_Term.unboxInt uu____3276  in
                        (uu____3273, uu____3275)  in
                      let mk_bv op mk_args resBox ts =
                        let uu____3335 =
                          let uu____3336 = mk_args ts  in op uu____3336  in
                        FStar_All.pipe_right uu____3335 resBox  in
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
                        let uu____3468 =
                          let uu____3473 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____3473  in
                        let uu____3482 =
                          let uu____3487 =
                            let uu____3489 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____3489  in
                          FStar_SMTEncoding_Term.boxBitVec uu____3487  in
                        mk_bv uu____3468 unary uu____3482 arg_tms2  in
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
                      let uu____3729 =
                        let uu____3739 =
                          FStar_List.tryFind
                            (fun uu____3763  ->
                               match uu____3763 with
                               | (l,uu____3774) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____3739 FStar_Util.must  in
                      (match uu____3729 with
                       | (uu____3820,op) ->
                           let uu____3832 = op arg_tms1  in
                           (uu____3832, (FStar_List.append sz_decls decls)))))

and (encode_deeply_embedded_quantifier :
  FStar_Syntax_Syntax.term ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let env1 =
        let uu___16_3842 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___16_3842.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___16_3842.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___16_3842.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___16_3842.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___16_3842.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___16_3842.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name =
            (uu___16_3842.FStar_SMTEncoding_Env.use_zfuel_name);
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___16_3842.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___16_3842.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier = true;
          FStar_SMTEncoding_Env.global_cache =
            (uu___16_3842.FStar_SMTEncoding_Env.global_cache)
        }  in
      let uu____3844 = encode_term t env1  in
      match uu____3844 with
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
               (uu____3870,{
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.FreeV uu____3871;
                             FStar_SMTEncoding_Term.freevars = uu____3872;
                             FStar_SMTEncoding_Term.rng = uu____3873;_}::
                {
                  FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV
                    uu____3874;
                  FStar_SMTEncoding_Term.freevars = uu____3875;
                  FStar_SMTEncoding_Term.rng = uu____3876;_}::[])
               ->
               (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                  (FStar_Errors.Warning_QuantifierWithoutPattern,
                    "Not encoding deeply embedded, unguarded quantifier to SMT");
                (tm, decls))
           | uu____3922 ->
               let uu____3923 = encode_formula t env1  in
               (match uu____3923 with
                | (phi,decls') ->
                    let interp =
                      match vars with
                      | [] ->
                          let uu____3943 =
                            let uu____3948 =
                              FStar_SMTEncoding_Term.mk_Valid tm  in
                            (uu____3948, phi)  in
                          FStar_SMTEncoding_Util.mkIff uu____3943
                      | uu____3949 ->
                          let uu____3950 =
                            let uu____3961 =
                              let uu____3962 =
                                let uu____3967 =
                                  FStar_SMTEncoding_Term.mk_Valid tm  in
                                (uu____3967, phi)  in
                              FStar_SMTEncoding_Util.mkIff uu____3962  in
                            ([[valid_tm]], vars, uu____3961)  in
                          FStar_SMTEncoding_Term.mkForall
                            t.FStar_Syntax_Syntax.pos uu____3950
                       in
                    let ax =
                      let uu____3977 =
                        let uu____3985 =
                          let uu____3987 =
                            FStar_Util.digest_of_string tkey_hash  in
                          Prims.op_Hat "l_quant_interp_" uu____3987  in
                        (interp,
                          (FStar_Pervasives_Native.Some
                             "Interpretation of deeply embedded quantifier"),
                          uu____3985)
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____3977  in
                    let uu____3993 =
                      let uu____3994 =
                        let uu____3997 =
                          FStar_SMTEncoding_Term.mk_decls "" tkey_hash 
                            [ax] (FStar_List.append decls decls')
                           in
                        FStar_List.append decls' uu____3997  in
                      FStar_List.append decls uu____3994  in
                    (tm, uu____3993)))

and (encode_term :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____4009 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____4009
       then
         let uu____4014 = FStar_Syntax_Print.tag_of_term t  in
         let uu____4016 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____4018 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____4014 uu____4016
           uu____4018
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____4027 ->
           let uu____4050 =
             let uu____4052 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____4055 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____4057 = FStar_Syntax_Print.term_to_string t0  in
             let uu____4059 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____4052
               uu____4055 uu____4057 uu____4059
              in
           failwith uu____4050
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____4066 =
             let uu____4068 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____4071 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____4073 = FStar_Syntax_Print.term_to_string t0  in
             let uu____4075 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____4068
               uu____4071 uu____4073 uu____4075
              in
           failwith uu____4066
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let e = FStar_Syntax_Util.unfold_lazy i  in
           ((let uu____4085 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____4085
             then
               let uu____4090 = FStar_Syntax_Print.term_to_string t0  in
               let uu____4092 = FStar_Syntax_Print.term_to_string e  in
               FStar_Util.print2 ">> Unfolded (%s) ~> (%s)\n" uu____4090
                 uu____4092
             else ());
            encode_term e env)
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____4098 =
             let uu____4100 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____4100
              in
           failwith uu____4098
       | FStar_Syntax_Syntax.Tm_ascribed (t1,(k,uu____4109),uu____4110) ->
           let uu____4159 =
             match k with
             | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
             | uu____4169 -> false  in
           if uu____4159
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t1 env
       | FStar_Syntax_Syntax.Tm_quoted (qt,uu____4187) ->
           let tv =
             let uu____4193 =
               let uu____4200 = FStar_Reflection_Basic.inspect_ln qt  in
               FStar_Syntax_Embeddings.embed
                 FStar_Reflection_Embeddings.e_term_view uu____4200
                in
             uu____4193 t.FStar_Syntax_Syntax.pos
               FStar_Pervasives_Native.None
               FStar_Syntax_Embeddings.id_norm_cb
              in
           ((let uu____4227 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____4227
             then
               let uu____4232 = FStar_Syntax_Print.term_to_string t0  in
               let uu____4234 = FStar_Syntax_Print.term_to_string tv  in
               FStar_Util.print2 ">> Inspected (%s) ~> (%s)\n" uu____4232
                 uu____4234
             else ());
            (let t1 =
               let uu____4242 =
                 let uu____4253 = FStar_Syntax_Syntax.as_arg tv  in
                 [uu____4253]  in
               FStar_Syntax_Util.mk_app
                 (FStar_Reflection_Data.refl_constant_term
                    FStar_Reflection_Data.fstar_refl_pack_ln) uu____4242
                in
             encode_term t1 env))
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_pattern uu____4279) ->
           encode_term t1
             (let uu___17_4297 = env  in
              {
                FStar_SMTEncoding_Env.bvar_bindings =
                  (uu___17_4297.FStar_SMTEncoding_Env.bvar_bindings);
                FStar_SMTEncoding_Env.fvar_bindings =
                  (uu___17_4297.FStar_SMTEncoding_Env.fvar_bindings);
                FStar_SMTEncoding_Env.depth =
                  (uu___17_4297.FStar_SMTEncoding_Env.depth);
                FStar_SMTEncoding_Env.tcenv =
                  (uu___17_4297.FStar_SMTEncoding_Env.tcenv);
                FStar_SMTEncoding_Env.warn =
                  (uu___17_4297.FStar_SMTEncoding_Env.warn);
                FStar_SMTEncoding_Env.nolabels =
                  (uu___17_4297.FStar_SMTEncoding_Env.nolabels);
                FStar_SMTEncoding_Env.use_zfuel_name =
                  (uu___17_4297.FStar_SMTEncoding_Env.use_zfuel_name);
                FStar_SMTEncoding_Env.encode_non_total_function_typ =
                  (uu___17_4297.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                FStar_SMTEncoding_Env.current_module_name =
                  (uu___17_4297.FStar_SMTEncoding_Env.current_module_name);
                FStar_SMTEncoding_Env.encoding_quantifier = false;
                FStar_SMTEncoding_Env.global_cache =
                  (uu___17_4297.FStar_SMTEncoding_Env.global_cache)
              })
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____4300) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = FStar_SMTEncoding_Env.lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____4308 = head_redex env t  in
           if uu____4308
           then let uu____4315 = whnf env t  in encode_term uu____4315 env
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
              let uu____4322 =
                if
                  fvb.FStar_SMTEncoding_Env.smt_arity > (Prims.parse_int "0")
                then
                  match tok.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.FreeV uu____4346 ->
                      let sym_name =
                        let uu____4357 =
                          FStar_Util.digest_of_string tkey_hash  in
                        Prims.op_Hat "@kick_partial_app_" uu____4357  in
                      let uu____4360 =
                        let uu____4363 =
                          let uu____4364 =
                            let uu____4372 =
                              FStar_SMTEncoding_Term.kick_partial_app tok  in
                            (uu____4372,
                              (FStar_Pervasives_Native.Some
                                 "kick_partial_app"), sym_name)
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____4364  in
                        [uu____4363]  in
                      (uu____4360, sym_name)
                  | FStar_SMTEncoding_Term.App (uu____4379,[]) ->
                      let sym_name =
                        let uu____4384 =
                          FStar_Util.digest_of_string tkey_hash  in
                        Prims.op_Hat "@kick_partial_app_" uu____4384  in
                      let uu____4387 =
                        let uu____4390 =
                          let uu____4391 =
                            let uu____4399 =
                              FStar_SMTEncoding_Term.kick_partial_app tok  in
                            (uu____4399,
                              (FStar_Pervasives_Native.Some
                                 "kick_partial_app"), sym_name)
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____4391  in
                        [uu____4390]  in
                      (uu____4387, sym_name)
                  | uu____4406 -> ([], "")
                else ([], "")  in
              match uu____4322 with
              | (aux_decls,sym_name) ->
                  let uu____4429 =
                    if aux_decls = []
                    then
                      FStar_All.pipe_right []
                        FStar_SMTEncoding_Term.mk_decls_trivial
                    else
                      FStar_SMTEncoding_Term.mk_decls sym_name tkey_hash
                        aux_decls []
                     in
                  (tok, uu____4429))
       | FStar_Syntax_Syntax.Tm_type uu____4437 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4439) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.FStar_SMTEncoding_Env.current_module_name
              in
           let uu____4469 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____4469 with
            | (binders1,res) ->
                let uu____4480 =
                  (env.FStar_SMTEncoding_Env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____4480
                then
                  let uu____4487 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____4487 with
                   | (vars,guards,env',decls,uu____4512) ->
                       let fsym =
                         let uu____4526 =
                           let uu____4532 =
                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                               module_name "f"
                              in
                           (uu____4532, FStar_SMTEncoding_Term.Term_sort)  in
                         FStar_SMTEncoding_Term.mk_fv uu____4526  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____4538 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___18_4547 =
                              env.FStar_SMTEncoding_Env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___18_4547.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___18_4547.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___18_4547.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___18_4547.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___18_4547.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___18_4547.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___18_4547.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___18_4547.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___18_4547.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___18_4547.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___18_4547.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___18_4547.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___18_4547.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___18_4547.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___18_4547.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___18_4547.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___18_4547.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___18_4547.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___18_4547.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___18_4547.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___18_4547.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___18_4547.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___18_4547.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___18_4547.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___18_4547.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___18_4547.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___18_4547.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___18_4547.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___18_4547.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___18_4547.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___18_4547.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___18_4547.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___18_4547.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___18_4547.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___18_4547.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___18_4547.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___18_4547.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___18_4547.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___18_4547.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___18_4547.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___18_4547.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___18_4547.FStar_TypeChecker_Env.nbe)
                            }) res
                          in
                       (match uu____4538 with
                        | (pre_opt,res_t) ->
                            let uu____4559 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____4559 with
                             | (res_pred,decls') ->
                                 let uu____4570 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____4583 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____4583, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____4587 =
                                         encode_formula pre env'  in
                                       (match uu____4587 with
                                        | (guard,decls0) ->
                                            let uu____4600 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____4600, decls0))
                                    in
                                 (match uu____4570 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____4614 =
                                          let uu____4625 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____4625)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t.FStar_Syntax_Syntax.pos
                                          uu____4614
                                         in
                                      let cvars =
                                        let uu____4645 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____4645
                                          (FStar_List.filter
                                             (fun x  ->
                                                let uu____4664 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    x
                                                   in
                                                let uu____4666 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    fsym
                                                   in
                                                uu____4664 <> uu____4666))
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
                                        let uu____4688 =
                                          FStar_Util.digest_of_string
                                            tkey_hash
                                           in
                                        Prims.op_Hat "Tm_arrow_" uu____4688
                                         in
                                      let cvar_sorts =
                                        FStar_List.map
                                          FStar_SMTEncoding_Term.fv_sort
                                          cvars
                                         in
                                      let caption =
                                        let uu____4703 =
                                          FStar_Options.log_queries ()  in
                                        if uu____4703
                                        then
                                          let uu____4706 =
                                            let uu____4708 =
                                              FStar_TypeChecker_Normalize.term_to_string
                                                env.FStar_SMTEncoding_Env.tcenv
                                                t0
                                               in
                                            FStar_Util.replace_char
                                              uu____4708 10 32
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____4706
                                        else FStar_Pervasives_Native.None  in
                                      let tdecl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (tsym, cvar_sorts,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            caption)
                                         in
                                      let t1 =
                                        let uu____4721 =
                                          let uu____4729 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              cvars
                                             in
                                          (tsym, uu____4729)  in
                                        FStar_SMTEncoding_Util.mkApp
                                          uu____4721
                                         in
                                      let t_has_kind =
                                        FStar_SMTEncoding_Term.mk_HasType t1
                                          FStar_SMTEncoding_Term.mk_Term_type
                                         in
                                      let k_assumption =
                                        let a_name =
                                          Prims.op_Hat "kinding_" tsym  in
                                        let uu____4748 =
                                          let uu____4756 =
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              ([[t_has_kind]], cvars,
                                                t_has_kind)
                                             in
                                          (uu____4756,
                                            (FStar_Pervasives_Native.Some
                                               a_name), a_name)
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____4748
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
                                        let uu____4773 =
                                          let uu____4781 =
                                            let uu____4782 =
                                              let uu____4793 =
                                                let uu____4794 =
                                                  let uu____4799 =
                                                    let uu____4800 =
                                                      FStar_SMTEncoding_Term.mk_PreType
                                                        f
                                                       in
                                                    FStar_SMTEncoding_Term.mk_tester
                                                      "Tm_arrow" uu____4800
                                                     in
                                                  (f_has_t, uu____4799)  in
                                                FStar_SMTEncoding_Util.mkImp
                                                  uu____4794
                                                 in
                                              ([[f_has_t]], (fsym :: cvars),
                                                uu____4793)
                                               in
                                            let uu____4818 =
                                              mkForall_fuel module_name
                                                t0.FStar_Syntax_Syntax.pos
                                               in
                                            uu____4818 uu____4782  in
                                          (uu____4781,
                                            (FStar_Pervasives_Native.Some
                                               "pre-typing for functions"),
                                            (Prims.op_Hat module_name
                                               (Prims.op_Hat "_" a_name)))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____4773
                                         in
                                      let t_interp1 =
                                        let a_name =
                                          Prims.op_Hat "interpretation_" tsym
                                           in
                                        let uu____4841 =
                                          let uu____4849 =
                                            let uu____4850 =
                                              let uu____4861 =
                                                FStar_SMTEncoding_Util.mkIff
                                                  (f_has_t_z, t_interp)
                                                 in
                                              ([[f_has_t_z]], (fsym ::
                                                cvars), uu____4861)
                                               in
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              uu____4850
                                             in
                                          (uu____4849,
                                            (FStar_Pervasives_Native.Some
                                               a_name),
                                            (Prims.op_Hat module_name
                                               (Prims.op_Hat "_" a_name)))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____4841
                                         in
                                      let t_decls1 =
                                        [tdecl;
                                        k_assumption;
                                        pre_typing;
                                        t_interp1]  in
                                      let uu____4884 =
                                        let uu____4885 =
                                          let uu____4888 =
                                            let uu____4891 =
                                              FStar_SMTEncoding_Term.mk_decls
                                                tsym tkey_hash t_decls1
                                                (FStar_List.append decls
                                                   (FStar_List.append decls'
                                                      guard_decls))
                                               in
                                            FStar_List.append guard_decls
                                              uu____4891
                                             in
                                          FStar_List.append decls' uu____4888
                                           in
                                        FStar_List.append decls uu____4885
                                         in
                                      (t1, uu____4884)))))
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
                     let uu____4912 =
                       let uu____4920 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____4920,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"), a_name)
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____4912  in
                   let fsym =
                     FStar_SMTEncoding_Term.mk_fv
                       ("f", FStar_SMTEncoding_Term.Term_sort)
                      in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.op_Hat "pre_typing_" tsym  in
                     let uu____4933 =
                       let uu____4941 =
                         let uu____4942 =
                           let uu____4953 =
                             let uu____4954 =
                               let uu____4959 =
                                 let uu____4960 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____4960
                                  in
                               (f_has_t, uu____4959)  in
                             FStar_SMTEncoding_Util.mkImp uu____4954  in
                           ([[f_has_t]], [fsym], uu____4953)  in
                         let uu____4986 =
                           mkForall_fuel module_name
                             t0.FStar_Syntax_Syntax.pos
                            in
                         uu____4986 uu____4942  in
                       (uu____4941, (FStar_Pervasives_Native.Some a_name),
                         a_name)
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____4933  in
                   let uu____5003 =
                     FStar_All.pipe_right [tdecl; t_kinding; t_interp]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                      in
                   (t1, uu____5003)))
       | FStar_Syntax_Syntax.Tm_refine uu____5006 ->
           let uu____5013 =
             let uu____5018 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Env.Weak;
                 FStar_TypeChecker_Env.HNF;
                 FStar_TypeChecker_Env.EraseUniverses]
                 env.FStar_SMTEncoding_Env.tcenv t0
                in
             match uu____5018 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____5025;
                 FStar_Syntax_Syntax.vars = uu____5026;_} ->
                 let uu____5033 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____5033 with
                  | (b,f1) ->
                      let uu____5058 =
                        let uu____5059 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____5059  in
                      (uu____5058, f1))
             | uu____5074 -> failwith "impossible"  in
           (match uu____5013 with
            | (x,f) ->
                let uu____5086 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____5086 with
                 | (base_t,decls) ->
                     let uu____5097 =
                       FStar_SMTEncoding_Env.gen_term_var env x  in
                     (match uu____5097 with
                      | (x1,xtm,env') ->
                          let uu____5114 = encode_formula f env'  in
                          (match uu____5114 with
                           | (refinement,decls') ->
                               let uu____5125 =
                                 FStar_SMTEncoding_Env.fresh_fvar
                                   env.FStar_SMTEncoding_Env.current_module_name
                                   "f" FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____5125 with
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
                                      let uu____5153 =
                                        let uu____5164 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____5175 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____5164
                                          uu____5175
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____5153
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun y  ->
                                              (let uu____5229 =
                                                 FStar_SMTEncoding_Term.fv_name
                                                   y
                                                  in
                                               uu____5229 <> x1) &&
                                                (let uu____5233 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     y
                                                    in
                                                 uu____5233 <> fsym)))
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
                                      let uu____5269 =
                                        FStar_Util.digest_of_string tkey_hash
                                         in
                                      Prims.op_Hat "Tm_refine_" uu____5269
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
                                      let uu____5289 =
                                        let uu____5297 =
                                          FStar_List.map
                                            FStar_SMTEncoding_Util.mkFreeV
                                            cvars1
                                           in
                                        (tsym, uu____5297)  in
                                      FStar_SMTEncoding_Util.mkApp uu____5289
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
                                      let uu____5317 =
                                        let uu____5325 =
                                          let uu____5326 =
                                            let uu____5337 =
                                              FStar_SMTEncoding_Util.mkIff
                                                (t_haseq_ref, t_haseq_base)
                                               in
                                            ([[t_haseq_ref]], cvars1,
                                              uu____5337)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            t0.FStar_Syntax_Syntax.pos
                                            uu____5326
                                           in
                                        (uu____5325,
                                          (FStar_Pervasives_Native.Some
                                             (Prims.op_Hat "haseq for " tsym)),
                                          (Prims.op_Hat "haseq" tsym))
                                         in
                                      FStar_SMTEncoding_Util.mkAssume
                                        uu____5317
                                       in
                                    let t_kinding =
                                      let uu____5351 =
                                        let uu____5359 =
                                          FStar_SMTEncoding_Term.mkForall
                                            t0.FStar_Syntax_Syntax.pos
                                            ([[t_has_kind]], cvars1,
                                              t_has_kind)
                                           in
                                        (uu____5359,
                                          (FStar_Pervasives_Native.Some
                                             "refinement kinding"),
                                          (Prims.op_Hat "refinement_kinding_"
                                             tsym))
                                         in
                                      FStar_SMTEncoding_Util.mkAssume
                                        uu____5351
                                       in
                                    let t_interp =
                                      let uu____5373 =
                                        let uu____5381 =
                                          let uu____5382 =
                                            let uu____5393 =
                                              FStar_SMTEncoding_Util.mkIff
                                                (x_has_t, encoding)
                                               in
                                            ([[x_has_t]], (ffv :: xfv ::
                                              cvars1), uu____5393)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            t0.FStar_Syntax_Syntax.pos
                                            uu____5382
                                           in
                                        (uu____5381,
                                          (FStar_Pervasives_Native.Some
                                             "refinement_interpretation"),
                                          (Prims.op_Hat
                                             "refinement_interpretation_"
                                             tsym))
                                         in
                                      FStar_SMTEncoding_Util.mkAssume
                                        uu____5373
                                       in
                                    let t_decls1 =
                                      [tdecl; t_kinding; t_interp; t_haseq1]
                                       in
                                    let uu____5425 =
                                      let uu____5426 =
                                        let uu____5429 =
                                          FStar_SMTEncoding_Term.mk_decls
                                            tsym tkey_hash t_decls1
                                            (FStar_List.append decls decls')
                                           in
                                        FStar_List.append decls' uu____5429
                                         in
                                      FStar_List.append decls uu____5426  in
                                    (t1, uu____5425))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,uu____5433) ->
           let ttm =
             let uu____5451 =
               FStar_Syntax_Unionfind.uvar_id
                 uv.FStar_Syntax_Syntax.ctx_uvar_head
                in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____5451  in
           let uu____5453 =
             encode_term_pred FStar_Pervasives_Native.None
               uv.FStar_Syntax_Syntax.ctx_uvar_typ env ttm
              in
           (match uu____5453 with
            | (t_has_k,decls) ->
                let d =
                  let uu____5465 =
                    let uu____5473 =
                      let uu____5475 =
                        let uu____5477 =
                          let uu____5479 =
                            FStar_Syntax_Unionfind.uvar_id
                              uv.FStar_Syntax_Syntax.ctx_uvar_head
                             in
                          FStar_Util.string_of_int uu____5479  in
                        FStar_Util.format1 "uvar_typing_%s" uu____5477  in
                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                        uu____5475
                       in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____5473)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____5465  in
                let uu____5485 =
                  let uu____5486 =
                    FStar_All.pipe_right [d]
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append decls uu____5486  in
                (ttm, uu____5485))
       | FStar_Syntax_Syntax.Tm_app uu____5493 ->
           let uu____5510 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____5510 with
            | (head1,args_e) ->
                let uu____5557 =
                  let uu____5572 =
                    let uu____5573 = FStar_Syntax_Subst.compress head1  in
                    uu____5573.FStar_Syntax_Syntax.n  in
                  (uu____5572, args_e)  in
                (match uu____5557 with
                 | uu____5590 when head_redex env head1 ->
                     let uu____5605 = whnf env t  in
                     encode_term uu____5605 env
                 | uu____5606 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____5629 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5647) when
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
                       FStar_Syntax_Syntax.pos = uu____5669;
                       FStar_Syntax_Syntax.vars = uu____5670;_},uu____5671),uu____5672)
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
                       FStar_Syntax_Syntax.pos = uu____5698;
                       FStar_Syntax_Syntax.vars = uu____5699;_},uu____5700),
                    (v0,uu____5702)::(v1,uu____5704)::(v2,uu____5706)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____5777 = encode_term v0 env  in
                     (match uu____5777 with
                      | (v01,decls0) ->
                          let uu____5788 = encode_term v1 env  in
                          (match uu____5788 with
                           | (v11,decls1) ->
                               let uu____5799 = encode_term v2 env  in
                               (match uu____5799 with
                                | (v21,decls2) ->
                                    let uu____5810 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____5810,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(v0,uu____5813)::(v1,uu____5815)::(v2,uu____5817)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____5884 = encode_term v0 env  in
                     (match uu____5884 with
                      | (v01,decls0) ->
                          let uu____5895 = encode_term v1 env  in
                          (match uu____5895 with
                           | (v11,decls1) ->
                               let uu____5906 = encode_term v2 env  in
                               (match uu____5906 with
                                | (v21,decls2) ->
                                    let uu____5917 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____5917,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____5919)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____5955)::(rng,uu____5957)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____6008) ->
                     let e0 =
                       let uu____6030 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg
                         env.FStar_SMTEncoding_Env.tcenv head1 uu____6030
                        in
                     ((let uu____6040 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug
                              env.FStar_SMTEncoding_Env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____6040
                       then
                         let uu____6045 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____6045
                       else ());
                      (let e =
                         let uu____6053 =
                           let uu____6058 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____6059 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____6058
                             uu____6059
                            in
                         uu____6053 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____6070),(arg,uu____6072)::[]) -> encode_term arg env
                 | uu____6107 ->
                     let uu____6122 = encode_args args_e env  in
                     (match uu____6122 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____6183 = encode_term head1 env  in
                            match uu____6183 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____6255 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____6255 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____6353  ->
                                                 fun uu____6354  ->
                                                   match (uu____6353,
                                                           uu____6354)
                                                   with
                                                   | ((bv,uu____6384),
                                                      (a,uu____6386)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____6416 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____6416
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____6417 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm
                                             in
                                          (match uu____6417 with
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
                                                 let uu____6434 =
                                                   let uu____6442 =
                                                     FStar_SMTEncoding_Term.mkForall
                                                       t0.FStar_Syntax_Syntax.pos
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____6451 =
                                                     let uu____6453 =
                                                       let uu____6455 =
                                                         FStar_SMTEncoding_Term.hash_of_term
                                                           app_tm
                                                          in
                                                       FStar_Util.digest_of_string
                                                         uu____6455
                                                        in
                                                     Prims.op_Hat
                                                       "partial_app_typing_"
                                                       uu____6453
                                                      in
                                                   (uu____6442,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____6451)
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____6434
                                                  in
                                               let uu____6461 =
                                                 let uu____6464 =
                                                   let uu____6467 =
                                                     let uu____6470 =
                                                       FStar_SMTEncoding_Term.mk_decls
                                                         "" tkey_hash
                                                         [e_typing]
                                                         (FStar_List.append
                                                            decls
                                                            (FStar_List.append
                                                               decls' decls''))
                                                        in
                                                     FStar_List.append
                                                       decls'' uu____6470
                                                      in
                                                   FStar_List.append decls'
                                                     uu____6467
                                                    in
                                                 FStar_List.append decls
                                                   uu____6464
                                                  in
                                               (app_tm, uu____6461))))
                             in
                          let encode_full_app fv =
                            let uu____6490 =
                              FStar_SMTEncoding_Env.lookup_free_var_sym env
                                fv
                               in
                            match uu____6490 with
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
                                   FStar_Syntax_Syntax.pos = uu____6533;
                                   FStar_Syntax_Syntax.vars = uu____6534;_},uu____6535)
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
                                   FStar_Syntax_Syntax.pos = uu____6542;
                                   FStar_Syntax_Syntax.vars = uu____6543;_},uu____6544)
                                ->
                                let uu____6549 =
                                  let uu____6550 =
                                    let uu____6555 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____6555
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____6550
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____6549
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____6585 =
                                  let uu____6586 =
                                    let uu____6591 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____6591
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____6586
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____6585
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____6620,(FStar_Util.Inl t1,uu____6622),uu____6623)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____6670,(FStar_Util.Inr c,uu____6672),uu____6673)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____6720 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____6741 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Env.Weak;
                                     FStar_TypeChecker_Env.HNF;
                                     FStar_TypeChecker_Env.EraseUniverses]
                                     env.FStar_SMTEncoding_Env.tcenv
                                     head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____6741
                                  in
                               let uu____6742 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____6742 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____6758;
                                            FStar_Syntax_Syntax.vars =
                                              uu____6759;_},uu____6760)
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
                                     | uu____6778 ->
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
           let uu____6857 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____6857 with
            | (bs1,body1,opening) ->
                let fallback uu____6880 =
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
                  let uu____6890 =
                    let uu____6891 =
                      FStar_SMTEncoding_Term.mk_fv
                        (f, FStar_SMTEncoding_Term.Term_sort)
                       in
                    FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV
                      uu____6891
                     in
                  let uu____6893 =
                    FStar_All.pipe_right [decl]
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  (uu____6890, uu____6893)  in
                let is_impure rc =
                  let uu____6903 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                      env.FStar_SMTEncoding_Env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____6903 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____6918 =
                          let uu____6931 =
                            FStar_TypeChecker_Env.get_range
                              env.FStar_SMTEncoding_Env.tcenv
                             in
                          FStar_TypeChecker_Util.new_implicit_var
                            "SMTEncoding codomain" uu____6931
                            env.FStar_SMTEncoding_Env.tcenv
                            FStar_Syntax_Util.ktype0
                           in
                        (match uu____6918 with
                         | (t1,uu____6934,uu____6935) -> t1)
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  let uu____6953 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                     in
                  if uu____6953
                  then
                    let uu____6958 = FStar_Syntax_Syntax.mk_Total res_typ  in
                    FStar_Pervasives_Native.Some uu____6958
                  else
                    (let uu____6961 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid
                        in
                     if uu____6961
                     then
                       let uu____6966 = FStar_Syntax_Syntax.mk_GTotal res_typ
                          in
                       FStar_Pervasives_Native.Some uu____6966
                     else FStar_Pervasives_Native.None)
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____6974 =
                         let uu____6980 =
                           let uu____6982 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____6982
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____6980)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____6974);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____6987 =
                       (is_impure rc) &&
                         (let uu____6990 =
                            FStar_TypeChecker_Env.is_reifiable_rc
                              env.FStar_SMTEncoding_Env.tcenv rc
                             in
                          Prims.op_Negation uu____6990)
                        in
                     if uu____6987
                     then fallback ()
                     else
                       (let uu____6999 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____6999 with
                        | (vars,guards,envbody,decls,uu____7024) ->
                            let body2 =
                              let uu____7038 =
                                FStar_TypeChecker_Env.is_reifiable_rc
                                  env.FStar_SMTEncoding_Env.tcenv rc
                                 in
                              if uu____7038
                              then
                                FStar_TypeChecker_Util.reify_body
                                  env.FStar_SMTEncoding_Env.tcenv body1
                              else body1  in
                            let uu____7043 = encode_term body2 envbody  in
                            (match uu____7043 with
                             | (body3,decls') ->
                                 let uu____7054 =
                                   let uu____7063 = codomain_eff rc  in
                                   match uu____7063 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____7082 = encode_term tfun env
                                          in
                                       (match uu____7082 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____7054 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____7116 =
                                          let uu____7127 =
                                            let uu____7128 =
                                              let uu____7133 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____7133, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____7128
                                             in
                                          ([], vars, uu____7127)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t0.FStar_Syntax_Syntax.pos
                                          uu____7116
                                         in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body
                                         in
                                      let uu____7141 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            (cvars, key_body)
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____7157 =
                                              let uu____7160 =
                                                let uu____7171 =
                                                  FStar_SMTEncoding_Term.free_variables
                                                    t1
                                                   in
                                                FStar_List.append uu____7171
                                                  cvars
                                                 in
                                              FStar_Util.remove_dups
                                                FStar_SMTEncoding_Term.fv_eq
                                                uu____7160
                                               in
                                            let uu____7198 =
                                              FStar_SMTEncoding_Util.mkAnd
                                                (key_body, t1)
                                               in
                                            (uu____7157, uu____7198)
                                         in
                                      (match uu____7141 with
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
                                           let uu____7220 =
                                             is_an_eta_expansion env vars
                                               body3
                                              in
                                           (match uu____7220 with
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
                                                  let uu____7236 =
                                                    FStar_Util.digest_of_string
                                                      tkey_hash
                                                     in
                                                  Prims.op_Hat "Tm_abs_"
                                                    uu____7236
                                                   in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None)
                                                   in
                                                let f =
                                                  let uu____7245 =
                                                    let uu____7253 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    (fsym, uu____7253)  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____7245
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
                                                      let uu____7270 =
                                                        let uu____7271 =
                                                          let uu____7279 =
                                                            FStar_SMTEncoding_Term.mkForall
                                                              t0.FStar_Syntax_Syntax.pos
                                                              ([[f]], cvars1,
                                                                f_has_t)
                                                             in
                                                          (uu____7279,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name)
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____7271
                                                         in
                                                      [uu____7270]
                                                   in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.op_Hat
                                                      "interpretation_" fsym
                                                     in
                                                  let uu____7294 =
                                                    let uu____7302 =
                                                      let uu____7303 =
                                                        let uu____7314 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3)
                                                           in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____7314)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        t0.FStar_Syntax_Syntax.pos
                                                        uu____7303
                                                       in
                                                    (uu____7302,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____7294
                                                   in
                                                let f_decls =
                                                  FStar_List.append (fdecl ::
                                                    typing_f) [interp_f]
                                                   in
                                                let uu____7328 =
                                                  let uu____7329 =
                                                    let uu____7332 =
                                                      let uu____7335 =
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
                                                        decls'' uu____7335
                                                       in
                                                    FStar_List.append decls'
                                                      uu____7332
                                                     in
                                                  FStar_List.append decls
                                                    uu____7329
                                                   in
                                                (f, uu____7328))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____7338,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____7339;
                          FStar_Syntax_Syntax.lbunivs = uu____7340;
                          FStar_Syntax_Syntax.lbtyp = uu____7341;
                          FStar_Syntax_Syntax.lbeff = uu____7342;
                          FStar_Syntax_Syntax.lbdef = uu____7343;
                          FStar_Syntax_Syntax.lbattrs = uu____7344;
                          FStar_Syntax_Syntax.lbpos = uu____7345;_}::uu____7346),uu____7347)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____7381;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____7383;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____7385;
                FStar_Syntax_Syntax.lbpos = uu____7386;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____7413 ->
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
              let uu____7485 =
                let uu____7490 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____7490 env  in
              match uu____7485 with
              | (ee1,decls1) ->
                  let uu____7515 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____7515 with
                   | (xs,e21) ->
                       let uu____7540 = FStar_List.hd xs  in
                       (match uu____7540 with
                        | (x1,uu____7558) ->
                            let env' =
                              FStar_SMTEncoding_Env.push_term_var env x1 ee1
                               in
                            let uu____7564 = encode_body e21 env'  in
                            (match uu____7564 with
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
            let uu____7594 =
              let uu____7602 =
                let uu____7603 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____7603  in
              FStar_SMTEncoding_Env.gen_term_var env uu____7602  in
            match uu____7594 with
            | (scrsym,scr',env1) ->
                let uu____7613 = encode_term e env1  in
                (match uu____7613 with
                 | (scr,decls) ->
                     let uu____7624 =
                       let encode_branch b uu____7653 =
                         match uu____7653 with
                         | (else_case,decls1) ->
                             let uu____7672 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____7672 with
                              | (p,w,br) ->
                                  let uu____7698 = encode_pat env1 p  in
                                  (match uu____7698 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____7735  ->
                                                   match uu____7735 with
                                                   | (x,t) ->
                                                       FStar_SMTEncoding_Env.push_term_var
                                                         env2 x t) env1)
                                          in
                                       let uu____7742 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____7764 =
                                               encode_term w1 env2  in
                                             (match uu____7764 with
                                              | (w2,decls2) ->
                                                  let uu____7777 =
                                                    let uu____7778 =
                                                      let uu____7783 =
                                                        let uu____7784 =
                                                          let uu____7789 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____7789)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____7784
                                                         in
                                                      (guard, uu____7783)  in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____7778
                                                     in
                                                  (uu____7777, decls2))
                                          in
                                       (match uu____7742 with
                                        | (guard1,decls2) ->
                                            let uu____7804 =
                                              encode_br br env2  in
                                            (match uu____7804 with
                                             | (br1,decls3) ->
                                                 let uu____7817 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____7817,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____7624 with
                      | (match_tm,decls1) ->
                          let uu____7838 =
                            let uu____7839 =
                              let uu____7850 =
                                let uu____7857 =
                                  let uu____7862 =
                                    FStar_SMTEncoding_Term.mk_fv
                                      (scrsym,
                                        FStar_SMTEncoding_Term.Term_sort)
                                     in
                                  (uu____7862, scr)  in
                                [uu____7857]  in
                              (uu____7850, match_tm)  in
                            FStar_SMTEncoding_Term.mkLet' uu____7839
                              FStar_Range.dummyRange
                             in
                          (uu____7838, decls1)))

and (encode_pat :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.pat -> (FStar_SMTEncoding_Env.env_t * pattern))
  =
  fun env  ->
    fun pat  ->
      (let uu____7885 =
         FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
           FStar_Options.Medium
          in
       if uu____7885
       then
         let uu____7888 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____7888
       else ());
      (let uu____7893 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____7893 with
       | (vars,pat_term) ->
           let uu____7910 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____7952  ->
                     fun v1  ->
                       match uu____7952 with
                       | (env1,vars1) ->
                           let uu____7988 =
                             FStar_SMTEncoding_Env.gen_term_var env1 v1  in
                           (match uu____7988 with
                            | (xx,uu____8007,env2) ->
                                let uu____8011 =
                                  let uu____8018 =
                                    let uu____8023 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xx,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    (v1, uu____8023)  in
                                  uu____8018 :: vars1  in
                                (env2, uu____8011))) (env, []))
              in
           (match uu____7910 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____8078 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____8079 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____8080 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____8088 = encode_const c env1  in
                      (match uu____8088 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____8096::uu____8097 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____8101 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon
                            env1.FStar_SMTEncoding_Env.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____8124 =
                          FStar_TypeChecker_Env.datacons_of_typ
                            env1.FStar_SMTEncoding_Env.tcenv tc_name
                           in
                        match uu____8124 with
                        | (uu____8132,uu____8133::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____8138 ->
                            FStar_SMTEncoding_Env.mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____8174  ->
                                  match uu____8174 with
                                  | (arg,uu____8184) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____8193 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____8193))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____8225) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____8256 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____8281 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____8327  ->
                                  match uu____8327 with
                                  | (arg,uu____8343) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____8352 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____8352))
                         in
                      FStar_All.pipe_right uu____8281 FStar_List.flatten
                   in
                let pat_term1 uu____8383 = encode_term pat_term env1  in
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
      let uu____8393 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____8441  ->
                fun uu____8442  ->
                  match (uu____8441, uu____8442) with
                  | ((tms,decls),(t,uu____8482)) ->
                      let uu____8509 = encode_term t env  in
                      (match uu____8509 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____8393 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____8566 = FStar_Syntax_Util.list_elements e  in
        match uu____8566 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____8597 =
          let uu____8614 = FStar_Syntax_Util.unmeta p  in
          FStar_All.pipe_right uu____8614 FStar_Syntax_Util.head_and_args  in
        match uu____8597 with
        | (head1,args) ->
            let uu____8665 =
              let uu____8680 =
                let uu____8681 = FStar_Syntax_Util.un_uinst head1  in
                uu____8681.FStar_Syntax_Syntax.n  in
              (uu____8680, args)  in
            (match uu____8665 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____8703,uu____8704)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____8756 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or1 t1 =
          let uu____8811 =
            let uu____8828 = FStar_Syntax_Util.unmeta t1  in
            FStar_All.pipe_right uu____8828 FStar_Syntax_Util.head_and_args
             in
          match uu____8811 with
          | (head1,args) ->
              let uu____8875 =
                let uu____8890 =
                  let uu____8891 = FStar_Syntax_Util.un_uinst head1  in
                  uu____8891.FStar_Syntax_Syntax.n  in
                (uu____8890, args)  in
              (match uu____8875 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____8910)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____8947 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____8977 = smt_pat_or1 t1  in
            (match uu____8977 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____8999 = list_elements1 e  in
                 FStar_All.pipe_right uu____8999
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____9029 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____9029
                           (FStar_List.map one_pat)))
             | uu____9052 ->
                 let uu____9057 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____9057])
        | uu____9108 ->
            let uu____9111 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____9111]
         in
      let uu____9162 =
        let uu____9177 =
          let uu____9178 = FStar_Syntax_Subst.compress t  in
          uu____9178.FStar_Syntax_Syntax.n  in
        match uu____9177 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____9217 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____9217 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____9252;
                        FStar_Syntax_Syntax.effect_name = uu____9253;
                        FStar_Syntax_Syntax.result_typ = uu____9254;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____9256)::(post,uu____9258)::(pats,uu____9260)::[];
                        FStar_Syntax_Syntax.flags = uu____9261;_}
                      ->
                      let uu____9322 = lemma_pats pats  in
                      (binders1, pre, post, uu____9322)
                  | uu____9333 -> failwith "impos"))
        | uu____9349 -> failwith "Impos"  in
      match uu____9162 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___19_9386 = env  in
            {
              FStar_SMTEncoding_Env.bvar_bindings =
                (uu___19_9386.FStar_SMTEncoding_Env.bvar_bindings);
              FStar_SMTEncoding_Env.fvar_bindings =
                (uu___19_9386.FStar_SMTEncoding_Env.fvar_bindings);
              FStar_SMTEncoding_Env.depth =
                (uu___19_9386.FStar_SMTEncoding_Env.depth);
              FStar_SMTEncoding_Env.tcenv =
                (uu___19_9386.FStar_SMTEncoding_Env.tcenv);
              FStar_SMTEncoding_Env.warn =
                (uu___19_9386.FStar_SMTEncoding_Env.warn);
              FStar_SMTEncoding_Env.nolabels =
                (uu___19_9386.FStar_SMTEncoding_Env.nolabels);
              FStar_SMTEncoding_Env.use_zfuel_name = true;
              FStar_SMTEncoding_Env.encode_non_total_function_typ =
                (uu___19_9386.FStar_SMTEncoding_Env.encode_non_total_function_typ);
              FStar_SMTEncoding_Env.current_module_name =
                (uu___19_9386.FStar_SMTEncoding_Env.current_module_name);
              FStar_SMTEncoding_Env.encoding_quantifier =
                (uu___19_9386.FStar_SMTEncoding_Env.encoding_quantifier);
              FStar_SMTEncoding_Env.global_cache =
                (uu___19_9386.FStar_SMTEncoding_Env.global_cache)
            }  in
          let uu____9388 =
            encode_binders FStar_Pervasives_Native.None binders env1  in
          (match uu____9388 with
           | (vars,guards,env2,decls,uu____9413) ->
               let uu____9426 = encode_smt_patterns patterns env2  in
               (match uu____9426 with
                | (pats,decls') ->
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
                    let env3 =
                      let uu___20_9453 = env2  in
                      {
                        FStar_SMTEncoding_Env.bvar_bindings =
                          (uu___20_9453.FStar_SMTEncoding_Env.bvar_bindings);
                        FStar_SMTEncoding_Env.fvar_bindings =
                          (uu___20_9453.FStar_SMTEncoding_Env.fvar_bindings);
                        FStar_SMTEncoding_Env.depth =
                          (uu___20_9453.FStar_SMTEncoding_Env.depth);
                        FStar_SMTEncoding_Env.tcenv =
                          (uu___20_9453.FStar_SMTEncoding_Env.tcenv);
                        FStar_SMTEncoding_Env.warn =
                          (uu___20_9453.FStar_SMTEncoding_Env.warn);
                        FStar_SMTEncoding_Env.nolabels = true;
                        FStar_SMTEncoding_Env.use_zfuel_name =
                          (uu___20_9453.FStar_SMTEncoding_Env.use_zfuel_name);
                        FStar_SMTEncoding_Env.encode_non_total_function_typ =
                          (uu___20_9453.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                        FStar_SMTEncoding_Env.current_module_name =
                          (uu___20_9453.FStar_SMTEncoding_Env.current_module_name);
                        FStar_SMTEncoding_Env.encoding_quantifier =
                          (uu___20_9453.FStar_SMTEncoding_Env.encoding_quantifier);
                        FStar_SMTEncoding_Env.global_cache =
                          (uu___20_9453.FStar_SMTEncoding_Env.global_cache)
                      }  in
                    let uu____9455 =
                      let uu____9460 = FStar_Syntax_Util.unmeta pre  in
                      encode_formula uu____9460 env3  in
                    (match uu____9455 with
                     | (pre1,decls'') ->
                         let uu____9467 =
                           let uu____9472 = FStar_Syntax_Util.unmeta post1
                              in
                           encode_formula uu____9472 env3  in
                         (match uu____9467 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append decls'
                                     (FStar_List.append decls'' decls'''))
                                 in
                              let uu____9482 =
                                let uu____9483 =
                                  let uu____9494 =
                                    let uu____9495 =
                                      let uu____9500 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards)
                                         in
                                      (uu____9500, post2)  in
                                    FStar_SMTEncoding_Util.mkImp uu____9495
                                     in
                                  (pats, vars, uu____9494)  in
                                FStar_SMTEncoding_Term.mkForall
                                  t.FStar_Syntax_Syntax.pos uu____9483
                                 in
                              (uu____9482, decls1)))))

and (encode_smt_patterns :
  FStar_Syntax_Syntax.arg Prims.list Prims.list ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term Prims.list Prims.list *
        FStar_SMTEncoding_Term.decls_t))
  =
  fun pats_l  ->
    fun env  ->
      let env1 =
        let uu___21_9520 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___21_9520.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___21_9520.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___21_9520.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___21_9520.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___21_9520.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___21_9520.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___21_9520.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___21_9520.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___21_9520.FStar_SMTEncoding_Env.encoding_quantifier);
          FStar_SMTEncoding_Env.global_cache =
            (uu___21_9520.FStar_SMTEncoding_Env.global_cache)
        }  in
      let encode_smt_pattern t =
        let uu____9536 = FStar_Syntax_Util.head_and_args t  in
        match uu____9536 with
        | (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____9599::(x,uu____9601)::(t1,uu____9603)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____9670 = encode_term x env1  in
                 (match uu____9670 with
                  | (x1,decls) ->
                      let uu____9681 = encode_term t1 env1  in
                      (match uu____9681 with
                       | (t2,decls') ->
                           let uu____9692 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                           (uu____9692, (FStar_List.append decls decls'))))
             | uu____9693 -> encode_term t env1)
         in
      FStar_List.fold_right
        (fun pats  ->
           fun uu____9736  ->
             match uu____9736 with
             | (pats_l1,decls) ->
                 let uu____9781 =
                   FStar_List.fold_right
                     (fun uu____9816  ->
                        fun uu____9817  ->
                          match (uu____9816, uu____9817) with
                          | ((p,uu____9859),(pats1,decls1)) ->
                              let uu____9894 = encode_smt_pattern p  in
                              (match uu____9894 with
                               | (t,d) ->
                                   let uu____9909 =
                                     FStar_SMTEncoding_Term.check_pattern_ok
                                       t
                                      in
                                   (match uu____9909 with
                                    | FStar_Pervasives_Native.None  ->
                                        ((t :: pats1),
                                          (FStar_List.append d decls1))
                                    | FStar_Pervasives_Native.Some
                                        illegal_subterm ->
                                        ((let uu____9926 =
                                            let uu____9932 =
                                              let uu____9934 =
                                                FStar_Syntax_Print.term_to_string
                                                  p
                                                 in
                                              let uu____9936 =
                                                FStar_SMTEncoding_Term.print_smt_term
                                                  illegal_subterm
                                                 in
                                              FStar_Util.format2
                                                "Pattern %s contains illegal sub-term (%s); dropping it"
                                                uu____9934 uu____9936
                                               in
                                            (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                                              uu____9932)
                                             in
                                          FStar_Errors.log_issue
                                            p.FStar_Syntax_Syntax.pos
                                            uu____9926);
                                         (pats1,
                                           (FStar_List.append d decls1))))))
                     pats ([], decls)
                    in
                 (match uu____9781 with
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
        let uu____9996 =
          FStar_All.pipe_left
            (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____9996
        then
          let uu____10001 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____10003 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10001 uu____10003
        else ()  in
      let enc f r l =
        let uu____10045 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10077 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____10077 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____10045 with
        | (decls,args) ->
            let uu____10108 =
              let uu___22_10109 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___22_10109.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___22_10109.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10108, decls)
         in
      let const_op f r uu____10144 =
        let uu____10157 = f r  in (uu____10157, [])  in
      let un_op f l =
        let uu____10180 = FStar_List.hd l  in
        FStar_All.pipe_left f uu____10180  in
      let bin_op f uu___13_10200 =
        match uu___13_10200 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10211 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____10252 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____10277  ->
                 match uu____10277 with
                 | (t,uu____10293) ->
                     let uu____10298 = encode_formula t env  in
                     (match uu____10298 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____10252 with
        | (decls,phis) ->
            let uu____10327 =
              let uu___23_10328 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___23_10328.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___23_10328.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10327, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____10391  ->
               match uu____10391 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____10412) -> false
                    | uu____10415 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____10434 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____10434
        else
          (let uu____10451 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____10451 r rf)
         in
      let eq3_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____10523 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::t1::v0::v1::[] ->
                     let uu____10555 =
                       let uu____10560 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____10561 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____10560, uu____10561)  in
                     FStar_SMTEncoding_Util.mkAnd uu____10555
                 | uu____10562 -> failwith "Impossible")
             in
          uu____10523 r args
        else
          (let uu____10568 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____10568)
         in
      let h_equals_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____10640 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::v0::t1::v1::[] ->
                     let uu____10672 =
                       let uu____10677 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____10678 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____10677, uu____10678)  in
                     FStar_SMTEncoding_Util.mkAnd uu____10672
                 | uu____10679 -> failwith "Impossible")
             in
          uu____10640 r args
        else
          (let uu____10685 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____10685)
         in
      let mk_imp1 r uu___14_10720 =
        match uu___14_10720 with
        | (lhs,uu____10726)::(rhs,uu____10728)::[] ->
            let uu____10769 = encode_formula rhs env  in
            (match uu____10769 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____10784) ->
                      (l1, decls1)
                  | uu____10789 ->
                      let uu____10790 = encode_formula lhs env  in
                      (match uu____10790 with
                       | (l2,decls2) ->
                           let uu____10801 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____10801, (FStar_List.append decls1 decls2)))))
        | uu____10802 -> failwith "impossible"  in
      let mk_ite r uu___15_10830 =
        match uu___15_10830 with
        | (guard,uu____10836)::(_then,uu____10838)::(_else,uu____10840)::[]
            ->
            let uu____10897 = encode_formula guard env  in
            (match uu____10897 with
             | (g,decls1) ->
                 let uu____10908 = encode_formula _then env  in
                 (match uu____10908 with
                  | (t,decls2) ->
                      let uu____10919 = encode_formula _else env  in
                      (match uu____10919 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____10931 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____10961 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l
           in
        f uu____10961  in
      let connectives =
        let uu____10991 =
          let uu____11016 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____11016)  in
        let uu____11059 =
          let uu____11086 =
            let uu____11111 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____11111)  in
          let uu____11154 =
            let uu____11181 =
              let uu____11208 =
                let uu____11233 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____11233)  in
              let uu____11276 =
                let uu____11303 =
                  let uu____11330 =
                    let uu____11355 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____11355)  in
                  [uu____11330;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.c_eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq3_op);
                  (FStar_Parser_Const.c_eq3_lid, h_equals_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11303  in
              uu____11208 :: uu____11276  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11181  in
          uu____11086 :: uu____11154  in
        uu____10991 :: uu____11059  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____11900 = encode_formula phi' env  in
            (match uu____11900 with
             | (phi2,decls) ->
                 let uu____11911 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____11911, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____11913 ->
            let uu____11920 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____11920 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____11959 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____11959 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____11971;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____11973;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____11975;
                 FStar_Syntax_Syntax.lbpos = uu____11976;_}::[]),e2)
            ->
            let uu____12003 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____12003 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____12056::(x,uu____12058)::(t,uu____12060)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12127 = encode_term x env  in
                 (match uu____12127 with
                  | (x1,decls) ->
                      let uu____12138 = encode_term t env  in
                      (match uu____12138 with
                       | (t1,decls') ->
                           let uu____12149 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____12149, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12152)::(msg,uu____12154)::(phi2,uu____12156)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12223 =
                   let uu____12228 =
                     let uu____12229 = FStar_Syntax_Subst.compress r  in
                     uu____12229.FStar_Syntax_Syntax.n  in
                   let uu____12232 =
                     let uu____12233 = FStar_Syntax_Subst.compress msg  in
                     uu____12233.FStar_Syntax_Syntax.n  in
                   (uu____12228, uu____12232)  in
                 (match uu____12223 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12242))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____12253 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____12260)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____12295 when head_redex env head2 ->
                 let uu____12310 = whnf env phi1  in
                 encode_formula uu____12310 env
             | uu____12311 ->
                 let uu____12326 = encode_term phi1 env  in
                 (match uu____12326 with
                  | (tt,decls) ->
                      let tt1 =
                        let uu____12338 =
                          let uu____12340 =
                            FStar_Range.use_range
                              tt.FStar_SMTEncoding_Term.rng
                             in
                          let uu____12341 =
                            FStar_Range.use_range
                              phi1.FStar_Syntax_Syntax.pos
                             in
                          FStar_Range.rng_included uu____12340 uu____12341
                           in
                        if uu____12338
                        then tt
                        else
                          (let uu___24_12345 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___24_12345.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___24_12345.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      let uu____12346 = FStar_SMTEncoding_Term.mk_Valid tt1
                         in
                      (uu____12346, decls)))
        | uu____12347 ->
            let uu____12348 = encode_term phi1 env  in
            (match uu____12348 with
             | (tt,decls) ->
                 let tt1 =
                   let uu____12360 =
                     let uu____12362 =
                       FStar_Range.use_range tt.FStar_SMTEncoding_Term.rng
                        in
                     let uu____12363 =
                       FStar_Range.use_range phi1.FStar_Syntax_Syntax.pos  in
                     FStar_Range.rng_included uu____12362 uu____12363  in
                   if uu____12360
                   then tt
                   else
                     (let uu___25_12367 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___25_12367.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___25_12367.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 let uu____12368 = FStar_SMTEncoding_Term.mk_Valid tt1  in
                 (uu____12368, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____12412 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____12412 with
        | (vars,guards,env2,decls,uu____12451) ->
            let uu____12464 = encode_smt_patterns ps env2  in
            (match uu____12464 with
             | (pats,decls') ->
                 let uu____12501 = encode_formula body env2  in
                 (match uu____12501 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12533;
                             FStar_SMTEncoding_Term.rng = uu____12534;_}::[])::[]
                            when
                            let uu____12554 =
                              FStar_Ident.text_of_lid
                                FStar_Parser_Const.guard_free
                               in
                            uu____12554 = gf -> []
                        | uu____12557 -> guards  in
                      let uu____12562 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____12562, body1,
                        (FStar_List.append decls
                           (FStar_List.append decls' decls'')))))
         in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi  in
       let uu____12573 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____12573 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12582 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____12688  ->
                     match uu____12688 with
                     | (l,uu____12713) -> FStar_Ident.lid_equals op l))
              in
           (match uu____12582 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____12782,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____12874 = encode_q_body env vars pats body  in
             match uu____12874 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____12919 =
                     let uu____12930 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____12930)  in
                   FStar_SMTEncoding_Term.mkForall
                     phi1.FStar_Syntax_Syntax.pos uu____12919
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____12961 = encode_q_body env vars pats body  in
             match uu____12961 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____13005 =
                   let uu____13006 =
                     let uu____13017 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____13017)  in
                   FStar_SMTEncoding_Term.mkExists
                     phi1.FStar_Syntax_Syntax.pos uu____13006
                    in
                 (uu____13005, decls))))
