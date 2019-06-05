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
        fun uu____45  ->
          match uu____45 with
          | (pats,vars,body) ->
              let fallback uu____73 =
                FStar_SMTEncoding_Term.mkForall r (pats, vars, body)  in
              let uu____78 = FStar_Options.unthrottle_inductives ()  in
              if uu____78
              then fallback ()
              else
                (let uu____83 =
                   FStar_SMTEncoding_Env.fresh_fvar mname "f"
                     FStar_SMTEncoding_Term.Fuel_sort
                    in
                 match uu____83 with
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
                               | uu____123 -> p))
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
                                 let uu____144 = add_fuel1 guards  in
                                 FStar_SMTEncoding_Util.mk_and_l uu____144
                             | uu____147 ->
                                 let uu____148 = add_fuel1 [guard]  in
                                 FStar_All.pipe_right uu____148 FStar_List.hd
                              in
                           FStar_SMTEncoding_Util.mkImp (guard1, body')
                       | uu____153 -> body  in
                     let vars1 =
                       let uu____165 =
                         FStar_SMTEncoding_Term.mk_fv
                           (fsym, FStar_SMTEncoding_Term.Fuel_sort)
                          in
                       uu____165 :: vars  in
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
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____292 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____311;
             FStar_Syntax_Syntax.vars = uu____312;_},uu____313)
          ->
          let uu____338 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____338 FStar_Option.isNone
      | uu____356 -> false
  
let (head_redex :
  FStar_SMTEncoding_Env.env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____370 =
        let uu____371 = FStar_Syntax_Util.un_uinst t  in
        uu____371.FStar_Syntax_Syntax.n  in
      match uu____370 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____375,uu____376,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___0_401  ->
                  match uu___0_401 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____404 -> false) rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____407 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____407 FStar_Option.isSome
      | uu____425 -> false
  
let (whnf :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____438 = head_normal env t  in
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
    let uu____460 =
      let uu____461 = FStar_Syntax_Syntax.null_binder t  in [uu____461]  in
    let uu____480 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    FStar_Syntax_Util.abs uu____460 uu____480 FStar_Pervasives_Native.None
  
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
                let uu____502 = FStar_SMTEncoding_Term.fv_sort var  in
                match uu____502 with
                | FStar_SMTEncoding_Term.Fuel_sort  ->
                    let uu____503 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____503
                | s ->
                    let uu____506 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____506) e)
  
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
          let uu____562 =
            let uu____568 =
              let uu____570 = FStar_Util.string_of_int arity  in
              let uu____572 = FStar_Util.string_of_int n_args  in
              FStar_Util.format3
                "Head symbol %s expects at least %s arguments; got only %s"
                head1 uu____570 uu____572
               in
            (FStar_Errors.Fatal_SMTEncodingArityMismatch, uu____568)  in
          FStar_Errors.raise_error uu____562 rng
  
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
                  (let uu____621 = FStar_Util.first_N arity args  in
                   match uu____621 with
                   | (args1,rest) ->
                       let head3 =
                         FStar_SMTEncoding_Util.mkApp' (head2, args1)  in
                       mk_Apply_args head3 rest)
                else
                  (let uu____645 = FStar_SMTEncoding_Term.op_to_string head2
                      in
                   raise_arity_mismatch uu____645 arity n_args rng)
  
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
          let uu____668 = FStar_SMTEncoding_Env.force_thunk fvb  in
          mk_Apply_args uu____668 args
        else
          maybe_curry_app rng
            (FStar_Util.Inl
               (FStar_SMTEncoding_Term.Var (fvb.FStar_SMTEncoding_Env.smt_id)))
            fvb.FStar_SMTEncoding_Env.smt_arity args
  
let (is_app : FStar_SMTEncoding_Term.op -> Prims.bool) =
  fun uu___1_677  ->
    match uu___1_677 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____683 -> false
  
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
                       FStar_SMTEncoding_Term.freevars = uu____731;
                       FStar_SMTEncoding_Term.rng = uu____732;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____763) ->
              let uu____773 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____790 -> false) args (FStar_List.rev xs))
                 in
              if uu____773
              then FStar_SMTEncoding_Env.tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____797,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t  in
              let uu____801 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____809 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars
                           in
                        Prims.op_Negation uu____809))
                 in
              if uu____801
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____816 -> FStar_Pervasives_Native.None  in
        check_partial_applications body (FStar_List.rev vars)
  
let check_pattern_vars :
  'Auu____834 'Auu____835 .
    FStar_SMTEncoding_Env.env_t ->
      (FStar_Syntax_Syntax.bv * 'Auu____834) Prims.list ->
        (FStar_Syntax_Syntax.term * 'Auu____835) Prims.list -> unit
  =
  fun env  ->
    fun vars  ->
      fun pats  ->
        let pats1 =
          FStar_All.pipe_right pats
            (FStar_List.map
               (fun uu____893  ->
                  match uu____893 with
                  | (x,uu____899) ->
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
              let uu____907 = FStar_Syntax_Free.names hd1  in
              FStar_List.fold_left
                (fun out  ->
                   fun x  ->
                     let uu____919 = FStar_Syntax_Free.names x  in
                     FStar_Util.set_union out uu____919) uu____907 tl1
               in
            let uu____922 =
              FStar_All.pipe_right vars
                (FStar_Util.find_opt
                   (fun uu____949  ->
                      match uu____949 with
                      | (b,uu____956) ->
                          let uu____957 = FStar_Util.set_mem b pat_vars  in
                          Prims.op_Negation uu____957))
               in
            (match uu____922 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some (x,uu____964) ->
                 let pos =
                   FStar_List.fold_left
                     (fun out  ->
                        fun t  ->
                          FStar_Range.union_ranges out
                            t.FStar_Syntax_Syntax.pos)
                     hd1.FStar_Syntax_Syntax.pos tl1
                    in
                 let uu____978 =
                   let uu____984 =
                     let uu____986 = FStar_Syntax_Print.bv_to_string x  in
                     FStar_Util.format1
                       "SMT pattern misses at least one bound variable: %s"
                       uu____986
                      in
                   (FStar_Errors.Warning_SMTPatternIllFormed, uu____984)  in
                 FStar_Errors.log_issue pos uu____978)
  
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
        | FStar_Syntax_Syntax.Tm_arrow uu____1272 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____1287 ->
            let uu____1294 = FStar_Syntax_Util.unrefine t1  in
            aux true uu____1294
        | uu____1296 ->
            if norm1
            then let uu____1298 = whnf env t1  in aux false uu____1298
            else
              (let uu____1302 =
                 let uu____1304 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let uu____1306 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____1304 uu____1306
                  in
               failwith uu____1302)
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
    | FStar_Syntax_Syntax.Tm_refine (bv,uu____1348) ->
        let uu____1353 =
          curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort  in
        (match uu____1353 with
         | (args,res) ->
             (match args with
              | [] ->
                  let uu____1374 = FStar_Syntax_Syntax.mk_Total k1  in
                  ([], uu____1374)
              | uu____1381 -> (args, res)))
    | uu____1382 ->
        let uu____1383 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____1383)
  
let is_arithmetic_primitive :
  'Auu____1397 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____1397 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1420::uu____1421::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1425::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____1428 -> false
  
let (isInteger : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____1459 -> false
  
let (getInteger : FStar_Syntax_Syntax.term' -> Prims.int) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____1482 -> failwith "Expected an Integer term"
  
let is_BitVector_primitive :
  'Auu____1492 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____1492)
        Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____1534)::uu____1535::uu____1536::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____1587)::uu____1588::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____1625 -> false
  
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
          let uu____1956 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue  in
          (uu____1956, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____1958 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse  in
          (uu____1958, [])
      | FStar_Const.Const_char c1 ->
          let uu____1961 =
            let uu____1962 =
              let uu____1970 =
                let uu____1973 =
                  let uu____1974 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1)
                     in
                  FStar_SMTEncoding_Term.boxInt uu____1974  in
                [uu____1973]  in
              ("FStar.Char.__char_of_int", uu____1970)  in
            FStar_SMTEncoding_Util.mkApp uu____1962  in
          (uu____1961, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____1992 =
            let uu____1993 = FStar_SMTEncoding_Util.mkInteger i  in
            FStar_SMTEncoding_Term.boxInt uu____1993  in
          (uu____1992, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.FStar_SMTEncoding_Env.tcenv).FStar_TypeChecker_Env.dsenv
              repr sw FStar_Range.dummyRange
             in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____2014) ->
          let uu____2017 =
            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.string_const s
             in
          (uu____2017, [])
      | FStar_Const.Const_range uu____2018 ->
          let uu____2019 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          (uu____2019, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | FStar_Const.Const_real r ->
          let uu____2022 =
            let uu____2023 = FStar_SMTEncoding_Util.mkReal r  in
            FStar_SMTEncoding_Term.boxReal uu____2023  in
          (uu____2022, [])
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
            let unary unbox arg_tms1 =
              let uu____2459 = FStar_List.hd arg_tms1  in unbox uu____2459
               in
            let binary unbox arg_tms1 =
              let uu____2484 =
                let uu____2485 = FStar_List.hd arg_tms1  in unbox uu____2485
                 in
              let uu____2486 =
                let uu____2487 =
                  let uu____2488 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____2488  in
                unbox uu____2487  in
              (uu____2484, uu____2486)  in
            let mk_default uu____2496 =
              let uu____2497 =
                FStar_SMTEncoding_Env.lookup_free_var_sym env
                  head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____2497 with
              | (fname,fuel_args,arity) ->
                  let args = FStar_List.append fuel_args arg_tms  in
                  maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity
                    args
               in
            let mk_l box op mk_args ts =
              let uu____2586 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____2586
              then
                let uu____2589 =
                  let uu____2590 = mk_args ts  in op uu____2590  in
                FStar_All.pipe_right uu____2589 box
              else mk_default ()  in
            let mk_nl box unbox nm op ts =
              let uu____2648 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____2648
              then
                let uu____2651 = binary unbox ts  in
                match uu____2651 with
                | (t1,t2) ->
                    let uu____2658 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____2658 box
              else
                (let uu____2664 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____2664
                 then
                   let uu____2667 =
                     let uu____2668 = binary unbox ts  in op uu____2668  in
                   FStar_All.pipe_right uu____2667 box
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
            let uu____3103 =
              let uu____3113 =
                FStar_List.tryFind
                  (fun uu____3137  ->
                     match uu____3137 with
                     | (l,uu____3148) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____3113 FStar_Util.must  in
            (match uu____3103 with
             | (uu____3192,op) ->
                 let uu____3204 = op arg_tms  in (uu____3204, decls))

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
        let uu____3220 = FStar_List.hd args_e  in
        match uu____3220 with
        | (tm_sz,uu____3236) ->
            let uu____3245 = uu____3220  in
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let t_decls1 = FStar_SMTEncoding_Term.mkBvConstructor sz  in
              FStar_SMTEncoding_Term.mk_decls "" sz_key t_decls1 []  in
            let uu____3256 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____3282::(sz_arg,uu____3284)::uu____3285::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____3352 =
                    let uu____3353 = FStar_List.tail args_e  in
                    FStar_List.tail uu____3353  in
                  let uu____3380 =
                    let uu____3384 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____3384  in
                  (uu____3352, uu____3380)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____3391::(sz_arg,uu____3393)::uu____3394::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____3461 =
                    let uu____3463 = FStar_Syntax_Print.term_to_string sz_arg
                       in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____3463
                     in
                  failwith uu____3461
              | uu____3473 ->
                  let uu____3488 = FStar_List.tail args_e  in
                  (uu____3488, FStar_Pervasives_Native.None)
               in
            (match uu____3256 with
             | (arg_tms,ext_sz) ->
                 let uu____3515 = encode_args arg_tms env  in
                 (match uu____3515 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____3536 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____3548 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____3548  in
                      let unary_arith arg_tms2 =
                        let uu____3559 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____3559  in
                      let binary arg_tms2 =
                        let uu____3574 =
                          let uu____3575 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3575
                           in
                        let uu____3576 =
                          let uu____3577 =
                            let uu____3578 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____3578  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3577
                           in
                        (uu____3574, uu____3576)  in
                      let binary_arith arg_tms2 =
                        let uu____3595 =
                          let uu____3596 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3596
                           in
                        let uu____3597 =
                          let uu____3598 =
                            let uu____3599 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____3599  in
                          FStar_SMTEncoding_Term.unboxInt uu____3598  in
                        (uu____3595, uu____3597)  in
                      let mk_bv op mk_args resBox ts =
                        let uu____3657 =
                          let uu____3658 = mk_args ts  in op uu____3658  in
                        FStar_All.pipe_right uu____3657 resBox  in
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
                        let uu____3790 =
                          let uu____3795 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____3795  in
                        let uu____3804 =
                          let uu____3809 =
                            let uu____3811 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____3811  in
                          FStar_SMTEncoding_Term.boxBitVec uu____3809  in
                        mk_bv uu____3790 unary uu____3804 arg_tms2  in
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
                      let uu____4051 =
                        let uu____4061 =
                          FStar_List.tryFind
                            (fun uu____4085  ->
                               match uu____4085 with
                               | (l,uu____4096) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____4061 FStar_Util.must  in
                      (match uu____4051 with
                       | (uu____4142,op) ->
                           let uu____4154 = op arg_tms1  in
                           (uu____4154, (FStar_List.append sz_decls decls)))))

and (encode_deeply_embedded_quantifier :
  FStar_Syntax_Syntax.term ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let env1 =
        let uu___540_4164 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___540_4164.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___540_4164.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___540_4164.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___540_4164.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___540_4164.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___540_4164.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name =
            (uu___540_4164.FStar_SMTEncoding_Env.use_zfuel_name);
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___540_4164.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___540_4164.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier = true;
          FStar_SMTEncoding_Env.global_cache =
            (uu___540_4164.FStar_SMTEncoding_Env.global_cache)
        }  in
      let uu____4166 = encode_term t env1  in
      match uu____4166 with
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
               (uu____4192,{
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.FreeV uu____4193;
                             FStar_SMTEncoding_Term.freevars = uu____4194;
                             FStar_SMTEncoding_Term.rng = uu____4195;_}::
                {
                  FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV
                    uu____4196;
                  FStar_SMTEncoding_Term.freevars = uu____4197;
                  FStar_SMTEncoding_Term.rng = uu____4198;_}::[])
               ->
               (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                  (FStar_Errors.Warning_QuantifierWithoutPattern,
                    "Not encoding deeply embedded, unguarded quantifier to SMT");
                (tm, decls))
           | uu____4244 ->
               let uu____4245 =
                 encode_formula FStar_Pervasives_Native.None t env1  in
               (match uu____4245 with
                | (phi,decls') ->
                    let interp =
                      match vars with
                      | [] ->
                          let uu____4266 =
                            let uu____4271 =
                              FStar_SMTEncoding_Term.mk_Valid tm  in
                            (uu____4271, phi)  in
                          FStar_SMTEncoding_Util.mkIff uu____4266
                      | uu____4272 ->
                          let uu____4273 =
                            let uu____4284 =
                              let uu____4285 =
                                let uu____4290 =
                                  FStar_SMTEncoding_Term.mk_Valid tm  in
                                (uu____4290, phi)  in
                              FStar_SMTEncoding_Util.mkIff uu____4285  in
                            ([[valid_tm]], vars, uu____4284)  in
                          FStar_SMTEncoding_Term.mkForall
                            t.FStar_Syntax_Syntax.pos uu____4273
                       in
                    let ax =
                      let uu____4300 =
                        let uu____4308 =
                          let uu____4310 =
                            FStar_Util.digest_of_string tkey_hash  in
                          Prims.op_Hat "l_quant_interp_" uu____4310  in
                        (interp,
                          (FStar_Pervasives_Native.Some
                             "Interpretation of deeply embedded quantifier"),
                          uu____4308)
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____4300  in
                    let uu____4316 =
                      let uu____4317 =
                        let uu____4320 =
                          FStar_SMTEncoding_Term.mk_decls "" tkey_hash 
                            [ax] (FStar_List.append decls decls')
                           in
                        FStar_List.append decls' uu____4320  in
                      FStar_List.append decls uu____4317  in
                    (tm, uu____4316)))

and (encode_term :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____4332 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____4332
       then
         let uu____4337 = FStar_Syntax_Print.tag_of_term t  in
         let uu____4339 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____4341 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____4337 uu____4339
           uu____4341
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____4350 ->
           let uu____4373 =
             let uu____4375 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____4378 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____4380 = FStar_Syntax_Print.term_to_string t0  in
             let uu____4382 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____4375
               uu____4378 uu____4380 uu____4382
              in
           failwith uu____4373
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____4389 =
             let uu____4391 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____4394 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____4396 = FStar_Syntax_Print.term_to_string t0  in
             let uu____4398 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____4391
               uu____4394 uu____4396 uu____4398
              in
           failwith uu____4389
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let e = FStar_Syntax_Util.unfold_lazy i  in
           ((let uu____4408 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____4408
             then
               let uu____4413 = FStar_Syntax_Print.term_to_string t0  in
               let uu____4415 = FStar_Syntax_Print.term_to_string e  in
               FStar_Util.print2 ">> Unfolded (%s) ~> (%s)\n" uu____4413
                 uu____4415
             else ());
            encode_term e env)
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____4421 =
             let uu____4423 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____4423
              in
           failwith uu____4421
       | FStar_Syntax_Syntax.Tm_ascribed (t1,(k,uu____4432),uu____4433) ->
           let uu____4482 =
             match k with
             | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
             | uu____4492 -> false  in
           if uu____4482
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t1 env
       | FStar_Syntax_Syntax.Tm_quoted (qt,uu____4510) ->
           let tv =
             let uu____4516 =
               let uu____4523 = FStar_Reflection_Basic.inspect_ln qt  in
               FStar_Syntax_Embeddings.embed
                 FStar_Reflection_Embeddings.e_term_view uu____4523
                in
             uu____4516 t.FStar_Syntax_Syntax.pos
               FStar_Pervasives_Native.None
               FStar_Syntax_Embeddings.id_norm_cb
              in
           ((let uu____4527 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____4527
             then
               let uu____4532 = FStar_Syntax_Print.term_to_string t0  in
               let uu____4534 = FStar_Syntax_Print.term_to_string tv  in
               FStar_Util.print2 ">> Inspected (%s) ~> (%s)\n" uu____4532
                 uu____4534
             else ());
            (let t1 =
               let uu____4542 =
                 let uu____4553 = FStar_Syntax_Syntax.as_arg tv  in
                 [uu____4553]  in
               FStar_Syntax_Util.mk_app
                 (FStar_Reflection_Data.refl_constant_term
                    FStar_Reflection_Data.fstar_refl_pack_ln) uu____4542
                in
             encode_term t1 env))
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_pattern uu____4579) ->
           encode_term t1
             (let uu___612_4605 = env  in
              {
                FStar_SMTEncoding_Env.bvar_bindings =
                  (uu___612_4605.FStar_SMTEncoding_Env.bvar_bindings);
                FStar_SMTEncoding_Env.fvar_bindings =
                  (uu___612_4605.FStar_SMTEncoding_Env.fvar_bindings);
                FStar_SMTEncoding_Env.depth =
                  (uu___612_4605.FStar_SMTEncoding_Env.depth);
                FStar_SMTEncoding_Env.tcenv =
                  (uu___612_4605.FStar_SMTEncoding_Env.tcenv);
                FStar_SMTEncoding_Env.warn =
                  (uu___612_4605.FStar_SMTEncoding_Env.warn);
                FStar_SMTEncoding_Env.nolabels =
                  (uu___612_4605.FStar_SMTEncoding_Env.nolabels);
                FStar_SMTEncoding_Env.use_zfuel_name =
                  (uu___612_4605.FStar_SMTEncoding_Env.use_zfuel_name);
                FStar_SMTEncoding_Env.encode_non_total_function_typ =
                  (uu___612_4605.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                FStar_SMTEncoding_Env.current_module_name =
                  (uu___612_4605.FStar_SMTEncoding_Env.current_module_name);
                FStar_SMTEncoding_Env.encoding_quantifier = false;
                FStar_SMTEncoding_Env.global_cache =
                  (uu___612_4605.FStar_SMTEncoding_Env.global_cache)
              })
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____4608) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = FStar_SMTEncoding_Env.lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____4616 = head_redex env t  in
           if uu____4616
           then let uu____4623 = whnf env t  in encode_term uu____4623 env
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
              let uu____4630 =
                if
                  fvb.FStar_SMTEncoding_Env.smt_arity > (Prims.parse_int "0")
                then
                  match tok.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.FreeV uu____4654 ->
                      let sym_name =
                        let uu____4665 =
                          FStar_Util.digest_of_string tkey_hash  in
                        Prims.op_Hat "@kick_partial_app_" uu____4665  in
                      let uu____4668 =
                        let uu____4671 =
                          let uu____4672 =
                            let uu____4680 =
                              FStar_SMTEncoding_Term.kick_partial_app tok  in
                            (uu____4680,
                              (FStar_Pervasives_Native.Some
                                 "kick_partial_app"), sym_name)
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____4672  in
                        [uu____4671]  in
                      (uu____4668, sym_name)
                  | FStar_SMTEncoding_Term.App (uu____4687,[]) ->
                      let sym_name =
                        let uu____4692 =
                          FStar_Util.digest_of_string tkey_hash  in
                        Prims.op_Hat "@kick_partial_app_" uu____4692  in
                      let uu____4695 =
                        let uu____4698 =
                          let uu____4699 =
                            let uu____4707 =
                              FStar_SMTEncoding_Term.kick_partial_app tok  in
                            (uu____4707,
                              (FStar_Pervasives_Native.Some
                                 "kick_partial_app"), sym_name)
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____4699  in
                        [uu____4698]  in
                      (uu____4695, sym_name)
                  | uu____4714 -> ([], "")
                else ([], "")  in
              match uu____4630 with
              | (aux_decls,sym_name) ->
                  let uu____4737 =
                    if aux_decls = []
                    then
                      FStar_All.pipe_right []
                        FStar_SMTEncoding_Term.mk_decls_trivial
                    else
                      FStar_SMTEncoding_Term.mk_decls sym_name tkey_hash
                        aux_decls []
                     in
                  (tok, uu____4737))
       | FStar_Syntax_Syntax.Tm_type uu____4745 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4747) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.FStar_SMTEncoding_Env.current_module_name
              in
           let uu____4777 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____4777 with
            | (binders1,res) ->
                let uu____4788 =
                  (env.FStar_SMTEncoding_Env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____4788
                then
                  let uu____4795 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____4795 with
                   | (vars,guards,env',decls,uu____4820) ->
                       let fsym =
                         let uu____4834 =
                           let uu____4840 =
                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                               module_name "f"
                              in
                           (uu____4840, FStar_SMTEncoding_Term.Term_sort)  in
                         FStar_SMTEncoding_Term.mk_fv uu____4834  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____4846 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___666_4855 =
                              env.FStar_SMTEncoding_Env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___666_4855.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___666_4855.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___666_4855.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___666_4855.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___666_4855.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___666_4855.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___666_4855.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___666_4855.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___666_4855.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___666_4855.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___666_4855.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___666_4855.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___666_4855.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___666_4855.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___666_4855.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___666_4855.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___666_4855.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___666_4855.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___666_4855.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___666_4855.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___666_4855.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___666_4855.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___666_4855.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___666_4855.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___666_4855.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___666_4855.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___666_4855.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___666_4855.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___666_4855.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___666_4855.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___666_4855.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___666_4855.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___666_4855.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___666_4855.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___666_4855.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___666_4855.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___666_4855.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___666_4855.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___666_4855.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___666_4855.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___666_4855.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___666_4855.FStar_TypeChecker_Env.nbe)
                            }) res
                          in
                       (match uu____4846 with
                        | (pre_opt,res_t) ->
                            let uu____4867 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____4867 with
                             | (res_pred,decls') ->
                                 let uu____4878 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____4891 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____4891, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____4895 =
                                         encode_formula
                                           FStar_Pervasives_Native.None pre
                                           env'
                                          in
                                       (match uu____4895 with
                                        | (guard,decls0) ->
                                            let uu____4909 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____4909, decls0))
                                    in
                                 (match uu____4878 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____4923 =
                                          let uu____4934 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____4934)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t.FStar_Syntax_Syntax.pos
                                          uu____4923
                                         in
                                      let cvars =
                                        let uu____4954 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____4954
                                          (FStar_List.filter
                                             (fun x  ->
                                                let uu____4973 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    x
                                                   in
                                                let uu____4975 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    fsym
                                                   in
                                                uu____4973 <> uu____4975))
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
                                        let uu____4997 =
                                          FStar_Util.digest_of_string
                                            tkey_hash
                                           in
                                        Prims.op_Hat "Tm_arrow_" uu____4997
                                         in
                                      let cvar_sorts =
                                        FStar_List.map
                                          FStar_SMTEncoding_Term.fv_sort
                                          cvars
                                         in
                                      let caption =
                                        let uu____5012 =
                                          FStar_Options.log_queries ()  in
                                        if uu____5012
                                        then
                                          let uu____5015 =
                                            let uu____5017 =
                                              FStar_TypeChecker_Normalize.term_to_string
                                                env.FStar_SMTEncoding_Env.tcenv
                                                t0
                                               in
                                            FStar_Util.replace_char
                                              uu____5017 10 32
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____5015
                                        else FStar_Pervasives_Native.None  in
                                      let tdecl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (tsym, cvar_sorts,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            caption)
                                         in
                                      let t1 =
                                        let uu____5030 =
                                          let uu____5038 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              cvars
                                             in
                                          (tsym, uu____5038)  in
                                        FStar_SMTEncoding_Util.mkApp
                                          uu____5030
                                         in
                                      let t_has_kind =
                                        FStar_SMTEncoding_Term.mk_HasType t1
                                          FStar_SMTEncoding_Term.mk_Term_type
                                         in
                                      let k_assumption =
                                        let a_name =
                                          Prims.op_Hat "kinding_" tsym  in
                                        let uu____5057 =
                                          let uu____5065 =
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              ([[t_has_kind]], cvars,
                                                t_has_kind)
                                             in
                                          (uu____5065,
                                            (FStar_Pervasives_Native.Some
                                               a_name), a_name)
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____5057
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
                                        let uu____5082 =
                                          let uu____5090 =
                                            let uu____5091 =
                                              let uu____5102 =
                                                let uu____5103 =
                                                  let uu____5108 =
                                                    let uu____5109 =
                                                      FStar_SMTEncoding_Term.mk_PreType
                                                        f
                                                       in
                                                    FStar_SMTEncoding_Term.mk_tester
                                                      "Tm_arrow" uu____5109
                                                     in
                                                  (f_has_t, uu____5108)  in
                                                FStar_SMTEncoding_Util.mkImp
                                                  uu____5103
                                                 in
                                              ([[f_has_t]], (fsym :: cvars),
                                                uu____5102)
                                               in
                                            let uu____5127 =
                                              mkForall_fuel module_name
                                                t0.FStar_Syntax_Syntax.pos
                                               in
                                            uu____5127 uu____5091  in
                                          (uu____5090,
                                            (FStar_Pervasives_Native.Some
                                               "pre-typing for functions"),
                                            (Prims.op_Hat module_name
                                               (Prims.op_Hat "_" a_name)))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____5082
                                         in
                                      let t_interp1 =
                                        let a_name =
                                          Prims.op_Hat "interpretation_" tsym
                                           in
                                        let uu____5150 =
                                          let uu____5158 =
                                            let uu____5159 =
                                              let uu____5170 =
                                                FStar_SMTEncoding_Util.mkIff
                                                  (f_has_t_z, t_interp)
                                                 in
                                              ([[f_has_t_z]], (fsym ::
                                                cvars), uu____5170)
                                               in
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              uu____5159
                                             in
                                          (uu____5158,
                                            (FStar_Pervasives_Native.Some
                                               a_name),
                                            (Prims.op_Hat module_name
                                               (Prims.op_Hat "_" a_name)))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____5150
                                         in
                                      let t_decls1 =
                                        [tdecl;
                                        k_assumption;
                                        pre_typing;
                                        t_interp1]  in
                                      let uu____5193 =
                                        let uu____5194 =
                                          let uu____5197 =
                                            let uu____5200 =
                                              FStar_SMTEncoding_Term.mk_decls
                                                tsym tkey_hash t_decls1
                                                (FStar_List.append decls
                                                   (FStar_List.append decls'
                                                      guard_decls))
                                               in
                                            FStar_List.append guard_decls
                                              uu____5200
                                             in
                                          FStar_List.append decls' uu____5197
                                           in
                                        FStar_List.append decls uu____5194
                                         in
                                      (t1, uu____5193)))))
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
                     let uu____5221 =
                       let uu____5229 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____5229,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"), a_name)
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____5221  in
                   let fsym =
                     FStar_SMTEncoding_Term.mk_fv
                       ("f", FStar_SMTEncoding_Term.Term_sort)
                      in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.op_Hat "pre_typing_" tsym  in
                     let uu____5242 =
                       let uu____5250 =
                         let uu____5251 =
                           let uu____5262 =
                             let uu____5263 =
                               let uu____5268 =
                                 let uu____5269 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____5269
                                  in
                               (f_has_t, uu____5268)  in
                             FStar_SMTEncoding_Util.mkImp uu____5263  in
                           ([[f_has_t]], [fsym], uu____5262)  in
                         let uu____5295 =
                           mkForall_fuel module_name
                             t0.FStar_Syntax_Syntax.pos
                            in
                         uu____5295 uu____5251  in
                       (uu____5250, (FStar_Pervasives_Native.Some a_name),
                         a_name)
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____5242  in
                   let uu____5312 =
                     FStar_All.pipe_right [tdecl; t_kinding; t_interp]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                      in
                   (t1, uu____5312)))
       | FStar_Syntax_Syntax.Tm_refine uu____5315 ->
           let uu____5322 =
             let uu____5327 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Env.Weak;
                 FStar_TypeChecker_Env.HNF;
                 FStar_TypeChecker_Env.EraseUniverses]
                 env.FStar_SMTEncoding_Env.tcenv t0
                in
             match uu____5327 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____5334;
                 FStar_Syntax_Syntax.vars = uu____5335;_} ->
                 let uu____5342 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____5342 with
                  | (b,f1) ->
                      let uu____5367 =
                        let uu____5368 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____5368  in
                      (uu____5367, f1))
             | uu____5383 -> failwith "impossible"  in
           (match uu____5322 with
            | (x,f) ->
                let uu____5395 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____5395 with
                 | (base_t,decls) ->
                     let uu____5406 =
                       FStar_SMTEncoding_Env.gen_term_var env x  in
                     (match uu____5406 with
                      | (x1,xtm,env') ->
                          let uu____5423 =
                            encode_formula FStar_Pervasives_Native.None f
                              env'
                             in
                          (match uu____5423 with
                           | (refinement,decls') ->
                               let uu____5435 =
                                 FStar_SMTEncoding_Env.fresh_fvar
                                   env.FStar_SMTEncoding_Env.current_module_name
                                   "f" FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____5435 with
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
                                      let uu____5463 =
                                        let uu____5474 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____5485 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____5474
                                          uu____5485
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____5463
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun y  ->
                                              (let uu____5539 =
                                                 FStar_SMTEncoding_Term.fv_name
                                                   y
                                                  in
                                               uu____5539 <> x1) &&
                                                (let uu____5543 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     y
                                                    in
                                                 uu____5543 <> fsym)))
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
                                      let uu____5579 =
                                        FStar_Util.digest_of_string tkey_hash
                                         in
                                      Prims.op_Hat "Tm_refine_" uu____5579
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
                                      let uu____5599 =
                                        let uu____5607 =
                                          FStar_List.map
                                            FStar_SMTEncoding_Util.mkFreeV
                                            cvars1
                                           in
                                        (tsym, uu____5607)  in
                                      FStar_SMTEncoding_Util.mkApp uu____5599
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
                                      let uu____5627 =
                                        let uu____5635 =
                                          let uu____5636 =
                                            let uu____5647 =
                                              FStar_SMTEncoding_Util.mkIff
                                                (t_haseq_ref, t_haseq_base)
                                               in
                                            ([[t_haseq_ref]], cvars1,
                                              uu____5647)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            t0.FStar_Syntax_Syntax.pos
                                            uu____5636
                                           in
                                        (uu____5635,
                                          (FStar_Pervasives_Native.Some
                                             (Prims.op_Hat "haseq for " tsym)),
                                          (Prims.op_Hat "haseq" tsym))
                                         in
                                      FStar_SMTEncoding_Util.mkAssume
                                        uu____5627
                                       in
                                    let t_kinding =
                                      let uu____5661 =
                                        let uu____5669 =
                                          FStar_SMTEncoding_Term.mkForall
                                            t0.FStar_Syntax_Syntax.pos
                                            ([[t_has_kind]], cvars1,
                                              t_has_kind)
                                           in
                                        (uu____5669,
                                          (FStar_Pervasives_Native.Some
                                             "refinement kinding"),
                                          (Prims.op_Hat "refinement_kinding_"
                                             tsym))
                                         in
                                      FStar_SMTEncoding_Util.mkAssume
                                        uu____5661
                                       in
                                    let t_interp =
                                      let uu____5683 =
                                        let uu____5691 =
                                          let uu____5692 =
                                            let uu____5703 =
                                              FStar_SMTEncoding_Util.mkIff
                                                (x_has_t, encoding)
                                               in
                                            ([[x_has_t]], (ffv :: xfv ::
                                              cvars1), uu____5703)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            t0.FStar_Syntax_Syntax.pos
                                            uu____5692
                                           in
                                        (uu____5691,
                                          (FStar_Pervasives_Native.Some
                                             "refinement_interpretation"),
                                          (Prims.op_Hat
                                             "refinement_interpretation_"
                                             tsym))
                                         in
                                      FStar_SMTEncoding_Util.mkAssume
                                        uu____5683
                                       in
                                    let t_decls1 =
                                      [tdecl; t_kinding; t_interp; t_haseq1]
                                       in
                                    let uu____5735 =
                                      let uu____5736 =
                                        let uu____5739 =
                                          FStar_SMTEncoding_Term.mk_decls
                                            tsym tkey_hash t_decls1
                                            (FStar_List.append decls decls')
                                           in
                                        FStar_List.append decls' uu____5739
                                         in
                                      FStar_List.append decls uu____5736  in
                                    (t1, uu____5735))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,uu____5743) ->
           let ttm =
             let uu____5761 =
               FStar_Syntax_Unionfind.uvar_id
                 uv.FStar_Syntax_Syntax.ctx_uvar_head
                in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____5761  in
           let uu____5763 =
             encode_term_pred FStar_Pervasives_Native.None
               uv.FStar_Syntax_Syntax.ctx_uvar_typ env ttm
              in
           (match uu____5763 with
            | (t_has_k,decls) ->
                let d =
                  let uu____5775 =
                    let uu____5783 =
                      let uu____5785 =
                        let uu____5787 =
                          let uu____5789 =
                            FStar_Syntax_Unionfind.uvar_id
                              uv.FStar_Syntax_Syntax.ctx_uvar_head
                             in
                          FStar_Util.string_of_int uu____5789  in
                        FStar_Util.format1 "uvar_typing_%s" uu____5787  in
                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                        uu____5785
                       in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____5783)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____5775  in
                let uu____5795 =
                  let uu____5796 =
                    FStar_All.pipe_right [d]
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append decls uu____5796  in
                (ttm, uu____5795))
       | FStar_Syntax_Syntax.Tm_app uu____5803 ->
           let uu____5820 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____5820 with
            | (head1,args_e) ->
                let uu____5867 =
                  let uu____5882 =
                    let uu____5883 = FStar_Syntax_Subst.compress head1  in
                    uu____5883.FStar_Syntax_Syntax.n  in
                  (uu____5882, args_e)  in
                (match uu____5867 with
                 | uu____5900 when head_redex env head1 ->
                     let uu____5915 = whnf env t  in
                     encode_term uu____5915 env
                 | uu____5916 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____5939 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5957) when
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
                       FStar_Syntax_Syntax.pos = uu____5979;
                       FStar_Syntax_Syntax.vars = uu____5980;_},uu____5981),uu____5982)
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
                       FStar_Syntax_Syntax.pos = uu____6008;
                       FStar_Syntax_Syntax.vars = uu____6009;_},uu____6010),
                    (v0,uu____6012)::(v1,uu____6014)::(v2,uu____6016)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____6087 = encode_term v0 env  in
                     (match uu____6087 with
                      | (v01,decls0) ->
                          let uu____6098 = encode_term v1 env  in
                          (match uu____6098 with
                           | (v11,decls1) ->
                               let uu____6109 = encode_term v2 env  in
                               (match uu____6109 with
                                | (v21,decls2) ->
                                    let uu____6120 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____6120,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(v0,uu____6123)::(v1,uu____6125)::(v2,uu____6127)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____6194 = encode_term v0 env  in
                     (match uu____6194 with
                      | (v01,decls0) ->
                          let uu____6205 = encode_term v1 env  in
                          (match uu____6205 with
                           | (v11,decls1) ->
                               let uu____6216 = encode_term v2 env  in
                               (match uu____6216 with
                                | (v21,decls2) ->
                                    let uu____6227 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____6227,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____6229)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____6265)::(rng,uu____6267)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____6318) ->
                     let e0 =
                       let uu____6340 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg
                         env.FStar_SMTEncoding_Env.tcenv head1 uu____6340
                        in
                     ((let uu____6350 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug
                              env.FStar_SMTEncoding_Env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____6350
                       then
                         let uu____6355 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____6355
                       else ());
                      (let e =
                         let uu____6363 =
                           let uu____6368 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____6369 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____6368
                             uu____6369
                            in
                         uu____6363 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____6378),(arg,uu____6380)::[]) -> encode_term arg env
                 | uu____6415 ->
                     let uu____6430 = encode_args args_e env  in
                     (match uu____6430 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____6491 = encode_term head1 env  in
                            match uu____6491 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____6563 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____6563 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____6661  ->
                                                 fun uu____6662  ->
                                                   match (uu____6661,
                                                           uu____6662)
                                                   with
                                                   | ((bv,uu____6692),
                                                      (a,uu____6694)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____6724 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____6724
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____6725 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm
                                             in
                                          (match uu____6725 with
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
                                                 let uu____6742 =
                                                   let uu____6750 =
                                                     FStar_SMTEncoding_Term.mkForall
                                                       t0.FStar_Syntax_Syntax.pos
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____6759 =
                                                     let uu____6761 =
                                                       let uu____6763 =
                                                         FStar_SMTEncoding_Term.hash_of_term
                                                           app_tm
                                                          in
                                                       FStar_Util.digest_of_string
                                                         uu____6763
                                                        in
                                                     Prims.op_Hat
                                                       "partial_app_typing_"
                                                       uu____6761
                                                      in
                                                   (uu____6750,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____6759)
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____6742
                                                  in
                                               let uu____6769 =
                                                 let uu____6772 =
                                                   let uu____6775 =
                                                     let uu____6778 =
                                                       FStar_SMTEncoding_Term.mk_decls
                                                         "" tkey_hash
                                                         [e_typing]
                                                         (FStar_List.append
                                                            decls
                                                            (FStar_List.append
                                                               decls' decls''))
                                                        in
                                                     FStar_List.append
                                                       decls'' uu____6778
                                                      in
                                                   FStar_List.append decls'
                                                     uu____6775
                                                    in
                                                 FStar_List.append decls
                                                   uu____6772
                                                  in
                                               (app_tm, uu____6769))))
                             in
                          let encode_full_app fv =
                            let uu____6798 =
                              FStar_SMTEncoding_Env.lookup_free_var_sym env
                                fv
                               in
                            match uu____6798 with
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
                                   FStar_Syntax_Syntax.pos = uu____6841;
                                   FStar_Syntax_Syntax.vars = uu____6842;_},uu____6843)
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
                                   FStar_Syntax_Syntax.pos = uu____6850;
                                   FStar_Syntax_Syntax.vars = uu____6851;_},uu____6852)
                                ->
                                let uu____6857 =
                                  let uu____6858 =
                                    let uu____6863 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____6863
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____6858
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____6857
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____6893 =
                                  let uu____6894 =
                                    let uu____6899 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____6899
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____6894
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____6893
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____6928,(FStar_Util.Inl t1,uu____6930),uu____6931)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____6978,(FStar_Util.Inr c,uu____6980),uu____6981)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____7028 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____7049 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Env.Weak;
                                     FStar_TypeChecker_Env.HNF;
                                     FStar_TypeChecker_Env.EraseUniverses]
                                     env.FStar_SMTEncoding_Env.tcenv
                                     head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____7049
                                  in
                               let uu____7050 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____7050 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____7066;
                                            FStar_Syntax_Syntax.vars =
                                              uu____7067;_},uu____7068)
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
                                     | uu____7086 ->
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
           let uu____7165 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____7165 with
            | (bs1,body1,opening) ->
                let fallback uu____7188 =
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
                  let uu____7198 =
                    let uu____7199 =
                      FStar_SMTEncoding_Term.mk_fv
                        (f, FStar_SMTEncoding_Term.Term_sort)
                       in
                    FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV
                      uu____7199
                     in
                  let uu____7201 =
                    FStar_All.pipe_right [decl]
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  (uu____7198, uu____7201)  in
                let is_impure rc =
                  let uu____7211 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                      env.FStar_SMTEncoding_Env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____7211 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____7226 =
                          let uu____7239 =
                            FStar_TypeChecker_Env.get_range
                              env.FStar_SMTEncoding_Env.tcenv
                             in
                          FStar_TypeChecker_Util.new_implicit_var
                            "SMTEncoding codomain" uu____7239
                            env.FStar_SMTEncoding_Env.tcenv
                            FStar_Syntax_Util.ktype0
                           in
                        (match uu____7226 with
                         | (t1,uu____7242,uu____7243) -> t1)
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  let uu____7261 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                     in
                  if uu____7261
                  then
                    let uu____7266 = FStar_Syntax_Syntax.mk_Total res_typ  in
                    FStar_Pervasives_Native.Some uu____7266
                  else
                    (let uu____7269 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid
                        in
                     if uu____7269
                     then
                       let uu____7274 = FStar_Syntax_Syntax.mk_GTotal res_typ
                          in
                       FStar_Pervasives_Native.Some uu____7274
                     else FStar_Pervasives_Native.None)
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____7282 =
                         let uu____7288 =
                           let uu____7290 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____7290
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____7288)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____7282);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____7295 =
                       (is_impure rc) &&
                         (let uu____7298 =
                            FStar_TypeChecker_Env.is_reifiable_rc
                              env.FStar_SMTEncoding_Env.tcenv rc
                             in
                          Prims.op_Negation uu____7298)
                        in
                     if uu____7295
                     then fallback ()
                     else
                       (let uu____7307 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____7307 with
                        | (vars,guards,envbody,decls,uu____7332) ->
                            let body2 =
                              let uu____7346 =
                                FStar_TypeChecker_Env.is_reifiable_rc
                                  env.FStar_SMTEncoding_Env.tcenv rc
                                 in
                              if uu____7346
                              then
                                FStar_TypeChecker_Util.reify_body
                                  env.FStar_SMTEncoding_Env.tcenv body1
                              else body1  in
                            let uu____7351 = encode_term body2 envbody  in
                            (match uu____7351 with
                             | (body3,decls') ->
                                 let uu____7362 =
                                   let uu____7371 = codomain_eff rc  in
                                   match uu____7371 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____7390 = encode_term tfun env
                                          in
                                       (match uu____7390 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____7362 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____7424 =
                                          let uu____7435 =
                                            let uu____7436 =
                                              let uu____7441 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____7441, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____7436
                                             in
                                          ([], vars, uu____7435)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t0.FStar_Syntax_Syntax.pos
                                          uu____7424
                                         in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body
                                         in
                                      let uu____7449 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            (cvars, key_body)
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____7465 =
                                              let uu____7468 =
                                                let uu____7479 =
                                                  FStar_SMTEncoding_Term.free_variables
                                                    t1
                                                   in
                                                FStar_List.append uu____7479
                                                  cvars
                                                 in
                                              FStar_Util.remove_dups
                                                FStar_SMTEncoding_Term.fv_eq
                                                uu____7468
                                               in
                                            let uu____7506 =
                                              FStar_SMTEncoding_Util.mkAnd
                                                (key_body, t1)
                                               in
                                            (uu____7465, uu____7506)
                                         in
                                      (match uu____7449 with
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
                                           let uu____7528 =
                                             is_an_eta_expansion env vars
                                               body3
                                              in
                                           (match uu____7528 with
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
                                                  let uu____7544 =
                                                    FStar_Util.digest_of_string
                                                      tkey_hash
                                                     in
                                                  Prims.op_Hat "Tm_abs_"
                                                    uu____7544
                                                   in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None)
                                                   in
                                                let f =
                                                  let uu____7553 =
                                                    let uu____7561 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    (fsym, uu____7561)  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____7553
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
                                                      let uu____7578 =
                                                        let uu____7579 =
                                                          let uu____7587 =
                                                            FStar_SMTEncoding_Term.mkForall
                                                              t0.FStar_Syntax_Syntax.pos
                                                              ([[f]], cvars1,
                                                                f_has_t)
                                                             in
                                                          (uu____7587,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name)
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____7579
                                                         in
                                                      [uu____7578]
                                                   in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.op_Hat
                                                      "interpretation_" fsym
                                                     in
                                                  let uu____7602 =
                                                    let uu____7610 =
                                                      let uu____7611 =
                                                        let uu____7622 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3)
                                                           in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____7622)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        t0.FStar_Syntax_Syntax.pos
                                                        uu____7611
                                                       in
                                                    (uu____7610,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____7602
                                                   in
                                                let f_decls =
                                                  FStar_List.append (fdecl ::
                                                    typing_f) [interp_f]
                                                   in
                                                let uu____7636 =
                                                  let uu____7637 =
                                                    let uu____7640 =
                                                      let uu____7643 =
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
                                                        decls'' uu____7643
                                                       in
                                                    FStar_List.append decls'
                                                      uu____7640
                                                     in
                                                  FStar_List.append decls
                                                    uu____7637
                                                   in
                                                (f, uu____7636))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____7646,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____7647;
                          FStar_Syntax_Syntax.lbunivs = uu____7648;
                          FStar_Syntax_Syntax.lbtyp = uu____7649;
                          FStar_Syntax_Syntax.lbeff = uu____7650;
                          FStar_Syntax_Syntax.lbdef = uu____7651;
                          FStar_Syntax_Syntax.lbattrs = uu____7652;
                          FStar_Syntax_Syntax.lbpos = uu____7653;_}::uu____7654),uu____7655)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____7689;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____7691;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____7693;
                FStar_Syntax_Syntax.lbpos = uu____7694;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____7721 ->
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
              let uu____7793 =
                let uu____7798 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____7798 env  in
              match uu____7793 with
              | (ee1,decls1) ->
                  let uu____7823 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____7823 with
                   | (xs,e21) ->
                       let uu____7848 = FStar_List.hd xs  in
                       (match uu____7848 with
                        | (x1,uu____7866) ->
                            let env' =
                              FStar_SMTEncoding_Env.push_term_var env x1 ee1
                               in
                            let uu____7872 = encode_body e21 env'  in
                            (match uu____7872 with
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
            let uu____7902 =
              let uu____7910 =
                let uu____7911 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____7911  in
              FStar_SMTEncoding_Env.gen_term_var env uu____7910  in
            match uu____7902 with
            | (scrsym,scr',env1) ->
                let uu____7921 = encode_term e env1  in
                (match uu____7921 with
                 | (scr,decls) ->
                     let uu____7932 =
                       let encode_branch b uu____7961 =
                         match uu____7961 with
                         | (else_case,decls1) ->
                             let uu____7980 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____7980 with
                              | (p,w,br) ->
                                  let uu____8006 = encode_pat env1 p  in
                                  (match uu____8006 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____8043  ->
                                                   match uu____8043 with
                                                   | (x,t) ->
                                                       FStar_SMTEncoding_Env.push_term_var
                                                         env2 x t) env1)
                                          in
                                       let uu____8050 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____8072 =
                                               encode_term w1 env2  in
                                             (match uu____8072 with
                                              | (w2,decls2) ->
                                                  let uu____8085 =
                                                    let uu____8086 =
                                                      let uu____8091 =
                                                        let uu____8092 =
                                                          let uu____8097 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____8097)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____8092
                                                         in
                                                      (guard, uu____8091)  in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____8086
                                                     in
                                                  (uu____8085, decls2))
                                          in
                                       (match uu____8050 with
                                        | (guard1,decls2) ->
                                            let uu____8112 =
                                              encode_br br env2  in
                                            (match uu____8112 with
                                             | (br1,decls3) ->
                                                 let uu____8125 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____8125,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____7932 with
                      | (match_tm,decls1) ->
                          let uu____8146 =
                            let uu____8147 =
                              let uu____8158 =
                                let uu____8165 =
                                  let uu____8170 =
                                    FStar_SMTEncoding_Term.mk_fv
                                      (scrsym,
                                        FStar_SMTEncoding_Term.Term_sort)
                                     in
                                  (uu____8170, scr)  in
                                [uu____8165]  in
                              (uu____8158, match_tm)  in
                            FStar_SMTEncoding_Term.mkLet' uu____8147
                              FStar_Range.dummyRange
                             in
                          (uu____8146, decls1)))

and (encode_pat :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.pat -> (FStar_SMTEncoding_Env.env_t * pattern))
  =
  fun env  ->
    fun pat  ->
      (let uu____8193 =
         FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
           FStar_Options.Medium
          in
       if uu____8193
       then
         let uu____8196 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____8196
       else ());
      (let uu____8201 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____8201 with
       | (vars,pat_term) ->
           let uu____8218 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____8260  ->
                     fun v1  ->
                       match uu____8260 with
                       | (env1,vars1) ->
                           let uu____8296 =
                             FStar_SMTEncoding_Env.gen_term_var env1 v1  in
                           (match uu____8296 with
                            | (xx,uu____8315,env2) ->
                                let uu____8319 =
                                  let uu____8326 =
                                    let uu____8331 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xx,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    (v1, uu____8331)  in
                                  uu____8326 :: vars1  in
                                (env2, uu____8319))) (env, []))
              in
           (match uu____8218 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____8386 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____8387 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____8388 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____8396 = encode_const c env1  in
                      (match uu____8396 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____8404::uu____8405 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____8409 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon
                            env1.FStar_SMTEncoding_Env.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____8432 =
                          FStar_TypeChecker_Env.datacons_of_typ
                            env1.FStar_SMTEncoding_Env.tcenv tc_name
                           in
                        match uu____8432 with
                        | (uu____8440,uu____8441::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____8446 ->
                            FStar_SMTEncoding_Env.mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____8482  ->
                                  match uu____8482 with
                                  | (arg,uu____8492) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____8501 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____8501))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____8533) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____8564 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____8589 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____8635  ->
                                  match uu____8635 with
                                  | (arg,uu____8651) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____8660 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____8660))
                         in
                      FStar_All.pipe_right uu____8589 FStar_List.flatten
                   in
                let pat_term1 uu____8691 = encode_term pat_term env1  in
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
      let uu____8701 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____8749  ->
                fun uu____8750  ->
                  match (uu____8749, uu____8750) with
                  | ((tms,decls),(t,uu____8790)) ->
                      let uu____8817 = encode_term t env  in
                      (match uu____8817 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____8701 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let universe_of_binders binders =
        FStar_List.map (fun uu____8895  -> FStar_Syntax_Syntax.U_zero)
          binders
         in
      let quant = FStar_Syntax_Util.smt_lemma_as_forall t universe_of_binders
         in
      let env1 =
        let uu___1241_8904 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___1241_8904.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___1241_8904.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___1241_8904.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___1241_8904.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___1241_8904.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___1241_8904.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___1241_8904.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___1241_8904.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___1241_8904.FStar_SMTEncoding_Env.encoding_quantifier);
          FStar_SMTEncoding_Env.global_cache =
            (uu___1241_8904.FStar_SMTEncoding_Env.global_cache)
        }  in
      encode_formula FStar_Pervasives_Native.None quant env1

and (encode_smt_patterns :
  FStar_Syntax_Syntax.arg Prims.list Prims.list ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term Prims.list Prims.list *
        FStar_SMTEncoding_Term.decls_t))
  =
  fun pats_l  ->
    fun env  ->
      let env1 =
        let uu___1246_8922 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___1246_8922.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___1246_8922.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___1246_8922.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___1246_8922.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___1246_8922.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___1246_8922.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___1246_8922.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___1246_8922.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___1246_8922.FStar_SMTEncoding_Env.encoding_quantifier);
          FStar_SMTEncoding_Env.global_cache =
            (uu___1246_8922.FStar_SMTEncoding_Env.global_cache)
        }  in
      let encode_smt_pattern t =
        let uu____8938 = FStar_Syntax_Util.head_and_args t  in
        match uu____8938 with
        | (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____9001::(x,uu____9003)::(t1,uu____9005)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____9072 = encode_term x env1  in
                 (match uu____9072 with
                  | (x1,decls) ->
                      let uu____9083 = encode_term t1 env1  in
                      (match uu____9083 with
                       | (t2,decls') ->
                           let uu____9094 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                           (uu____9094, (FStar_List.append decls decls'))))
             | uu____9095 -> encode_term t env1)
         in
      FStar_List.fold_right
        (fun pats  ->
           fun uu____9138  ->
             match uu____9138 with
             | (pats_l1,decls) ->
                 let uu____9183 =
                   FStar_List.fold_right
                     (fun uu____9218  ->
                        fun uu____9219  ->
                          match (uu____9218, uu____9219) with
                          | ((p,uu____9261),(pats1,decls1)) ->
                              let uu____9296 = encode_smt_pattern p  in
                              (match uu____9296 with
                               | (t,d) ->
                                   let uu____9311 =
                                     FStar_SMTEncoding_Term.check_pattern_ok
                                       t
                                      in
                                   (match uu____9311 with
                                    | FStar_Pervasives_Native.None  ->
                                        ((t :: pats1),
                                          (FStar_List.append d decls1))
                                    | FStar_Pervasives_Native.Some
                                        illegal_subterm ->
                                        ((let uu____9328 =
                                            let uu____9334 =
                                              let uu____9336 =
                                                FStar_Syntax_Print.term_to_string
                                                  p
                                                 in
                                              let uu____9338 =
                                                FStar_SMTEncoding_Term.print_smt_term
                                                  illegal_subterm
                                                 in
                                              FStar_Util.format2
                                                "Pattern %s contains illegal sub-term (%s); dropping it"
                                                uu____9336 uu____9338
                                               in
                                            (FStar_Errors.Warning_SMTPatternIllFormed,
                                              uu____9334)
                                             in
                                          FStar_Errors.log_issue
                                            p.FStar_Syntax_Syntax.pos
                                            uu____9328);
                                         (pats1,
                                           (FStar_List.append d decls1))))))
                     pats ([], decls)
                    in
                 (match uu____9183 with
                  | (pats1,decls1) -> ((pats1 :: pats_l1), decls1))) pats_l
        ([], [])

and (encode_formula :
  Prims.string FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.typ ->
      FStar_SMTEncoding_Env.env_t ->
        (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun prev_msg  ->
    fun phi  ->
      fun env  ->
        let debug1 phi1 =
          let uu____9402 =
            FStar_All.pipe_left
              (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
              (FStar_Options.Other "SMTEncoding")
             in
          if uu____9402
          then
            let uu____9407 = FStar_Syntax_Print.tag_of_term phi1  in
            let uu____9409 = FStar_Syntax_Print.term_to_string phi1  in
            FStar_Util.print2 "Formula (%s)  %s\n" uu____9407 uu____9409
          else ()  in
        let enc f r l =
          let uu____9451 =
            FStar_Util.fold_map
              (fun decls  ->
                 fun x  ->
                   let uu____9483 =
                     encode_term (FStar_Pervasives_Native.fst x) env  in
                   match uu____9483 with
                   | (t,decls') -> ((FStar_List.append decls decls'), t)) []
              l
             in
          match uu____9451 with
          | (decls,args) ->
              let uu____9514 =
                let uu___1311_9515 = f args  in
                {
                  FStar_SMTEncoding_Term.tm =
                    (uu___1311_9515.FStar_SMTEncoding_Term.tm);
                  FStar_SMTEncoding_Term.freevars =
                    (uu___1311_9515.FStar_SMTEncoding_Term.freevars);
                  FStar_SMTEncoding_Term.rng = r
                }  in
              (uu____9514, decls)
           in
        let const_op f msg r uu____9558 =
          let uu____9574 = f r  in (uu____9574, [])  in
        let un_op f l =
          let uu____9597 = FStar_List.hd l  in
          FStar_All.pipe_left f uu____9597  in
        let bin_op f uu___2_9617 =
          match uu___2_9617 with
          | t1::t2::[] -> f (t1, t2)
          | uu____9628 -> failwith "Impossible"  in
        let enc_prop_c f msg r l =
          let uu____9685 =
            FStar_Util.fold_map
              (fun decls  ->
                 fun uu____9710  ->
                   match uu____9710 with
                   | (t,uu____9726) ->
                       let uu____9731 = encode_formula msg t env  in
                       (match uu____9731 with
                        | (phi1,decls') ->
                            ((FStar_List.append decls decls'), phi1))) [] l
             in
          match uu____9685 with
          | (decls,phis) ->
              let uu____9760 =
                let uu___1343_9761 = f phis  in
                {
                  FStar_SMTEncoding_Term.tm =
                    (uu___1343_9761.FStar_SMTEncoding_Term.tm);
                  FStar_SMTEncoding_Term.freevars =
                    (uu___1343_9761.FStar_SMTEncoding_Term.freevars);
                  FStar_SMTEncoding_Term.rng = r
                }  in
              (uu____9760, decls)
           in
        let eq_op msg r args =
          let rf =
            FStar_List.filter
              (fun uu____9835  ->
                 match uu____9835 with
                 | (a,q) ->
                     (match q with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____9856) -> false
                      | uu____9859 -> true)) args
             in
          if (FStar_List.length rf) <> (Prims.parse_int "2")
          then
            let uu____9878 =
              FStar_Util.format1
                "eq_op: got %s non-implicit arguments instead of 2?"
                (Prims.string_of_int (FStar_List.length rf))
               in
            failwith uu____9878
          else
            (let uu____9895 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
             uu____9895 r rf)
           in
        let eq3_op msg r args =
          let n1 = FStar_List.length args  in
          if n1 = (Prims.parse_int "4")
          then
            let uu____9974 =
              enc
                (fun terms  ->
                   match terms with
                   | t0::t1::v0::v1::[] ->
                       let uu____10006 =
                         let uu____10011 =
                           FStar_SMTEncoding_Util.mkEq (t0, t1)  in
                         let uu____10012 =
                           FStar_SMTEncoding_Util.mkEq (v0, v1)  in
                         (uu____10011, uu____10012)  in
                       FStar_SMTEncoding_Util.mkAnd uu____10006
                   | uu____10013 -> failwith "Impossible")
               in
            uu____9974 r args
          else
            (let uu____10019 =
               FStar_Util.format1
                 "eq3_op: got %s non-implicit arguments instead of 4?"
                 (Prims.string_of_int n1)
                in
             failwith uu____10019)
           in
        let h_equals_op msg r args =
          let n1 = FStar_List.length args  in
          if n1 = (Prims.parse_int "4")
          then
            let uu____10092 =
              enc
                (fun terms  ->
                   match terms with
                   | t0::v0::t1::v1::[] ->
                       let uu____10124 =
                         let uu____10129 =
                           FStar_SMTEncoding_Util.mkEq (t0, t1)  in
                         let uu____10130 =
                           FStar_SMTEncoding_Util.mkEq (v0, v1)  in
                         (uu____10129, uu____10130)  in
                       FStar_SMTEncoding_Util.mkAnd uu____10124
                   | uu____10131 -> failwith "Impossible")
               in
            uu____10092 r args
          else
            (let uu____10137 =
               FStar_Util.format1
                 "eq3_op: got %s non-implicit arguments instead of 4?"
                 (Prims.string_of_int n1)
                in
             failwith uu____10137)
           in
        let mk_imp1 msg r uu___3_10177 =
          match uu___3_10177 with
          | (lhs,uu____10183)::(rhs,uu____10185)::[] ->
              let uu____10226 = encode_formula msg rhs env  in
              (match uu____10226 with
               | (l1,decls1) ->
                   (match l1.FStar_SMTEncoding_Term.tm with
                    | FStar_SMTEncoding_Term.App
                        (FStar_SMTEncoding_Term.TrueOp ,uu____10241) ->
                        (l1, decls1)
                    | uu____10246 ->
                        let uu____10247 = encode_formula msg lhs env  in
                        (match uu____10247 with
                         | (l2,decls2) ->
                             let uu____10258 =
                               FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                             (uu____10258, (FStar_List.append decls1 decls2)))))
          | uu____10259 -> failwith "impossible"  in
        let mk_ite msg r uu___4_10298 =
          match uu___4_10298 with
          | (guard,uu____10304)::(_then,uu____10306)::(_else,uu____10308)::[]
              ->
              let uu____10365 = encode_formula msg guard env  in
              (match uu____10365 with
               | (g,decls1) ->
                   let uu____10376 = encode_formula msg _then env  in
                   (match uu____10376 with
                    | (t,decls2) ->
                        let uu____10387 = encode_formula msg _else env  in
                        (match uu____10387 with
                         | (e,decls3) ->
                             let res =
                               FStar_SMTEncoding_Term.mkITE (g, t, e) r  in
                             (res,
                               (FStar_List.append decls1
                                  (FStar_List.append decls2 decls3))))))
          | uu____10399 -> failwith "impossible"  in
        let unboxInt_l f l =
          let uu____10429 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l
             in
          f uu____10429  in
        let connectives =
          let uu____10465 =
            let uu____10496 =
              enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)  in
            (FStar_Parser_Const.and_lid, uu____10496)  in
          let uu____10552 =
            let uu____10585 =
              let uu____10616 =
                enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)  in
              (FStar_Parser_Const.or_lid, uu____10616)  in
            let uu____10672 =
              let uu____10705 =
                let uu____10738 =
                  let uu____10769 =
                    enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                  (FStar_Parser_Const.iff_lid, uu____10769)  in
                let uu____10825 =
                  let uu____10858 =
                    let uu____10891 =
                      let uu____10922 =
                        enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                      (FStar_Parser_Const.not_lid, uu____10922)  in
                    [uu____10891;
                    (FStar_Parser_Const.eq2_lid, eq_op);
                    (FStar_Parser_Const.c_eq2_lid, eq_op);
                    (FStar_Parser_Const.eq3_lid, eq3_op);
                    (FStar_Parser_Const.c_eq3_lid, h_equals_op);
                    (FStar_Parser_Const.true_lid,
                      (const_op FStar_SMTEncoding_Term.mkTrue));
                    (FStar_Parser_Const.false_lid,
                      (const_op FStar_SMTEncoding_Term.mkFalse))]
                     in
                  (FStar_Parser_Const.ite_lid, mk_ite) :: uu____10858  in
                uu____10738 :: uu____10825  in
              (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____10705  in
            uu____10585 :: uu____10672  in
          uu____10465 :: uu____10552  in
        let rec fallback phi1 =
          match phi1.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_meta
              (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
              let s =
                if msg = "could not prove post-condition"
                then FStar_Pervasives_Native.None
                else
                  (let uu____11619 =
                     let uu____11621 = FStar_Range.string_of_range r  in
                     FStar_Util.format2 "(%s) %s" uu____11621 msg  in
                   FStar_Pervasives_Native.Some uu____11619)
                 in
              let uu____11625 = encode_formula s phi' env  in
              (match uu____11625 with
               | (phi2,decls) ->
                   let uu____11636 =
                     FStar_SMTEncoding_Term.mk
                       (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                      in
                   (uu____11636, decls))
          | FStar_Syntax_Syntax.Tm_meta uu____11638 ->
              let uu____11645 = FStar_Syntax_Util.unmeta phi1  in
              encode_formula prev_msg uu____11645 env
          | FStar_Syntax_Syntax.Tm_match (e,pats) ->
              let uu____11684 =
                encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                  (encode_formula prev_msg)
                 in
              (match uu____11684 with | (t,decls) -> (t, decls))
          | FStar_Syntax_Syntax.Tm_let
              ((false
                ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                   FStar_Syntax_Syntax.lbunivs = uu____11696;
                   FStar_Syntax_Syntax.lbtyp = t1;
                   FStar_Syntax_Syntax.lbeff = uu____11698;
                   FStar_Syntax_Syntax.lbdef = e1;
                   FStar_Syntax_Syntax.lbattrs = uu____11700;
                   FStar_Syntax_Syntax.lbpos = uu____11701;_}::[]),e2)
              ->
              let uu____11728 =
                encode_let x t1 e1 e2 env (encode_formula prev_msg)  in
              (match uu____11728 with | (t,decls) -> (t, decls))
          | FStar_Syntax_Syntax.Tm_app (head1,args) ->
              let head2 = FStar_Syntax_Util.un_uinst head1  in
              (match ((head2.FStar_Syntax_Syntax.n), args) with
               | (FStar_Syntax_Syntax.Tm_fvar
                  fv,uu____11781::(x,uu____11783)::(t,uu____11785)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.has_type_lid
                   ->
                   let uu____11852 = encode_term x env  in
                   (match uu____11852 with
                    | (x1,decls) ->
                        let uu____11863 = encode_term t env  in
                        (match uu____11863 with
                         | (t1,decls') ->
                             let uu____11874 =
                               FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                             (uu____11874, (FStar_List.append decls decls'))))
               | (FStar_Syntax_Syntax.Tm_fvar
                  fv,(r,uu____11877)::(msg,uu____11879)::(phi2,uu____11881)::[])
                   when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.labeled_lid
                   ->
                   let uu____11948 =
                     let uu____11953 =
                       let uu____11954 = FStar_Syntax_Subst.compress r  in
                       uu____11954.FStar_Syntax_Syntax.n  in
                     let uu____11957 =
                       let uu____11958 = FStar_Syntax_Subst.compress msg  in
                       uu____11958.FStar_Syntax_Syntax.n  in
                     (uu____11953, uu____11957)  in
                   (match uu____11948 with
                    | (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_range
                       r1),FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_string (s,uu____11967))) ->
                        let s1 =
                          match prev_msg with
                          | FStar_Pervasives_Native.Some msg1 ->
                              Prims.op_Hat msg1 (Prims.op_Hat ": " s)
                          | FStar_Pervasives_Native.None  -> s  in
                        let phi3 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_meta
                               (phi2,
                                 (FStar_Syntax_Syntax.Meta_labeled
                                    (s1, r1, false))))
                            FStar_Pervasives_Native.None r1
                           in
                        fallback phi3
                    | uu____11986 -> fallback phi2)
               | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____11993)::[]) when
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.squash_lid)
                     ||
                     (FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.auto_squash_lid)
                   -> encode_formula prev_msg t env
               | uu____12028 when head_redex env head2 ->
                   let uu____12043 = whnf env phi1  in
                   encode_formula prev_msg uu____12043 env
               | uu____12044 ->
                   let uu____12059 = encode_term phi1 env  in
                   (match uu____12059 with
                    | (tt,decls) ->
                        let tt1 =
                          let uu____12071 =
                            let uu____12073 =
                              FStar_Range.use_range
                                tt.FStar_SMTEncoding_Term.rng
                               in
                            let uu____12074 =
                              FStar_Range.use_range
                                phi1.FStar_Syntax_Syntax.pos
                               in
                            FStar_Range.rng_included uu____12073 uu____12074
                             in
                          if uu____12071
                          then tt
                          else
                            (let uu___1541_12078 = tt  in
                             {
                               FStar_SMTEncoding_Term.tm =
                                 (uu___1541_12078.FStar_SMTEncoding_Term.tm);
                               FStar_SMTEncoding_Term.freevars =
                                 (uu___1541_12078.FStar_SMTEncoding_Term.freevars);
                               FStar_SMTEncoding_Term.rng =
                                 (phi1.FStar_Syntax_Syntax.pos)
                             })
                           in
                        let uu____12079 = FStar_SMTEncoding_Term.mk_Valid tt1
                           in
                        (uu____12079, decls)))
          | uu____12080 ->
              let uu____12081 = encode_term phi1 env  in
              (match uu____12081 with
               | (tt,decls) ->
                   let tt1 =
                     let uu____12093 =
                       let uu____12095 =
                         FStar_Range.use_range tt.FStar_SMTEncoding_Term.rng
                          in
                       let uu____12096 =
                         FStar_Range.use_range phi1.FStar_Syntax_Syntax.pos
                          in
                       FStar_Range.rng_included uu____12095 uu____12096  in
                     if uu____12093
                     then tt
                     else
                       (let uu___1549_12100 = tt  in
                        {
                          FStar_SMTEncoding_Term.tm =
                            (uu___1549_12100.FStar_SMTEncoding_Term.tm);
                          FStar_SMTEncoding_Term.freevars =
                            (uu___1549_12100.FStar_SMTEncoding_Term.freevars);
                          FStar_SMTEncoding_Term.rng =
                            (phi1.FStar_Syntax_Syntax.pos)
                        })
                      in
                   let uu____12101 = FStar_SMTEncoding_Term.mk_Valid tt1  in
                   (uu____12101, decls))
           in
        let encode_q_body env1 bs ps body =
          let uu____12145 =
            encode_binders FStar_Pervasives_Native.None bs env1  in
          match uu____12145 with
          | (vars,guards,env2,decls,uu____12184) ->
              let uu____12197 = encode_smt_patterns ps env2  in
              (match uu____12197 with
               | (pats,decls') ->
                   let uu____12234 =
                     encode_formula FStar_Pervasives_Native.None body env2
                      in
                   (match uu____12234 with
                    | (body1,decls'') ->
                        let guards1 =
                          match pats with
                          | ({
                               FStar_SMTEncoding_Term.tm =
                                 FStar_SMTEncoding_Term.App
                                 (FStar_SMTEncoding_Term.Var gf,p::[]);
                               FStar_SMTEncoding_Term.freevars = uu____12267;
                               FStar_SMTEncoding_Term.rng = uu____12268;_}::[])::[]
                              when
                              let uu____12288 =
                                FStar_Ident.text_of_lid
                                  FStar_Parser_Const.guard_free
                                 in
                              uu____12288 = gf -> []
                          | uu____12291 -> guards  in
                        let uu____12296 =
                          FStar_SMTEncoding_Util.mk_and_l guards1  in
                        (vars, pats, uu____12296, body1,
                          (FStar_List.append decls
                             (FStar_List.append decls' decls'')))))
           in
        debug1 phi;
        (let phi1 = FStar_Syntax_Util.unascribe phi  in
         let uu____12307 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
         match uu____12307 with
         | FStar_Pervasives_Native.None  -> fallback phi1
         | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
             (op,arms)) ->
             let uu____12316 =
               FStar_All.pipe_right connectives
                 (FStar_List.tryFind
                    (fun uu____12446  ->
                       match uu____12446 with
                       | (l,uu____12476) -> FStar_Ident.lid_equals op l))
                in
             (match uu____12316 with
              | FStar_Pervasives_Native.None  -> fallback phi1
              | FStar_Pervasives_Native.Some (uu____12563,f) ->
                  f prev_msg phi1.FStar_Syntax_Syntax.pos arms)
         | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
             (vars,pats,body)) ->
             (FStar_All.pipe_right pats
                (FStar_List.iter (check_pattern_vars env vars));
              (let uu____12673 = encode_q_body env vars pats body  in
               match uu____12673 with
               | (vars1,pats1,guard,body1,decls) ->
                   let tm =
                     let uu____12718 =
                       let uu____12729 =
                         FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                       (pats1, vars1, uu____12729)  in
                     FStar_SMTEncoding_Term.mkForall
                       phi1.FStar_Syntax_Syntax.pos uu____12718
                      in
                   (tm, decls)))
         | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
             (vars,pats,body)) ->
             (FStar_All.pipe_right pats
                (FStar_List.iter (check_pattern_vars env vars));
              (let uu____12760 = encode_q_body env vars pats body  in
               match uu____12760 with
               | (vars1,pats1,guard,body1,decls) ->
                   let uu____12804 =
                     let uu____12805 =
                       let uu____12816 =
                         FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                       (pats1, vars1, uu____12816)  in
                     FStar_SMTEncoding_Term.mkExists
                       phi1.FStar_Syntax_Syntax.pos uu____12805
                      in
                   (uu____12804, decls))))
