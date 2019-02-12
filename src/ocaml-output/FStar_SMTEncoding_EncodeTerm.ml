open Prims
let mkForall_fuel' :
  'Auu____9 .
    FStar_Range.range ->
      'Auu____9 ->
        (FStar_SMTEncoding_Term.pat Prims.list Prims.list *
          FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term) ->
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
              (let uu____71 =
                 FStar_SMTEncoding_Env.fresh_fvar "f"
                   FStar_SMTEncoding_Term.Fuel_sort
                  in
               match uu____71 with
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
                             | uu____111 -> p))
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
                               let uu____132 = add_fuel1 guards  in
                               FStar_SMTEncoding_Util.mk_and_l uu____132
                           | uu____135 ->
                               let uu____136 = add_fuel1 [guard]  in
                               FStar_All.pipe_right uu____136 FStar_List.hd
                            in
                         FStar_SMTEncoding_Util.mkImp (guard1, body')
                     | uu____141 -> body  in
                   let vars1 =
                     let uu____153 =
                       FStar_SMTEncoding_Term.mk_fv
                         (fsym, FStar_SMTEncoding_Term.Fuel_sort)
                        in
                     uu____153 :: vars  in
                   FStar_SMTEncoding_Term.mkForall r (pats1, vars1, body1))
  
let (mkForall_fuel :
  FStar_Range.range ->
    (FStar_SMTEncoding_Term.pat Prims.list Prims.list *
      FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term) ->
      FStar_SMTEncoding_Term.term)
  = fun r  -> mkForall_fuel' r (Prims.parse_int "1") 
let (head_normal :
  FStar_SMTEncoding_Env.env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow uu____210 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____226 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____234 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____236 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____250 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____270 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____273 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____273 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____292;
             FStar_Syntax_Syntax.vars = uu____293;_},uu____294)
          ->
          let uu____319 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____319 FStar_Option.isNone
      | uu____337 -> false
  
let (head_redex :
  FStar_SMTEncoding_Env.env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____351 =
        let uu____352 = FStar_Syntax_Util.un_uinst t  in
        uu____352.FStar_Syntax_Syntax.n  in
      match uu____351 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____356,uu____357,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___358_382  ->
                  match uu___358_382 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____385 -> false) rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____388 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____388 FStar_Option.isSome
      | uu____406 -> false
  
let (whnf :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____419 = head_normal env t  in
      if uu____419
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
    let uu____441 =
      let uu____442 = FStar_Syntax_Syntax.null_binder t  in [uu____442]  in
    let uu____461 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    FStar_Syntax_Util.abs uu____441 uu____461 FStar_Pervasives_Native.None
  
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
                let uu____483 = FStar_SMTEncoding_Term.fv_sort var  in
                match uu____483 with
                | FStar_SMTEncoding_Term.Fuel_sort  ->
                    let uu____484 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____484
                | s ->
                    let uu____487 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____487) e)
  
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
          let uu____543 =
            let uu____549 =
              let uu____551 = FStar_Util.string_of_int arity  in
              let uu____553 = FStar_Util.string_of_int n_args  in
              FStar_Util.format3
                "Head symbol %s expects at least %s arguments; got only %s"
                head1 uu____551 uu____553
               in
            (FStar_Errors.Fatal_SMTEncodingArityMismatch, uu____549)  in
          FStar_Errors.raise_error uu____543 rng
  
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
                  (let uu____612 = FStar_Util.first_N arity args  in
                   match uu____612 with
                   | (args1,rest) ->
                       let head3 =
                         FStar_SMTEncoding_Util.mkApp' (head2, args1)  in
                       mk_Apply_args head3 rest)
                else
                  (let uu____636 = FStar_SMTEncoding_Term.op_to_string head2
                      in
                   raise_arity_mismatch uu____636 arity n_args rng)
  
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
          let uu____663 = FStar_SMTEncoding_Env.force_thunk fvb  in
          mk_Apply_args uu____663 args
        else
          maybe_curry_app rng
            (FStar_Util.Inl
               (FStar_SMTEncoding_Term.Var (fvb.FStar_SMTEncoding_Env.smt_id)))
            fvb.FStar_SMTEncoding_Env.smt_arity args
  
let (is_app : FStar_SMTEncoding_Term.op -> Prims.bool) =
  fun uu___359_672  ->
    match uu___359_672 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____678 -> false
  
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
                       FStar_SMTEncoding_Term.freevars = uu____726;
                       FStar_SMTEncoding_Term.rng = uu____727;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____758) ->
              let uu____768 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____785 -> false) args (FStar_List.rev xs))
                 in
              if uu____768
              then FStar_SMTEncoding_Env.tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____792,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t  in
              let uu____796 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____804 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars
                           in
                        Prims.op_Negation uu____804))
                 in
              if uu____796
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____811 -> FStar_Pervasives_Native.None  in
        check_partial_applications body (FStar_List.rev vars)
  
let check_pattern_vars :
  'Auu____829 'Auu____830 .
    FStar_SMTEncoding_Env.env_t ->
      (FStar_Syntax_Syntax.bv * 'Auu____829) Prims.list ->
        (FStar_Syntax_Syntax.term * 'Auu____830) Prims.list -> unit
  =
  fun env  ->
    fun vars  ->
      fun pats  ->
        let pats1 =
          FStar_All.pipe_right pats
            (FStar_List.map
               (fun uu____888  ->
                  match uu____888 with
                  | (x,uu____894) ->
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
              let uu____902 = FStar_Syntax_Free.names hd1  in
              FStar_List.fold_left
                (fun out  ->
                   fun x  ->
                     let uu____914 = FStar_Syntax_Free.names x  in
                     FStar_Util.set_union out uu____914) uu____902 tl1
               in
            let uu____917 =
              FStar_All.pipe_right vars
                (FStar_Util.find_opt
                   (fun uu____944  ->
                      match uu____944 with
                      | (b,uu____951) ->
                          let uu____952 = FStar_Util.set_mem b pat_vars  in
                          Prims.op_Negation uu____952))
               in
            (match uu____917 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some (x,uu____959) ->
                 let pos =
                   FStar_List.fold_left
                     (fun out  ->
                        fun t  ->
                          FStar_Range.union_ranges out
                            t.FStar_Syntax_Syntax.pos)
                     hd1.FStar_Syntax_Syntax.pos tl1
                    in
                 let uu____973 =
                   let uu____979 =
                     let uu____981 = FStar_Syntax_Print.bv_to_string x  in
                     FStar_Util.format1
                       "SMT pattern misses at least one bound variable: %s"
                       uu____981
                      in
                   (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                     uu____979)
                    in
                 FStar_Errors.log_issue pos uu____973)
  
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
        | FStar_Syntax_Syntax.Tm_arrow uu____1267 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____1282 ->
            let uu____1289 = FStar_Syntax_Util.unrefine t1  in
            aux true uu____1289
        | uu____1291 ->
            if norm1
            then let uu____1293 = whnf env t1  in aux false uu____1293
            else
              (let uu____1297 =
                 let uu____1299 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let uu____1301 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____1299 uu____1301
                  in
               failwith uu____1297)
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
    | FStar_Syntax_Syntax.Tm_refine (bv,uu____1343) ->
        let uu____1348 =
          curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort  in
        (match uu____1348 with
         | (args,res) ->
             (match args with
              | [] ->
                  let uu____1369 = FStar_Syntax_Syntax.mk_Total k1  in
                  ([], uu____1369)
              | uu____1376 -> (args, res)))
    | uu____1377 ->
        let uu____1378 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____1378)
  
let is_arithmetic_primitive :
  'Auu____1392 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____1392 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1415::uu____1416::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1420::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____1423 -> false
  
let (isInteger : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____1454 -> false
  
let (getInteger : FStar_Syntax_Syntax.term' -> Prims.int) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____1477 -> failwith "Expected an Integer term"
  
let is_BitVector_primitive :
  'Auu____1487 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____1487)
        Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____1529)::uu____1530::uu____1531::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____1582)::uu____1583::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____1620 -> false
  
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
          let uu____1938 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue  in
          (uu____1938, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____1940 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse  in
          (uu____1940, [])
      | FStar_Const.Const_char c1 ->
          let uu____1943 =
            let uu____1944 =
              let uu____1952 =
                let uu____1955 =
                  let uu____1956 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1)
                     in
                  FStar_SMTEncoding_Term.boxInt uu____1956  in
                [uu____1955]  in
              ("FStar.Char.__char_of_int", uu____1952)  in
            FStar_SMTEncoding_Util.mkApp uu____1944  in
          (uu____1943, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____1974 =
            let uu____1975 = FStar_SMTEncoding_Util.mkInteger i  in
            FStar_SMTEncoding_Term.boxInt uu____1975  in
          (uu____1974, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.FStar_SMTEncoding_Env.tcenv).FStar_TypeChecker_Env.dsenv
              repr sw FStar_Range.dummyRange
             in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____1996) ->
          let uu____1999 =
            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.string_const s
             in
          (uu____1999, [])
      | FStar_Const.Const_range uu____2000 ->
          let uu____2001 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          (uu____2001, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | FStar_Const.Const_real r ->
          let uu____2004 =
            let uu____2005 = FStar_SMTEncoding_Util.mkReal r  in
            FStar_SMTEncoding_Term.boxReal uu____2005  in
          (uu____2004, [])
      | c1 ->
          let uu____2007 =
            let uu____2009 = FStar_Syntax_Print.const_to_string c1  in
            FStar_Util.format1 "Unhandled constant: %s" uu____2009  in
          failwith uu____2007

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
        (let uu____2038 =
           FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
             FStar_Options.Medium
            in
         if uu____2038
         then
           let uu____2041 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____2041
         else ());
        (let uu____2047 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2129  ->
                   fun b  ->
                     match uu____2129 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2194 =
                           let x = FStar_Pervasives_Native.fst b  in
                           let uu____2210 =
                             FStar_SMTEncoding_Env.gen_term_var env1 x  in
                           match uu____2210 with
                           | (xxsym,xx,env') ->
                               let uu____2235 =
                                 let uu____2240 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____2240 env1 xx
                                  in
                               (match uu____2235 with
                                | (guard_x_t,decls') ->
                                    let uu____2255 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xxsym,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    (uu____2255, guard_x_t, env', decls', x))
                            in
                         (match uu____2194 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____2047 with
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
          let uu____2355 = encode_term t env  in
          match uu____2355 with
          | (t1,decls) ->
              let uu____2366 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____2366, decls)

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
          let uu____2377 = encode_term t env  in
          match uu____2377 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____2392 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____2392, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____2394 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____2394, decls))

and (encode_arith_term :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____2400 = encode_args args_e env  in
        match uu____2400 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____2419 -> failwith "Impossible"  in
            let unary unbox arg_tms1 =
              let uu____2441 = FStar_List.hd arg_tms1  in unbox uu____2441
               in
            let binary unbox arg_tms1 =
              let uu____2466 =
                let uu____2467 = FStar_List.hd arg_tms1  in unbox uu____2467
                 in
              let uu____2468 =
                let uu____2469 =
                  let uu____2470 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____2470  in
                unbox uu____2469  in
              (uu____2466, uu____2468)  in
            let mk_default uu____2478 =
              let uu____2479 =
                FStar_SMTEncoding_Env.lookup_free_var_sym env
                  head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____2479 with
              | (fname,fuel_args,arity) ->
                  let args = FStar_List.append fuel_args arg_tms  in
                  maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity
                    args
               in
            let mk_l box op mk_args ts =
              let uu____2568 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____2568
              then
                let uu____2571 =
                  let uu____2572 = mk_args ts  in op uu____2572  in
                FStar_All.pipe_right uu____2571 box
              else mk_default ()  in
            let mk_nl box unbox nm op ts =
              let uu____2630 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____2630
              then
                let uu____2633 = binary unbox ts  in
                match uu____2633 with
                | (t1,t2) ->
                    let uu____2640 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____2640 box
              else
                (let uu____2646 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____2646
                 then
                   let uu____2649 =
                     let uu____2650 = binary unbox ts  in op uu____2650  in
                   FStar_All.pipe_right uu____2649 box
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
                (div1 FStar_SMTEncoding_Term.boxReal
                   FStar_SMTEncoding_Term.unboxReal "_rdiv"));
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
            let uu____3085 =
              let uu____3095 =
                FStar_List.tryFind
                  (fun uu____3119  ->
                     match uu____3119 with
                     | (l,uu____3130) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____3095 FStar_Util.must  in
            (match uu____3085 with
             | (uu____3174,op) ->
                 let uu____3186 = op arg_tms  in (uu____3186, decls))

and (encode_BitVector_term :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.arg Prims.list ->
        (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl
          Prims.list))
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____3194 = FStar_List.hd args_e  in
        match uu____3194 with
        | (tm_sz,uu____3202) ->
            let uu____3211 = uu____3194  in
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let uu____3220 =
                FStar_Util.smap_try_find env.FStar_SMTEncoding_Env.cache
                  sz_key
                 in
              match uu____3220 with
              | FStar_Pervasives_Native.Some cache_entry ->
                  FStar_SMTEncoding_Env.use_cache_entry cache_entry
              | FStar_Pervasives_Native.None  ->
                  let t_decls1 = FStar_SMTEncoding_Term.mkBvConstructor sz
                     in
                  ((let uu____3228 =
                      FStar_SMTEncoding_Env.mk_cache_entry env "" [] t_decls1
                       in
                    FStar_Util.smap_add env.FStar_SMTEncoding_Env.cache
                      sz_key uu____3228);
                   t_decls1)
               in
            let uu____3230 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____3256::(sz_arg,uu____3258)::uu____3259::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____3326 =
                    let uu____3327 = FStar_List.tail args_e  in
                    FStar_List.tail uu____3327  in
                  let uu____3330 =
                    let uu____3334 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____3334  in
                  (uu____3326, uu____3330)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____3341::(sz_arg,uu____3343)::uu____3344::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____3411 =
                    let uu____3413 = FStar_Syntax_Print.term_to_string sz_arg
                       in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____3413
                     in
                  failwith uu____3411
              | uu____3423 ->
                  let uu____3438 = FStar_List.tail args_e  in
                  (uu____3438, FStar_Pervasives_Native.None)
               in
            (match uu____3230 with
             | (arg_tms,ext_sz) ->
                 let uu____3457 = encode_args arg_tms env  in
                 (match uu____3457 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____3478 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____3490 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____3490  in
                      let unary_arith arg_tms2 =
                        let uu____3501 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____3501  in
                      let binary arg_tms2 =
                        let uu____3516 =
                          let uu____3517 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3517
                           in
                        let uu____3518 =
                          let uu____3519 =
                            let uu____3520 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____3520  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3519
                           in
                        (uu____3516, uu____3518)  in
                      let binary_arith arg_tms2 =
                        let uu____3537 =
                          let uu____3538 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3538
                           in
                        let uu____3539 =
                          let uu____3540 =
                            let uu____3541 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____3541  in
                          FStar_SMTEncoding_Term.unboxInt uu____3540  in
                        (uu____3537, uu____3539)  in
                      let mk_bv op mk_args resBox ts =
                        let uu____3599 =
                          let uu____3600 = mk_args ts  in op uu____3600  in
                        FStar_All.pipe_right uu____3599 resBox  in
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
                        let uu____3732 =
                          let uu____3737 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____3737  in
                        let uu____3746 =
                          let uu____3751 =
                            let uu____3753 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____3753  in
                          FStar_SMTEncoding_Term.boxBitVec uu____3751  in
                        mk_bv uu____3732 unary uu____3746 arg_tms2  in
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
                      let uu____3993 =
                        let uu____4003 =
                          FStar_List.tryFind
                            (fun uu____4027  ->
                               match uu____4027 with
                               | (l,uu____4038) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____4003 FStar_Util.must  in
                      (match uu____3993 with
                       | (uu____4084,op) ->
                           let uu____4096 = op arg_tms1  in
                           (uu____4096, (FStar_List.append sz_decls decls)))))

and (encode_deeply_embedded_quantifier :
  FStar_Syntax_Syntax.term ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let env1 =
        let uu___363_4106 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___363_4106.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___363_4106.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___363_4106.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___363_4106.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___363_4106.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.cache =
            (uu___363_4106.FStar_SMTEncoding_Env.cache);
          FStar_SMTEncoding_Env.nolabels =
            (uu___363_4106.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name =
            (uu___363_4106.FStar_SMTEncoding_Env.use_zfuel_name);
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___363_4106.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___363_4106.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier = true
        }  in
      let uu____4108 = encode_term t env1  in
      match uu____4108 with
      | (tm,decls) ->
          let vars = FStar_SMTEncoding_Term.free_variables tm  in
          let valid_tm = FStar_SMTEncoding_Term.mk_Valid tm  in
          let key =
            FStar_SMTEncoding_Term.mkForall t.FStar_Syntax_Syntax.pos
              ([], vars, valid_tm)
             in
          let tkey_hash = FStar_SMTEncoding_Term.hash_of_term key  in
          let uu____4130 =
            FStar_Util.smap_try_find env1.FStar_SMTEncoding_Env.cache
              tkey_hash
             in
          (match uu____4130 with
           | FStar_Pervasives_Native.Some cache_entry ->
               (tm,
                 (FStar_List.append decls
                    (FStar_SMTEncoding_Env.use_cache_entry cache_entry)))
           | uu____4138 ->
               (match tm.FStar_SMTEncoding_Term.tm with
                | FStar_SMTEncoding_Term.App
                    (uu____4145,{
                                  FStar_SMTEncoding_Term.tm =
                                    FStar_SMTEncoding_Term.FreeV uu____4146;
                                  FStar_SMTEncoding_Term.freevars =
                                    uu____4147;
                                  FStar_SMTEncoding_Term.rng = uu____4148;_}::
                     {
                       FStar_SMTEncoding_Term.tm =
                         FStar_SMTEncoding_Term.FreeV uu____4149;
                       FStar_SMTEncoding_Term.freevars = uu____4150;
                       FStar_SMTEncoding_Term.rng = uu____4151;_}::[])
                    ->
                    (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                       (FStar_Errors.Warning_QuantifierWithoutPattern,
                         "Not encoding deeply embedded, unguarded quantifier to SMT");
                     (tm, decls))
                | uu____4197 ->
                    let uu____4198 = encode_formula t env1  in
                    (match uu____4198 with
                     | (phi,decls') ->
                         let interp =
                           match vars with
                           | [] ->
                               let uu____4218 =
                                 let uu____4223 =
                                   FStar_SMTEncoding_Term.mk_Valid tm  in
                                 (uu____4223, phi)  in
                               FStar_SMTEncoding_Util.mkIff uu____4218
                           | uu____4224 ->
                               let uu____4225 =
                                 let uu____4236 =
                                   let uu____4237 =
                                     let uu____4242 =
                                       FStar_SMTEncoding_Term.mk_Valid tm  in
                                     (uu____4242, phi)  in
                                   FStar_SMTEncoding_Util.mkIff uu____4237
                                    in
                                 ([[valid_tm]], vars, uu____4236)  in
                               FStar_SMTEncoding_Term.mkForall
                                 t.FStar_Syntax_Syntax.pos uu____4225
                            in
                         let ax =
                           let uu____4252 =
                             let uu____4260 =
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 "l_quant_interp"
                                in
                             (interp,
                               (FStar_Pervasives_Native.Some
                                  "Interpretation of deeply embedded quantifier"),
                               uu____4260)
                              in
                           FStar_SMTEncoding_Util.mkAssume uu____4252  in
                         let decls1 =
                           FStar_List.append decls
                             (FStar_List.append decls' [ax])
                            in
                         ((let uu____4270 =
                             FStar_SMTEncoding_Env.mk_cache_entry env1 "" []
                               decls1
                              in
                           FStar_Util.smap_add
                             env1.FStar_SMTEncoding_Env.cache tkey_hash
                             uu____4270);
                          (tm, decls1)))))

and (encode_term :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____4280 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____4280
       then
         let uu____4285 = FStar_Syntax_Print.tag_of_term t  in
         let uu____4287 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____4289 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____4285 uu____4287
           uu____4289
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____4298 ->
           let uu____4321 =
             let uu____4323 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____4326 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____4328 = FStar_Syntax_Print.term_to_string t0  in
             let uu____4330 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____4323
               uu____4326 uu____4328 uu____4330
              in
           failwith uu____4321
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____4337 =
             let uu____4339 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____4342 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____4344 = FStar_Syntax_Print.term_to_string t0  in
             let uu____4346 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____4339
               uu____4342 uu____4344 uu____4346
              in
           failwith uu____4337
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let e = FStar_Syntax_Util.unfold_lazy i  in
           ((let uu____4356 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____4356
             then
               let uu____4361 = FStar_Syntax_Print.term_to_string t0  in
               let uu____4363 = FStar_Syntax_Print.term_to_string e  in
               FStar_Util.print2 ">> Unfolded (%s) ~> (%s)\n" uu____4361
                 uu____4363
             else ());
            encode_term e env)
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____4369 =
             let uu____4371 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____4371
              in
           failwith uu____4369
       | FStar_Syntax_Syntax.Tm_ascribed (t1,(k,uu____4380),uu____4381) ->
           let uu____4430 =
             match k with
             | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
             | uu____4440 -> false  in
           if uu____4430
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t1 env
       | FStar_Syntax_Syntax.Tm_quoted (qt,uu____4458) ->
           let tv =
             let uu____4464 =
               let uu____4471 = FStar_Reflection_Basic.inspect_ln qt  in
               FStar_Syntax_Embeddings.embed
                 FStar_Reflection_Embeddings.e_term_view uu____4471
                in
             uu____4464 t.FStar_Syntax_Syntax.pos
               FStar_Pervasives_Native.None
               FStar_Syntax_Embeddings.id_norm_cb
              in
           ((let uu____4498 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____4498
             then
               let uu____4503 = FStar_Syntax_Print.term_to_string t0  in
               let uu____4505 = FStar_Syntax_Print.term_to_string tv  in
               FStar_Util.print2 ">> Inspected (%s) ~> (%s)\n" uu____4503
                 uu____4505
             else ());
            (let t1 =
               let uu____4513 =
                 let uu____4524 = FStar_Syntax_Syntax.as_arg tv  in
                 [uu____4524]  in
               FStar_Syntax_Util.mk_app
                 (FStar_Reflection_Data.refl_constant_term
                    FStar_Reflection_Data.fstar_refl_pack_ln) uu____4513
                in
             encode_term t1 env))
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_pattern uu____4550) ->
           encode_term t1
             (let uu___364_4568 = env  in
              {
                FStar_SMTEncoding_Env.bvar_bindings =
                  (uu___364_4568.FStar_SMTEncoding_Env.bvar_bindings);
                FStar_SMTEncoding_Env.fvar_bindings =
                  (uu___364_4568.FStar_SMTEncoding_Env.fvar_bindings);
                FStar_SMTEncoding_Env.depth =
                  (uu___364_4568.FStar_SMTEncoding_Env.depth);
                FStar_SMTEncoding_Env.tcenv =
                  (uu___364_4568.FStar_SMTEncoding_Env.tcenv);
                FStar_SMTEncoding_Env.warn =
                  (uu___364_4568.FStar_SMTEncoding_Env.warn);
                FStar_SMTEncoding_Env.cache =
                  (uu___364_4568.FStar_SMTEncoding_Env.cache);
                FStar_SMTEncoding_Env.nolabels =
                  (uu___364_4568.FStar_SMTEncoding_Env.nolabels);
                FStar_SMTEncoding_Env.use_zfuel_name =
                  (uu___364_4568.FStar_SMTEncoding_Env.use_zfuel_name);
                FStar_SMTEncoding_Env.encode_non_total_function_typ =
                  (uu___364_4568.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                FStar_SMTEncoding_Env.current_module_name =
                  (uu___364_4568.FStar_SMTEncoding_Env.current_module_name);
                FStar_SMTEncoding_Env.encoding_quantifier = false
              })
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____4571) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = FStar_SMTEncoding_Env.lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____4579 = head_redex env t  in
           if uu____4579
           then let uu____4586 = whnf env t  in encode_term uu____4586 env
           else
             (let fvb =
                FStar_SMTEncoding_Env.lookup_free_var_name env
                  v1.FStar_Syntax_Syntax.fv_name
                 in
              let tok =
                FStar_SMTEncoding_Env.lookup_free_var env
                  v1.FStar_Syntax_Syntax.fv_name
                 in
              let aux_decls =
                if
                  fvb.FStar_SMTEncoding_Env.smt_arity > (Prims.parse_int "0")
                then
                  match tok.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.FreeV uu____4594 ->
                      let uu____4603 =
                        let uu____4604 =
                          let uu____4612 =
                            FStar_SMTEncoding_Term.kick_partial_app tok  in
                          let uu____4613 =
                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                              "@kick_partial_app"
                             in
                          (uu____4612,
                            (FStar_Pervasives_Native.Some "kick_partial_app"),
                            uu____4613)
                           in
                        FStar_SMTEncoding_Util.mkAssume uu____4604  in
                      [uu____4603]
                  | FStar_SMTEncoding_Term.App (uu____4619,[]) ->
                      let uu____4622 =
                        let uu____4623 =
                          let uu____4631 =
                            FStar_SMTEncoding_Term.kick_partial_app tok  in
                          let uu____4632 =
                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                              "@kick_partial_app"
                             in
                          (uu____4631,
                            (FStar_Pervasives_Native.Some "kick_partial_app"),
                            uu____4632)
                           in
                        FStar_SMTEncoding_Util.mkAssume uu____4623  in
                      [uu____4622]
                  | uu____4638 -> []
                else []  in
              (tok, aux_decls))
       | FStar_Syntax_Syntax.Tm_type uu____4641 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4643) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.FStar_SMTEncoding_Env.current_module_name
              in
           let uu____4673 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____4673 with
            | (binders1,res) ->
                let uu____4684 =
                  (env.FStar_SMTEncoding_Env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____4684
                then
                  let uu____4691 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____4691 with
                   | (vars,guards,env',decls,uu____4716) ->
                       let fsym =
                         let uu____4730 =
                           let uu____4736 =
                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                               "f"
                              in
                           (uu____4736, FStar_SMTEncoding_Term.Term_sort)  in
                         FStar_SMTEncoding_Term.mk_fv uu____4730  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____4742 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___365_4751 =
                              env.FStar_SMTEncoding_Env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___365_4751.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___365_4751.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___365_4751.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___365_4751.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___365_4751.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___365_4751.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___365_4751.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___365_4751.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___365_4751.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___365_4751.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___365_4751.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___365_4751.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___365_4751.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___365_4751.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___365_4751.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___365_4751.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___365_4751.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___365_4751.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___365_4751.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___365_4751.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___365_4751.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___365_4751.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___365_4751.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___365_4751.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___365_4751.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___365_4751.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___365_4751.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___365_4751.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___365_4751.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___365_4751.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___365_4751.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___365_4751.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___365_4751.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___365_4751.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___365_4751.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___365_4751.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___365_4751.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___365_4751.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___365_4751.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___365_4751.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___365_4751.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___365_4751.FStar_TypeChecker_Env.nbe)
                            }) res
                          in
                       (match uu____4742 with
                        | (pre_opt,res_t) ->
                            let uu____4763 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____4763 with
                             | (res_pred,decls') ->
                                 let uu____4774 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____4787 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____4787, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____4791 =
                                         encode_formula pre env'  in
                                       (match uu____4791 with
                                        | (guard,decls0) ->
                                            let uu____4804 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____4804, decls0))
                                    in
                                 (match uu____4774 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____4818 =
                                          let uu____4829 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____4829)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t.FStar_Syntax_Syntax.pos
                                          uu____4818
                                         in
                                      let cvars =
                                        let uu____4849 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____4849
                                          (FStar_List.filter
                                             (fun x  ->
                                                let uu____4868 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    x
                                                   in
                                                let uu____4870 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    fsym
                                                   in
                                                uu____4868 <> uu____4870))
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
                                      let uu____4890 =
                                        FStar_Util.smap_try_find
                                          env.FStar_SMTEncoding_Env.cache
                                          tkey_hash
                                         in
                                      (match uu____4890 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____4898 =
                                             let uu____4899 =
                                               let uu____4907 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV)
                                                  in
                                               ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                                 uu____4907)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4899
                                              in
                                           (uu____4898,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (FStar_SMTEncoding_Env.use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____4919 =
                                               let uu____4921 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____4921
                                                in
                                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                               uu____4919
                                              in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_SMTEncoding_Term.fv_sort
                                               cvars
                                              in
                                           let caption =
                                             let uu____4936 =
                                               FStar_Options.log_queries ()
                                                in
                                             if uu____4936
                                             then
                                               let uu____4939 =
                                                 let uu____4941 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env.FStar_SMTEncoding_Env.tcenv
                                                     t0
                                                    in
                                                 FStar_Util.replace_char
                                                   uu____4941 10 32
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____4939
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
                                             let uu____4954 =
                                               let uu____4962 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars
                                                  in
                                               (tsym, uu____4962)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4954
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
                                             let uu____4981 =
                                               let uu____4989 =
                                                 FStar_SMTEncoding_Term.mkForall
                                                   t0.FStar_Syntax_Syntax.pos
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind)
                                                  in
                                               (uu____4989,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name)
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4981
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
                                             let uu____5006 =
                                               let uu____5014 =
                                                 let uu____5015 =
                                                   let uu____5026 =
                                                     let uu____5027 =
                                                       let uu____5032 =
                                                         let uu____5033 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f
                                                            in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____5033
                                                          in
                                                       (f_has_t, uu____5032)
                                                        in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____5027
                                                      in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____5026)
                                                    in
                                                 let uu____5051 =
                                                   mkForall_fuel
                                                     t0.FStar_Syntax_Syntax.pos
                                                    in
                                                 uu____5051 uu____5015  in
                                               (uu____5014,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____5006
                                              in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym
                                                in
                                             let uu____5074 =
                                               let uu____5082 =
                                                 let uu____5083 =
                                                   let uu____5094 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp)
                                                      in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____5094)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   t0.FStar_Syntax_Syntax.pos
                                                   uu____5083
                                                  in
                                               (uu____5082,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____5074
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
                                           ((let uu____5118 =
                                               FStar_SMTEncoding_Env.mk_cache_entry
                                                 env tsym cvar_sorts t_decls1
                                                in
                                             FStar_Util.smap_add
                                               env.FStar_SMTEncoding_Env.cache
                                               tkey_hash uu____5118);
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
                     let uu____5137 =
                       let uu____5145 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____5145,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____5137  in
                   let fsym =
                     FStar_SMTEncoding_Term.mk_fv
                       ("f", FStar_SMTEncoding_Term.Term_sort)
                      in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym  in
                     let uu____5159 =
                       let uu____5167 =
                         let uu____5168 =
                           let uu____5179 =
                             let uu____5180 =
                               let uu____5185 =
                                 let uu____5186 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____5186
                                  in
                               (f_has_t, uu____5185)  in
                             FStar_SMTEncoding_Util.mkImp uu____5180  in
                           ([[f_has_t]], [fsym], uu____5179)  in
                         let uu____5212 =
                           mkForall_fuel t0.FStar_Syntax_Syntax.pos  in
                         uu____5212 uu____5168  in
                       (uu____5167, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____5159  in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____5230 ->
           let uu____5237 =
             let uu____5242 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Env.Weak;
                 FStar_TypeChecker_Env.HNF;
                 FStar_TypeChecker_Env.EraseUniverses]
                 env.FStar_SMTEncoding_Env.tcenv t0
                in
             match uu____5242 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____5249;
                 FStar_Syntax_Syntax.vars = uu____5250;_} ->
                 let uu____5257 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____5257 with
                  | (b,f1) ->
                      let uu____5282 =
                        let uu____5283 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____5283  in
                      (uu____5282, f1))
             | uu____5298 -> failwith "impossible"  in
           (match uu____5237 with
            | (x,f) ->
                let uu____5310 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____5310 with
                 | (base_t,decls) ->
                     let uu____5321 =
                       FStar_SMTEncoding_Env.gen_term_var env x  in
                     (match uu____5321 with
                      | (x1,xtm,env') ->
                          let uu____5338 = encode_formula f env'  in
                          (match uu____5338 with
                           | (refinement,decls') ->
                               let uu____5349 =
                                 FStar_SMTEncoding_Env.fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____5349 with
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
                                      let uu____5377 =
                                        let uu____5388 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____5399 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____5388
                                          uu____5399
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____5377
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun y  ->
                                              (let uu____5453 =
                                                 FStar_SMTEncoding_Term.fv_name
                                                   y
                                                  in
                                               uu____5453 <> x1) &&
                                                (let uu____5457 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     y
                                                    in
                                                 uu____5457 <> fsym)))
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
                                    let uu____5489 =
                                      FStar_Util.smap_try_find
                                        env.FStar_SMTEncoding_Env.cache
                                        tkey_hash
                                       in
                                    (match uu____5489 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____5497 =
                                           let uu____5498 =
                                             let uu____5506 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV)
                                                in
                                             ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                               uu____5506)
                                              in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____5498
                                            in
                                         (uu____5497,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (FStar_SMTEncoding_Env.use_cache_entry
                                                    cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.FStar_SMTEncoding_Env.current_module_name
                                            in
                                         let tsym =
                                           let uu____5520 =
                                             let uu____5522 =
                                               let uu____5524 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____5524
                                                in
                                             Prims.strcat module_name
                                               uu____5522
                                              in
                                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                             uu____5520
                                            in
                                         let cvar_sorts =
                                           FStar_List.map
                                             FStar_SMTEncoding_Term.fv_sort
                                             cvars1
                                            in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None)
                                            in
                                         let t1 =
                                           let uu____5544 =
                                             let uu____5552 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1
                                                in
                                             (tsym, uu____5552)  in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____5544
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
                                           let uu____5572 =
                                             let uu____5580 =
                                               let uu____5581 =
                                                 let uu____5592 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base)
                                                    in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____5592)
                                                  in
                                               FStar_SMTEncoding_Term.mkForall
                                                 t0.FStar_Syntax_Syntax.pos
                                                 uu____5581
                                                in
                                             (uu____5580,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____5572
                                            in
                                         let t_kinding =
                                           let uu____5606 =
                                             let uu____5614 =
                                               FStar_SMTEncoding_Term.mkForall
                                                 t0.FStar_Syntax_Syntax.pos
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind)
                                                in
                                             (uu____5614,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____5606
                                            in
                                         let t_interp =
                                           let uu____5628 =
                                             let uu____5636 =
                                               let uu____5637 =
                                                 let uu____5648 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding)
                                                    in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____5648)
                                                  in
                                               FStar_SMTEncoding_Term.mkForall
                                                 t0.FStar_Syntax_Syntax.pos
                                                 uu____5637
                                                in
                                             (uu____5636,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement_interpretation"),
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____5628
                                            in
                                         let t_decls1 =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1])
                                            in
                                         ((let uu____5681 =
                                             FStar_SMTEncoding_Env.mk_cache_entry
                                               env tsym cvar_sorts t_decls1
                                              in
                                           FStar_Util.smap_add
                                             env.FStar_SMTEncoding_Env.cache
                                             tkey_hash uu____5681);
                                          (t1, t_decls1))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,uu____5683) ->
           let ttm =
             let uu____5701 =
               FStar_Syntax_Unionfind.uvar_id
                 uv.FStar_Syntax_Syntax.ctx_uvar_head
                in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____5701  in
           let uu____5703 =
             encode_term_pred FStar_Pervasives_Native.None
               uv.FStar_Syntax_Syntax.ctx_uvar_typ env ttm
              in
           (match uu____5703 with
            | (t_has_k,decls) ->
                let d =
                  let uu____5715 =
                    let uu____5723 =
                      let uu____5725 =
                        let uu____5727 =
                          let uu____5729 =
                            FStar_Syntax_Unionfind.uvar_id
                              uv.FStar_Syntax_Syntax.ctx_uvar_head
                             in
                          FStar_Util.string_of_int uu____5729  in
                        FStar_Util.format1 "uvar_typing_%s" uu____5727  in
                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                        uu____5725
                       in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____5723)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____5715  in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____5735 ->
           let uu____5752 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____5752 with
            | (head1,args_e) ->
                let uu____5799 =
                  let uu____5814 =
                    let uu____5815 = FStar_Syntax_Subst.compress head1  in
                    uu____5815.FStar_Syntax_Syntax.n  in
                  (uu____5814, args_e)  in
                (match uu____5799 with
                 | uu____5832 when head_redex env head1 ->
                     let uu____5847 = whnf env t  in
                     encode_term uu____5847 env
                 | uu____5848 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____5871 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5889) when
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
                       FStar_Syntax_Syntax.pos = uu____5911;
                       FStar_Syntax_Syntax.vars = uu____5912;_},uu____5913),uu____5914)
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
                       FStar_Syntax_Syntax.pos = uu____5940;
                       FStar_Syntax_Syntax.vars = uu____5941;_},uu____5942),
                    (v0,uu____5944)::(v1,uu____5946)::(v2,uu____5948)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____6019 = encode_term v0 env  in
                     (match uu____6019 with
                      | (v01,decls0) ->
                          let uu____6030 = encode_term v1 env  in
                          (match uu____6030 with
                           | (v11,decls1) ->
                               let uu____6041 = encode_term v2 env  in
                               (match uu____6041 with
                                | (v21,decls2) ->
                                    let uu____6052 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____6052,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(v0,uu____6055)::(v1,uu____6057)::(v2,uu____6059)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____6126 = encode_term v0 env  in
                     (match uu____6126 with
                      | (v01,decls0) ->
                          let uu____6137 = encode_term v1 env  in
                          (match uu____6137 with
                           | (v11,decls1) ->
                               let uu____6148 = encode_term v2 env  in
                               (match uu____6148 with
                                | (v21,decls2) ->
                                    let uu____6159 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____6159,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____6161)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____6197)::(rng,uu____6199)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____6250) ->
                     let e0 =
                       let uu____6272 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg
                         env.FStar_SMTEncoding_Env.tcenv head1 uu____6272
                        in
                     ((let uu____6282 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug
                              env.FStar_SMTEncoding_Env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____6282
                       then
                         let uu____6287 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____6287
                       else ());
                      (let e =
                         let uu____6295 =
                           let uu____6300 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____6301 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____6300
                             uu____6301
                            in
                         uu____6295 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____6312),(arg,uu____6314)::[]) -> encode_term arg env
                 | uu____6349 ->
                     let uu____6364 = encode_args args_e env  in
                     (match uu____6364 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____6425 = encode_term head1 env  in
                            match uu____6425 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____6497 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____6497 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____6595  ->
                                                 fun uu____6596  ->
                                                   match (uu____6595,
                                                           uu____6596)
                                                   with
                                                   | ((bv,uu____6626),
                                                      (a,uu____6628)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____6658 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____6658
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____6659 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm
                                             in
                                          (match uu____6659 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type
                                                  in
                                               let e_typing =
                                                 let uu____6674 =
                                                   let uu____6682 =
                                                     FStar_SMTEncoding_Term.mkForall
                                                       t0.FStar_Syntax_Syntax.pos
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____6691 =
                                                     let uu____6693 =
                                                       let uu____6695 =
                                                         let uu____6697 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm
                                                            in
                                                         FStar_Util.digest_of_string
                                                           uu____6697
                                                          in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____6695
                                                        in
                                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                       uu____6693
                                                      in
                                                   (uu____6682,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____6691)
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____6674
                                                  in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing])))))))
                             in
                          let encode_full_app fv =
                            let uu____6719 =
                              FStar_SMTEncoding_Env.lookup_free_var_sym env
                                fv
                               in
                            match uu____6719 with
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
                                   FStar_Syntax_Syntax.pos = uu____6762;
                                   FStar_Syntax_Syntax.vars = uu____6763;_},uu____6764)
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
                                   FStar_Syntax_Syntax.pos = uu____6771;
                                   FStar_Syntax_Syntax.vars = uu____6772;_},uu____6773)
                                ->
                                let uu____6778 =
                                  let uu____6779 =
                                    let uu____6784 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____6784
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____6779
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____6778
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____6814 =
                                  let uu____6815 =
                                    let uu____6820 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____6820
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____6815
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____6814
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____6849,(FStar_Util.Inl t1,uu____6851),uu____6852)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____6899,(FStar_Util.Inr c,uu____6901),uu____6902)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____6949 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____6970 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Env.Weak;
                                     FStar_TypeChecker_Env.HNF;
                                     FStar_TypeChecker_Env.EraseUniverses]
                                     env.FStar_SMTEncoding_Env.tcenv
                                     head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____6970
                                  in
                               let uu____6971 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____6971 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____6987;
                                            FStar_Syntax_Syntax.vars =
                                              uu____6988;_},uu____6989)
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
                                     | uu____7007 ->
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
           let uu____7086 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____7086 with
            | (bs1,body1,opening) ->
                let fallback uu____7111 =
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
                  let uu____7121 =
                    let uu____7122 =
                      FStar_SMTEncoding_Term.mk_fv
                        (f, FStar_SMTEncoding_Term.Term_sort)
                       in
                    FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV
                      uu____7122
                     in
                  (uu____7121, [decl])  in
                let is_impure rc =
                  let uu____7133 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                      env.FStar_SMTEncoding_Env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____7133 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____7148 =
                          let uu____7161 =
                            FStar_TypeChecker_Env.get_range
                              env.FStar_SMTEncoding_Env.tcenv
                             in
                          FStar_TypeChecker_Util.new_implicit_var
                            "SMTEncoding codomain" uu____7161
                            env.FStar_SMTEncoding_Env.tcenv
                            FStar_Syntax_Util.ktype0
                           in
                        (match uu____7148 with
                         | (t1,uu____7164,uu____7165) -> t1)
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  let uu____7183 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                     in
                  if uu____7183
                  then
                    let uu____7188 = FStar_Syntax_Syntax.mk_Total res_typ  in
                    FStar_Pervasives_Native.Some uu____7188
                  else
                    (let uu____7191 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid
                        in
                     if uu____7191
                     then
                       let uu____7196 = FStar_Syntax_Syntax.mk_GTotal res_typ
                          in
                       FStar_Pervasives_Native.Some uu____7196
                     else FStar_Pervasives_Native.None)
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____7204 =
                         let uu____7210 =
                           let uu____7212 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____7212
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____7210)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____7204);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____7217 =
                       (is_impure rc) &&
                         (let uu____7220 =
                            FStar_TypeChecker_Env.is_reifiable_rc
                              env.FStar_SMTEncoding_Env.tcenv rc
                             in
                          Prims.op_Negation uu____7220)
                        in
                     if uu____7217
                     then fallback ()
                     else
                       (let cache_size =
                          FStar_Util.smap_size
                            env.FStar_SMTEncoding_Env.cache
                           in
                        let uu____7231 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____7231 with
                        | (vars,guards,envbody,decls,uu____7256) ->
                            let body2 =
                              let uu____7270 =
                                FStar_TypeChecker_Env.is_reifiable_rc
                                  env.FStar_SMTEncoding_Env.tcenv rc
                                 in
                              if uu____7270
                              then
                                FStar_TypeChecker_Util.reify_body
                                  env.FStar_SMTEncoding_Env.tcenv body1
                              else body1  in
                            let uu____7275 = encode_term body2 envbody  in
                            (match uu____7275 with
                             | (body3,decls') ->
                                 let uu____7286 =
                                   let uu____7295 = codomain_eff rc  in
                                   match uu____7295 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____7314 = encode_term tfun env
                                          in
                                       (match uu____7314 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____7286 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____7348 =
                                          let uu____7359 =
                                            let uu____7360 =
                                              let uu____7365 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____7365, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____7360
                                             in
                                          ([], vars, uu____7359)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t0.FStar_Syntax_Syntax.pos
                                          uu____7348
                                         in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body
                                         in
                                      let uu____7373 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            (cvars, key_body)
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____7389 =
                                              let uu____7392 =
                                                let uu____7403 =
                                                  FStar_SMTEncoding_Term.free_variables
                                                    t1
                                                   in
                                                FStar_List.append uu____7403
                                                  cvars
                                                 in
                                              FStar_Util.remove_dups
                                                FStar_SMTEncoding_Term.fv_eq
                                                uu____7392
                                               in
                                            let uu____7430 =
                                              FStar_SMTEncoding_Util.mkAnd
                                                (key_body, t1)
                                               in
                                            (uu____7389, uu____7430)
                                         in
                                      (match uu____7373 with
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
                                           let uu____7452 =
                                             FStar_Util.smap_try_find
                                               env.FStar_SMTEncoding_Env.cache
                                               tkey_hash
                                              in
                                           (match uu____7452 with
                                            | FStar_Pervasives_Native.Some
                                                cache_entry ->
                                                let uu____7460 =
                                                  let uu____7461 =
                                                    let uu____7469 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                                      uu____7469)
                                                     in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____7461
                                                   in
                                                (uu____7460,
                                                  (FStar_List.append decls
                                                     (FStar_List.append
                                                        decls'
                                                        (FStar_List.append
                                                           decls''
                                                           (FStar_SMTEncoding_Env.use_cache_entry
                                                              cache_entry)))))
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                let uu____7475 =
                                                  is_an_eta_expansion env
                                                    vars body3
                                                   in
                                                (match uu____7475 with
                                                 | FStar_Pervasives_Native.Some
                                                     t1 ->
                                                     let decls1 =
                                                       let uu____7484 =
                                                         let uu____7486 =
                                                           FStar_Util.smap_size
                                                             env.FStar_SMTEncoding_Env.cache
                                                            in
                                                         uu____7486 =
                                                           cache_size
                                                          in
                                                       if uu____7484
                                                       then []
                                                       else
                                                         FStar_List.append
                                                           decls
                                                           (FStar_List.append
                                                              decls' decls'')
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
                                                       let module_name =
                                                         env.FStar_SMTEncoding_Env.current_module_name
                                                          in
                                                       let fsym =
                                                         let uu____7501 =
                                                           let uu____7503 =
                                                             FStar_Util.digest_of_string
                                                               tkey_hash
                                                              in
                                                           Prims.strcat
                                                             "Tm_abs_"
                                                             uu____7503
                                                            in
                                                         FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                           uu____7501
                                                          in
                                                       Prims.strcat
                                                         module_name
                                                         (Prims.strcat "_"
                                                            fsym)
                                                        in
                                                     let fdecl =
                                                       FStar_SMTEncoding_Term.DeclFun
                                                         (fsym, cvar_sorts,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           FStar_Pervasives_Native.None)
                                                        in
                                                     let f =
                                                       let uu____7513 =
                                                         let uu____7521 =
                                                           FStar_List.map
                                                             FStar_SMTEncoding_Util.mkFreeV
                                                             cvars1
                                                            in
                                                         (fsym, uu____7521)
                                                          in
                                                       FStar_SMTEncoding_Util.mkApp
                                                         uu____7513
                                                        in
                                                     let app =
                                                       mk_Apply f vars  in
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
                                                           let uu____7538 =
                                                             let uu____7539 =
                                                               let uu____7547
                                                                 =
                                                                 FStar_SMTEncoding_Term.mkForall
                                                                   t0.FStar_Syntax_Syntax.pos
                                                                   ([[f]],
                                                                    cvars1,
                                                                    f_has_t)
                                                                  in
                                                               (uu____7547,
                                                                 (FStar_Pervasives_Native.Some
                                                                    a_name),
                                                                 a_name)
                                                                in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____7539
                                                              in
                                                           [uu____7538]
                                                        in
                                                     let interp_f =
                                                       let a_name =
                                                         Prims.strcat
                                                           "interpretation_"
                                                           fsym
                                                          in
                                                       let uu____7562 =
                                                         let uu____7570 =
                                                           let uu____7571 =
                                                             let uu____7582 =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (app, body3)
                                                                in
                                                             ([[app]],
                                                               (FStar_List.append
                                                                  vars cvars1),
                                                               uu____7582)
                                                              in
                                                           FStar_SMTEncoding_Term.mkForall
                                                             t0.FStar_Syntax_Syntax.pos
                                                             uu____7571
                                                            in
                                                         (uu____7570,
                                                           (FStar_Pervasives_Native.Some
                                                              a_name),
                                                           a_name)
                                                          in
                                                       FStar_SMTEncoding_Util.mkAssume
                                                         uu____7562
                                                        in
                                                     let f_decls =
                                                       FStar_List.append
                                                         decls
                                                         (FStar_List.append
                                                            decls'
                                                            (FStar_List.append
                                                               decls''
                                                               (FStar_List.append
                                                                  (fdecl ::
                                                                  typing_f)
                                                                  [interp_f])))
                                                        in
                                                     ((let uu____7597 =
                                                         FStar_SMTEncoding_Env.mk_cache_entry
                                                           env fsym
                                                           cvar_sorts f_decls
                                                          in
                                                       FStar_Util.smap_add
                                                         env.FStar_SMTEncoding_Env.cache
                                                         tkey_hash uu____7597);
                                                      (f, f_decls))))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____7598,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____7599;
                          FStar_Syntax_Syntax.lbunivs = uu____7600;
                          FStar_Syntax_Syntax.lbtyp = uu____7601;
                          FStar_Syntax_Syntax.lbeff = uu____7602;
                          FStar_Syntax_Syntax.lbdef = uu____7603;
                          FStar_Syntax_Syntax.lbattrs = uu____7604;
                          FStar_Syntax_Syntax.lbpos = uu____7605;_}::uu____7606),uu____7607)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____7641;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____7643;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____7645;
                FStar_Syntax_Syntax.lbpos = uu____7646;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____7673 ->
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
              let uu____7745 =
                let uu____7750 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____7750 env  in
              match uu____7745 with
              | (ee1,decls1) ->
                  let uu____7775 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____7775 with
                   | (xs,e21) ->
                       let uu____7800 = FStar_List.hd xs  in
                       (match uu____7800 with
                        | (x1,uu____7818) ->
                            let env' =
                              FStar_SMTEncoding_Env.push_term_var env x1 ee1
                               in
                            let uu____7824 = encode_body e21 env'  in
                            (match uu____7824 with
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
            let uu____7854 =
              let uu____7862 =
                let uu____7863 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____7863  in
              FStar_SMTEncoding_Env.gen_term_var env uu____7862  in
            match uu____7854 with
            | (scrsym,scr',env1) ->
                let uu____7873 = encode_term e env1  in
                (match uu____7873 with
                 | (scr,decls) ->
                     let uu____7884 =
                       let encode_branch b uu____7913 =
                         match uu____7913 with
                         | (else_case,decls1) ->
                             let uu____7932 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____7932 with
                              | (p,w,br) ->
                                  let uu____7958 = encode_pat env1 p  in
                                  (match uu____7958 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____7995  ->
                                                   match uu____7995 with
                                                   | (x,t) ->
                                                       FStar_SMTEncoding_Env.push_term_var
                                                         env2 x t) env1)
                                          in
                                       let uu____8002 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____8024 =
                                               encode_term w1 env2  in
                                             (match uu____8024 with
                                              | (w2,decls2) ->
                                                  let uu____8037 =
                                                    let uu____8038 =
                                                      let uu____8043 =
                                                        let uu____8044 =
                                                          let uu____8049 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____8049)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____8044
                                                         in
                                                      (guard, uu____8043)  in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____8038
                                                     in
                                                  (uu____8037, decls2))
                                          in
                                       (match uu____8002 with
                                        | (guard1,decls2) ->
                                            let uu____8064 =
                                              encode_br br env2  in
                                            (match uu____8064 with
                                             | (br1,decls3) ->
                                                 let uu____8077 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____8077,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____7884 with
                      | (match_tm,decls1) ->
                          let uu____8098 =
                            let uu____8099 =
                              let uu____8110 =
                                let uu____8117 =
                                  let uu____8122 =
                                    FStar_SMTEncoding_Term.mk_fv
                                      (scrsym,
                                        FStar_SMTEncoding_Term.Term_sort)
                                     in
                                  (uu____8122, scr)  in
                                [uu____8117]  in
                              (uu____8110, match_tm)  in
                            FStar_SMTEncoding_Term.mkLet' uu____8099
                              FStar_Range.dummyRange
                             in
                          (uu____8098, decls1)))

and (encode_pat :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.pat -> (FStar_SMTEncoding_Env.env_t * pattern))
  =
  fun env  ->
    fun pat  ->
      (let uu____8145 =
         FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
           FStar_Options.Medium
          in
       if uu____8145
       then
         let uu____8148 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____8148
       else ());
      (let uu____8153 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____8153 with
       | (vars,pat_term) ->
           let uu____8170 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____8212  ->
                     fun v1  ->
                       match uu____8212 with
                       | (env1,vars1) ->
                           let uu____8248 =
                             FStar_SMTEncoding_Env.gen_term_var env1 v1  in
                           (match uu____8248 with
                            | (xx,uu____8267,env2) ->
                                let uu____8271 =
                                  let uu____8278 =
                                    let uu____8283 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xx,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    (v1, uu____8283)  in
                                  uu____8278 :: vars1  in
                                (env2, uu____8271))) (env, []))
              in
           (match uu____8170 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____8338 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____8339 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____8340 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____8348 = encode_const c env1  in
                      (match uu____8348 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____8356::uu____8357 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____8361 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon
                            env1.FStar_SMTEncoding_Env.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____8384 =
                          FStar_TypeChecker_Env.datacons_of_typ
                            env1.FStar_SMTEncoding_Env.tcenv tc_name
                           in
                        match uu____8384 with
                        | (uu____8392,uu____8393::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____8398 ->
                            FStar_SMTEncoding_Env.mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____8434  ->
                                  match uu____8434 with
                                  | (arg,uu____8444) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____8453 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____8453))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____8485) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____8516 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____8541 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____8587  ->
                                  match uu____8587 with
                                  | (arg,uu____8603) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____8612 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____8612))
                         in
                      FStar_All.pipe_right uu____8541 FStar_List.flatten
                   in
                let pat_term1 uu____8643 = encode_term pat_term env1  in
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
      let uu____8653 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____8701  ->
                fun uu____8702  ->
                  match (uu____8701, uu____8702) with
                  | ((tms,decls),(t,uu____8742)) ->
                      let uu____8769 = encode_term t env  in
                      (match uu____8769 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____8653 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____8826 = FStar_Syntax_Util.list_elements e  in
        match uu____8826 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____8857 =
          let uu____8874 = FStar_Syntax_Util.unmeta p  in
          FStar_All.pipe_right uu____8874 FStar_Syntax_Util.head_and_args  in
        match uu____8857 with
        | (head1,args) ->
            let uu____8925 =
              let uu____8940 =
                let uu____8941 = FStar_Syntax_Util.un_uinst head1  in
                uu____8941.FStar_Syntax_Syntax.n  in
              (uu____8940, args)  in
            (match uu____8925 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____8963,uu____8964)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____9016 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or1 t1 =
          let uu____9071 =
            let uu____9088 = FStar_Syntax_Util.unmeta t1  in
            FStar_All.pipe_right uu____9088 FStar_Syntax_Util.head_and_args
             in
          match uu____9071 with
          | (head1,args) ->
              let uu____9135 =
                let uu____9150 =
                  let uu____9151 = FStar_Syntax_Util.un_uinst head1  in
                  uu____9151.FStar_Syntax_Syntax.n  in
                (uu____9150, args)  in
              (match uu____9135 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____9170)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____9207 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____9237 = smt_pat_or1 t1  in
            (match uu____9237 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____9259 = list_elements1 e  in
                 FStar_All.pipe_right uu____9259
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____9289 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____9289
                           (FStar_List.map one_pat)))
             | uu____9312 ->
                 let uu____9317 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____9317])
        | uu____9368 ->
            let uu____9371 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____9371]
         in
      let uu____9422 =
        let uu____9437 =
          let uu____9438 = FStar_Syntax_Subst.compress t  in
          uu____9438.FStar_Syntax_Syntax.n  in
        match uu____9437 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____9477 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____9477 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____9512;
                        FStar_Syntax_Syntax.effect_name = uu____9513;
                        FStar_Syntax_Syntax.result_typ = uu____9514;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____9516)::(post,uu____9518)::(pats,uu____9520)::[];
                        FStar_Syntax_Syntax.flags = uu____9521;_}
                      ->
                      let uu____9582 = lemma_pats pats  in
                      (binders1, pre, post, uu____9582)
                  | uu____9593 -> failwith "impos"))
        | uu____9609 -> failwith "Impos"  in
      match uu____9422 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___366_9646 = env  in
            {
              FStar_SMTEncoding_Env.bvar_bindings =
                (uu___366_9646.FStar_SMTEncoding_Env.bvar_bindings);
              FStar_SMTEncoding_Env.fvar_bindings =
                (uu___366_9646.FStar_SMTEncoding_Env.fvar_bindings);
              FStar_SMTEncoding_Env.depth =
                (uu___366_9646.FStar_SMTEncoding_Env.depth);
              FStar_SMTEncoding_Env.tcenv =
                (uu___366_9646.FStar_SMTEncoding_Env.tcenv);
              FStar_SMTEncoding_Env.warn =
                (uu___366_9646.FStar_SMTEncoding_Env.warn);
              FStar_SMTEncoding_Env.cache =
                (uu___366_9646.FStar_SMTEncoding_Env.cache);
              FStar_SMTEncoding_Env.nolabels =
                (uu___366_9646.FStar_SMTEncoding_Env.nolabels);
              FStar_SMTEncoding_Env.use_zfuel_name = true;
              FStar_SMTEncoding_Env.encode_non_total_function_typ =
                (uu___366_9646.FStar_SMTEncoding_Env.encode_non_total_function_typ);
              FStar_SMTEncoding_Env.current_module_name =
                (uu___366_9646.FStar_SMTEncoding_Env.current_module_name);
              FStar_SMTEncoding_Env.encoding_quantifier =
                (uu___366_9646.FStar_SMTEncoding_Env.encoding_quantifier)
            }  in
          let uu____9648 =
            encode_binders FStar_Pervasives_Native.None binders env1  in
          (match uu____9648 with
           | (vars,guards,env2,decls,uu____9673) ->
               let uu____9686 = encode_smt_patterns patterns env2  in
               (match uu____9686 with
                | (pats,decls') ->
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
                    let env3 =
                      let uu___367_9719 = env2  in
                      {
                        FStar_SMTEncoding_Env.bvar_bindings =
                          (uu___367_9719.FStar_SMTEncoding_Env.bvar_bindings);
                        FStar_SMTEncoding_Env.fvar_bindings =
                          (uu___367_9719.FStar_SMTEncoding_Env.fvar_bindings);
                        FStar_SMTEncoding_Env.depth =
                          (uu___367_9719.FStar_SMTEncoding_Env.depth);
                        FStar_SMTEncoding_Env.tcenv =
                          (uu___367_9719.FStar_SMTEncoding_Env.tcenv);
                        FStar_SMTEncoding_Env.warn =
                          (uu___367_9719.FStar_SMTEncoding_Env.warn);
                        FStar_SMTEncoding_Env.cache =
                          (uu___367_9719.FStar_SMTEncoding_Env.cache);
                        FStar_SMTEncoding_Env.nolabels = true;
                        FStar_SMTEncoding_Env.use_zfuel_name =
                          (uu___367_9719.FStar_SMTEncoding_Env.use_zfuel_name);
                        FStar_SMTEncoding_Env.encode_non_total_function_typ =
                          (uu___367_9719.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                        FStar_SMTEncoding_Env.current_module_name =
                          (uu___367_9719.FStar_SMTEncoding_Env.current_module_name);
                        FStar_SMTEncoding_Env.encoding_quantifier =
                          (uu___367_9719.FStar_SMTEncoding_Env.encoding_quantifier)
                      }  in
                    let uu____9721 =
                      let uu____9726 = FStar_Syntax_Util.unmeta pre  in
                      encode_formula uu____9726 env3  in
                    (match uu____9721 with
                     | (pre1,decls'') ->
                         let uu____9733 =
                           let uu____9738 = FStar_Syntax_Util.unmeta post1
                              in
                           encode_formula uu____9738 env3  in
                         (match uu____9733 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append decls'
                                     (FStar_List.append decls'' decls'''))
                                 in
                              let uu____9748 =
                                let uu____9749 =
                                  let uu____9760 =
                                    let uu____9761 =
                                      let uu____9766 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards)
                                         in
                                      (uu____9766, post2)  in
                                    FStar_SMTEncoding_Util.mkImp uu____9761
                                     in
                                  (pats, vars, uu____9760)  in
                                FStar_SMTEncoding_Term.mkForall
                                  t.FStar_Syntax_Syntax.pos uu____9749
                                 in
                              (uu____9748, decls1)))))

and (encode_smt_patterns :
  FStar_Syntax_Syntax.arg Prims.list Prims.list ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term Prims.list Prims.list *
        FStar_SMTEncoding_Term.decl Prims.list))
  =
  fun pats_l  ->
    fun env  ->
      let env1 =
        let uu___368_9788 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___368_9788.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___368_9788.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___368_9788.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___368_9788.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___368_9788.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.cache =
            (uu___368_9788.FStar_SMTEncoding_Env.cache);
          FStar_SMTEncoding_Env.nolabels =
            (uu___368_9788.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___368_9788.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___368_9788.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___368_9788.FStar_SMTEncoding_Env.encoding_quantifier)
        }  in
      let encode_smt_pattern t =
        let uu____9804 = FStar_Syntax_Util.head_and_args t  in
        match uu____9804 with
        | (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____9867::(x,uu____9869)::(t1,uu____9871)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____9938 = encode_term x env1  in
                 (match uu____9938 with
                  | (x1,decls) ->
                      let uu____9949 = encode_term t1 env1  in
                      (match uu____9949 with
                       | (t2,decls') ->
                           let uu____9960 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                           (uu____9960, (FStar_List.append decls decls'))))
             | uu____9961 -> encode_term t env1)
         in
      FStar_List.fold_right
        (fun pats  ->
           fun uu____10004  ->
             match uu____10004 with
             | (pats_l1,decls) ->
                 let uu____10049 =
                   FStar_List.fold_right
                     (fun uu____10084  ->
                        fun uu____10085  ->
                          match (uu____10084, uu____10085) with
                          | ((p,uu____10127),(pats1,decls1)) ->
                              let uu____10162 = encode_smt_pattern p  in
                              (match uu____10162 with
                               | (t,d) ->
                                   let uu____10177 =
                                     FStar_SMTEncoding_Term.check_pattern_ok
                                       t
                                      in
                                   (match uu____10177 with
                                    | FStar_Pervasives_Native.None  ->
                                        ((t :: pats1),
                                          (FStar_List.append d decls1))
                                    | FStar_Pervasives_Native.Some
                                        illegal_subterm ->
                                        ((let uu____10194 =
                                            let uu____10200 =
                                              let uu____10202 =
                                                FStar_Syntax_Print.term_to_string
                                                  p
                                                 in
                                              let uu____10204 =
                                                FStar_SMTEncoding_Term.print_smt_term
                                                  illegal_subterm
                                                 in
                                              FStar_Util.format2
                                                "Pattern %s contains illegal sub-term (%s); dropping it"
                                                uu____10202 uu____10204
                                               in
                                            (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                                              uu____10200)
                                             in
                                          FStar_Errors.log_issue
                                            p.FStar_Syntax_Syntax.pos
                                            uu____10194);
                                         (pats1,
                                           (FStar_List.append d decls1))))))
                     pats ([], decls)
                    in
                 (match uu____10049 with
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
        let uu____10264 =
          FStar_All.pipe_left
            (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____10264
        then
          let uu____10269 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____10271 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10269 uu____10271
        else ()  in
      let enc f r l =
        let uu____10313 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10345 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____10345 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____10313 with
        | (decls,args) ->
            let uu____10376 =
              let uu___369_10377 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___369_10377.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___369_10377.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10376, decls)
         in
      let const_op f r uu____10412 =
        let uu____10425 = f r  in (uu____10425, [])  in
      let un_op f l =
        let uu____10448 = FStar_List.hd l  in
        FStar_All.pipe_left f uu____10448  in
      let bin_op f uu___360_10468 =
        match uu___360_10468 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10479 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____10520 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____10545  ->
                 match uu____10545 with
                 | (t,uu____10561) ->
                     let uu____10566 = encode_formula t env  in
                     (match uu____10566 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____10520 with
        | (decls,phis) ->
            let uu____10595 =
              let uu___370_10596 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___370_10596.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___370_10596.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10595, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____10659  ->
               match uu____10659 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____10680) -> false
                    | uu____10683 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____10702 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____10702
        else
          (let uu____10719 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____10719 r rf)
         in
      let eq3_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____10791 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::t1::v0::v1::[] ->
                     let uu____10823 =
                       let uu____10828 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____10829 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____10828, uu____10829)  in
                     FStar_SMTEncoding_Util.mkAnd uu____10823
                 | uu____10830 -> failwith "Impossible")
             in
          uu____10791 r args
        else
          (let uu____10836 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____10836)
         in
      let h_equals_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____10908 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::v0::t1::v1::[] ->
                     let uu____10940 =
                       let uu____10945 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____10946 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____10945, uu____10946)  in
                     FStar_SMTEncoding_Util.mkAnd uu____10940
                 | uu____10947 -> failwith "Impossible")
             in
          uu____10908 r args
        else
          (let uu____10953 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____10953)
         in
      let mk_imp1 r uu___361_10988 =
        match uu___361_10988 with
        | (lhs,uu____10994)::(rhs,uu____10996)::[] ->
            let uu____11037 = encode_formula rhs env  in
            (match uu____11037 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11052) ->
                      (l1, decls1)
                  | uu____11057 ->
                      let uu____11058 = encode_formula lhs env  in
                      (match uu____11058 with
                       | (l2,decls2) ->
                           let uu____11069 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____11069, (FStar_List.append decls1 decls2)))))
        | uu____11070 -> failwith "impossible"  in
      let mk_ite r uu___362_11098 =
        match uu___362_11098 with
        | (guard,uu____11104)::(_then,uu____11106)::(_else,uu____11108)::[]
            ->
            let uu____11165 = encode_formula guard env  in
            (match uu____11165 with
             | (g,decls1) ->
                 let uu____11176 = encode_formula _then env  in
                 (match uu____11176 with
                  | (t,decls2) ->
                      let uu____11187 = encode_formula _else env  in
                      (match uu____11187 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11199 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____11229 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l
           in
        f uu____11229  in
      let connectives =
        let uu____11259 =
          let uu____11284 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____11284)  in
        let uu____11327 =
          let uu____11354 =
            let uu____11379 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____11379)  in
          let uu____11422 =
            let uu____11449 =
              let uu____11476 =
                let uu____11501 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____11501)  in
              let uu____11544 =
                let uu____11571 =
                  let uu____11598 =
                    let uu____11623 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____11623)  in
                  [uu____11598;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.c_eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq3_op);
                  (FStar_Parser_Const.c_eq3_lid, h_equals_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11571  in
              uu____11476 :: uu____11544  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11449  in
          uu____11354 :: uu____11422  in
        uu____11259 :: uu____11327  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____12168 = encode_formula phi' env  in
            (match uu____12168 with
             | (phi2,decls) ->
                 let uu____12179 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____12179, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____12181 ->
            let uu____12188 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____12188 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____12227 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____12227 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____12239;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____12241;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____12243;
                 FStar_Syntax_Syntax.lbpos = uu____12244;_}::[]),e2)
            ->
            let uu____12271 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____12271 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____12324::(x,uu____12326)::(t,uu____12328)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12395 = encode_term x env  in
                 (match uu____12395 with
                  | (x1,decls) ->
                      let uu____12406 = encode_term t env  in
                      (match uu____12406 with
                       | (t1,decls') ->
                           let uu____12417 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____12417, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12420)::(msg,uu____12422)::(phi2,uu____12424)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12491 =
                   let uu____12496 =
                     let uu____12497 = FStar_Syntax_Subst.compress r  in
                     uu____12497.FStar_Syntax_Syntax.n  in
                   let uu____12500 =
                     let uu____12501 = FStar_Syntax_Subst.compress msg  in
                     uu____12501.FStar_Syntax_Syntax.n  in
                   (uu____12496, uu____12500)  in
                 (match uu____12491 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12510))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____12521 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____12528)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____12563 when head_redex env head2 ->
                 let uu____12578 = whnf env phi1  in
                 encode_formula uu____12578 env
             | uu____12579 ->
                 let uu____12594 = encode_term phi1 env  in
                 (match uu____12594 with
                  | (tt,decls) ->
                      let tt1 =
                        let uu____12606 =
                          let uu____12608 =
                            FStar_Range.use_range
                              tt.FStar_SMTEncoding_Term.rng
                             in
                          let uu____12609 =
                            FStar_Range.use_range
                              phi1.FStar_Syntax_Syntax.pos
                             in
                          FStar_Range.rng_included uu____12608 uu____12609
                           in
                        if uu____12606
                        then tt
                        else
                          (let uu___371_12613 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___371_12613.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___371_12613.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      let uu____12614 = FStar_SMTEncoding_Term.mk_Valid tt1
                         in
                      (uu____12614, decls)))
        | uu____12615 ->
            let uu____12616 = encode_term phi1 env  in
            (match uu____12616 with
             | (tt,decls) ->
                 let tt1 =
                   let uu____12628 =
                     let uu____12630 =
                       FStar_Range.use_range tt.FStar_SMTEncoding_Term.rng
                        in
                     let uu____12631 =
                       FStar_Range.use_range phi1.FStar_Syntax_Syntax.pos  in
                     FStar_Range.rng_included uu____12630 uu____12631  in
                   if uu____12628
                   then tt
                   else
                     (let uu___372_12635 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___372_12635.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___372_12635.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 let uu____12636 = FStar_SMTEncoding_Term.mk_Valid tt1  in
                 (uu____12636, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____12680 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____12680 with
        | (vars,guards,env2,decls,uu____12719) ->
            let uu____12732 = encode_smt_patterns ps env2  in
            (match uu____12732 with
             | (pats,decls') ->
                 let uu____12775 = encode_formula body env2  in
                 (match uu____12775 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12807;
                             FStar_SMTEncoding_Term.rng = uu____12808;_}::[])::[]
                            when
                            let uu____12828 =
                              FStar_Ident.text_of_lid
                                FStar_Parser_Const.guard_free
                               in
                            uu____12828 = gf -> []
                        | uu____12831 -> guards  in
                      let uu____12836 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____12836, body1,
                        (FStar_List.append decls
                           (FStar_List.append decls' decls'')))))
         in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi  in
       let uu____12847 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____12847 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12856 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____12962  ->
                     match uu____12962 with
                     | (l,uu____12987) -> FStar_Ident.lid_equals op l))
              in
           (match uu____12856 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____13056,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____13148 = encode_q_body env vars pats body  in
             match uu____13148 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____13193 =
                     let uu____13204 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____13204)  in
                   FStar_SMTEncoding_Term.mkForall
                     phi1.FStar_Syntax_Syntax.pos uu____13193
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____13235 = encode_q_body env vars pats body  in
             match uu____13235 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____13279 =
                   let uu____13280 =
                     let uu____13291 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____13291)  in
                   FStar_SMTEncoding_Term.mkExists
                     phi1.FStar_Syntax_Syntax.pos uu____13280
                    in
                 (uu____13279, decls))))
