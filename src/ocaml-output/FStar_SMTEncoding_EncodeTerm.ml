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
               (fun uu___48_382  ->
                  match uu___48_382 with
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
  fun uu___49_672  ->
    match uu___49_672 with
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
          let uu____1944 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue  in
          (uu____1944, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____1946 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse  in
          (uu____1946, [])
      | FStar_Const.Const_char c1 ->
          let uu____1949 =
            let uu____1950 =
              let uu____1958 =
                let uu____1961 =
                  let uu____1962 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1)
                     in
                  FStar_SMTEncoding_Term.boxInt uu____1962  in
                [uu____1961]  in
              ("FStar.Char.__char_of_int", uu____1958)  in
            FStar_SMTEncoding_Util.mkApp uu____1950  in
          (uu____1949, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____1980 =
            let uu____1981 = FStar_SMTEncoding_Util.mkInteger i  in
            FStar_SMTEncoding_Term.boxInt uu____1981  in
          (uu____1980, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.FStar_SMTEncoding_Env.tcenv).FStar_TypeChecker_Env.dsenv
              repr sw FStar_Range.dummyRange
             in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____2002) ->
          let uu____2005 =
            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.string_const s
             in
          (uu____2005, [])
      | FStar_Const.Const_range uu____2006 ->
          let uu____2007 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          (uu____2007, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | c1 ->
          let uu____2009 =
            let uu____2011 = FStar_Syntax_Print.const_to_string c1  in
            FStar_Util.format1 "Unhandled constant: %s" uu____2011  in
          failwith uu____2009

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
        (let uu____2040 =
           FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
             FStar_Options.Medium
            in
         if uu____2040
         then
           let uu____2043 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____2043
         else ());
        (let uu____2049 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2131  ->
                   fun b  ->
                     match uu____2131 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2196 =
                           let x = FStar_Pervasives_Native.fst b  in
                           let uu____2212 =
                             FStar_SMTEncoding_Env.gen_term_var env1 x  in
                           match uu____2212 with
                           | (xxsym,xx,env') ->
                               let uu____2237 =
                                 let uu____2242 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____2242 env1 xx
                                  in
                               (match uu____2237 with
                                | (guard_x_t,decls') ->
                                    let uu____2257 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xxsym,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    (uu____2257, guard_x_t, env', decls', x))
                            in
                         (match uu____2196 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____2049 with
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
          let uu____2357 = encode_term t env  in
          match uu____2357 with
          | (t1,decls) ->
              let uu____2368 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____2368, decls)

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
          let uu____2379 = encode_term t env  in
          match uu____2379 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____2394 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____2394, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____2396 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____2396, decls))

and (encode_arith_term :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____2402 = encode_args args_e env  in
        match uu____2402 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____2421 -> failwith "Impossible"  in
            let unary arg_tms1 =
              let uu____2433 = FStar_List.hd arg_tms1  in
              FStar_SMTEncoding_Term.unboxInt uu____2433  in
            let binary arg_tms1 =
              let uu____2448 =
                let uu____2449 = FStar_List.hd arg_tms1  in
                FStar_SMTEncoding_Term.unboxInt uu____2449  in
              let uu____2450 =
                let uu____2451 =
                  let uu____2452 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____2452  in
                FStar_SMTEncoding_Term.unboxInt uu____2451  in
              (uu____2448, uu____2450)  in
            let mk_default uu____2460 =
              let uu____2461 =
                FStar_SMTEncoding_Env.lookup_free_var_sym env
                  head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____2461 with
              | (fname,fuel_args,arity) ->
                  let args = FStar_List.append fuel_args arg_tms  in
                  maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity
                    args
               in
            let mk_l op mk_args ts =
              let uu____2538 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____2538
              then
                let uu____2541 =
                  let uu____2542 = mk_args ts  in op uu____2542  in
                FStar_All.pipe_right uu____2541 FStar_SMTEncoding_Term.boxInt
              else mk_default ()  in
            let mk_nl nm op ts =
              let uu____2580 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____2580
              then
                let uu____2583 = binary ts  in
                match uu____2583 with
                | (t1,t2) ->
                    let uu____2590 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____2590
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____2596 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____2596
                 then
                   let uu____2599 =
                     let uu____2600 = binary ts  in op uu____2600  in
                   FStar_All.pipe_right uu____2599
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
            let uu____2765 =
              let uu____2775 =
                FStar_List.tryFind
                  (fun uu____2799  ->
                     match uu____2799 with
                     | (l,uu____2810) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____2775 FStar_Util.must  in
            (match uu____2765 with
             | (uu____2854,op) ->
                 let uu____2866 = op arg_tms  in (uu____2866, decls))

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
        let uu____2882 = FStar_List.hd args_e  in
        match uu____2882 with
        | (tm_sz,uu____2898) ->
            let uu____2907 = uu____2882  in
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let t_decls1 = FStar_SMTEncoding_Term.mkBvConstructor sz  in
              FStar_SMTEncoding_Term.mk_decls "" sz_key t_decls1 []  in
            let uu____2918 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____2944::(sz_arg,uu____2946)::uu____2947::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____3014 =
                    let uu____3015 = FStar_List.tail args_e  in
                    FStar_List.tail uu____3015  in
                  let uu____3042 =
                    let uu____3046 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____3046  in
                  (uu____3014, uu____3042)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____3053::(sz_arg,uu____3055)::uu____3056::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____3123 =
                    let uu____3125 = FStar_Syntax_Print.term_to_string sz_arg
                       in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____3125
                     in
                  failwith uu____3123
              | uu____3135 ->
                  let uu____3150 = FStar_List.tail args_e  in
                  (uu____3150, FStar_Pervasives_Native.None)
               in
            (match uu____2918 with
             | (arg_tms,ext_sz) ->
                 let uu____3177 = encode_args arg_tms env  in
                 (match uu____3177 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____3198 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____3210 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____3210  in
                      let unary_arith arg_tms2 =
                        let uu____3221 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____3221  in
                      let binary arg_tms2 =
                        let uu____3236 =
                          let uu____3237 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3237
                           in
                        let uu____3238 =
                          let uu____3239 =
                            let uu____3240 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____3240  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3239
                           in
                        (uu____3236, uu____3238)  in
                      let binary_arith arg_tms2 =
                        let uu____3257 =
                          let uu____3258 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3258
                           in
                        let uu____3259 =
                          let uu____3260 =
                            let uu____3261 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____3261  in
                          FStar_SMTEncoding_Term.unboxInt uu____3260  in
                        (uu____3257, uu____3259)  in
                      let mk_bv op mk_args resBox ts =
                        let uu____3319 =
                          let uu____3320 = mk_args ts  in op uu____3320  in
                        FStar_All.pipe_right uu____3319 resBox  in
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
                        let uu____3452 =
                          let uu____3457 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____3457  in
                        let uu____3466 =
                          let uu____3471 =
                            let uu____3473 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____3473  in
                          FStar_SMTEncoding_Term.boxBitVec uu____3471  in
                        mk_bv uu____3452 unary uu____3466 arg_tms2  in
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
                      let uu____3713 =
                        let uu____3723 =
                          FStar_List.tryFind
                            (fun uu____3747  ->
                               match uu____3747 with
                               | (l,uu____3758) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____3723 FStar_Util.must  in
                      (match uu____3713 with
                       | (uu____3804,op) ->
                           let uu____3816 = op arg_tms1  in
                           (uu____3816, (FStar_List.append sz_decls decls)))))

and (encode_deeply_embedded_quantifier :
  FStar_Syntax_Syntax.term ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let env1 =
        let uu___53_3826 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___53_3826.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___53_3826.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___53_3826.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___53_3826.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___53_3826.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___53_3826.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name =
            (uu___53_3826.FStar_SMTEncoding_Env.use_zfuel_name);
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___53_3826.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___53_3826.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier = true;
          FStar_SMTEncoding_Env.global_cache =
            (uu___53_3826.FStar_SMTEncoding_Env.global_cache)
        }  in
      let uu____3828 = encode_term t env1  in
      match uu____3828 with
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
               (uu____3854,{
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.FreeV uu____3855;
                             FStar_SMTEncoding_Term.freevars = uu____3856;
                             FStar_SMTEncoding_Term.rng = uu____3857;_}::
                {
                  FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV
                    uu____3858;
                  FStar_SMTEncoding_Term.freevars = uu____3859;
                  FStar_SMTEncoding_Term.rng = uu____3860;_}::[])
               ->
               (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                  (FStar_Errors.Warning_QuantifierWithoutPattern,
                    "Not encoding deeply embedded, unguarded quantifier to SMT");
                (tm, decls))
           | uu____3906 ->
               let uu____3907 = encode_formula t env1  in
               (match uu____3907 with
                | (phi,decls') ->
                    let interp =
                      match vars with
                      | [] ->
                          let uu____3927 =
                            let uu____3932 =
                              FStar_SMTEncoding_Term.mk_Valid tm  in
                            (uu____3932, phi)  in
                          FStar_SMTEncoding_Util.mkIff uu____3927
                      | uu____3933 ->
                          let uu____3934 =
                            let uu____3945 =
                              let uu____3946 =
                                let uu____3951 =
                                  FStar_SMTEncoding_Term.mk_Valid tm  in
                                (uu____3951, phi)  in
                              FStar_SMTEncoding_Util.mkIff uu____3946  in
                            ([[valid_tm]], vars, uu____3945)  in
                          FStar_SMTEncoding_Term.mkForall
                            t.FStar_Syntax_Syntax.pos uu____3934
                       in
                    let ax =
                      let uu____3961 =
                        let uu____3969 =
                          let uu____3971 =
                            FStar_Util.digest_of_string tkey_hash  in
                          Prims.strcat "l_quant_interp_" uu____3971  in
                        (interp,
                          (FStar_Pervasives_Native.Some
                             "Interpretation of deeply embedded quantifier"),
                          uu____3969)
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____3961  in
                    let uu____3977 =
                      let uu____3978 =
                        let uu____3981 =
                          FStar_SMTEncoding_Term.mk_decls "" tkey_hash 
                            [ax] (FStar_List.append decls decls')
                           in
                        FStar_List.append decls' uu____3981  in
                      FStar_List.append decls uu____3978  in
                    (tm, uu____3977)))

and (encode_term :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____3993 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____3993
       then
         let uu____3998 = FStar_Syntax_Print.tag_of_term t  in
         let uu____4000 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____4002 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____3998 uu____4000
           uu____4002
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____4011 ->
           let uu____4034 =
             let uu____4036 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____4039 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____4041 = FStar_Syntax_Print.term_to_string t0  in
             let uu____4043 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____4036
               uu____4039 uu____4041 uu____4043
              in
           failwith uu____4034
       | FStar_Syntax_Syntax.Tm_unknown  ->
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
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let e = FStar_Syntax_Util.unfold_lazy i  in
           ((let uu____4069 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____4069
             then
               let uu____4074 = FStar_Syntax_Print.term_to_string t0  in
               let uu____4076 = FStar_Syntax_Print.term_to_string e  in
               FStar_Util.print2 ">> Unfolded (%s) ~> (%s)\n" uu____4074
                 uu____4076
             else ());
            encode_term e env)
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____4082 =
             let uu____4084 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____4084
              in
           failwith uu____4082
       | FStar_Syntax_Syntax.Tm_ascribed (t1,(k,uu____4093),uu____4094) ->
           let uu____4143 =
             match k with
             | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
             | uu____4153 -> false  in
           if uu____4143
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t1 env
       | FStar_Syntax_Syntax.Tm_quoted (qt,uu____4171) ->
           let tv =
             let uu____4177 =
               let uu____4184 = FStar_Reflection_Basic.inspect_ln qt  in
               FStar_Syntax_Embeddings.embed
                 FStar_Reflection_Embeddings.e_term_view uu____4184
                in
             uu____4177 t.FStar_Syntax_Syntax.pos
               FStar_Pervasives_Native.None
               FStar_Syntax_Embeddings.id_norm_cb
              in
           ((let uu____4211 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____4211
             then
               let uu____4216 = FStar_Syntax_Print.term_to_string t0  in
               let uu____4218 = FStar_Syntax_Print.term_to_string tv  in
               FStar_Util.print2 ">> Inspected (%s) ~> (%s)\n" uu____4216
                 uu____4218
             else ());
            (let t1 =
               let uu____4226 =
                 let uu____4237 = FStar_Syntax_Syntax.as_arg tv  in
                 [uu____4237]  in
               FStar_Syntax_Util.mk_app
                 (FStar_Reflection_Data.refl_constant_term
                    FStar_Reflection_Data.fstar_refl_pack_ln) uu____4226
                in
             encode_term t1 env))
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_pattern uu____4263) ->
           encode_term t1
             (let uu___54_4281 = env  in
              {
                FStar_SMTEncoding_Env.bvar_bindings =
                  (uu___54_4281.FStar_SMTEncoding_Env.bvar_bindings);
                FStar_SMTEncoding_Env.fvar_bindings =
                  (uu___54_4281.FStar_SMTEncoding_Env.fvar_bindings);
                FStar_SMTEncoding_Env.depth =
                  (uu___54_4281.FStar_SMTEncoding_Env.depth);
                FStar_SMTEncoding_Env.tcenv =
                  (uu___54_4281.FStar_SMTEncoding_Env.tcenv);
                FStar_SMTEncoding_Env.warn =
                  (uu___54_4281.FStar_SMTEncoding_Env.warn);
                FStar_SMTEncoding_Env.nolabels =
                  (uu___54_4281.FStar_SMTEncoding_Env.nolabels);
                FStar_SMTEncoding_Env.use_zfuel_name =
                  (uu___54_4281.FStar_SMTEncoding_Env.use_zfuel_name);
                FStar_SMTEncoding_Env.encode_non_total_function_typ =
                  (uu___54_4281.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                FStar_SMTEncoding_Env.current_module_name =
                  (uu___54_4281.FStar_SMTEncoding_Env.current_module_name);
                FStar_SMTEncoding_Env.encoding_quantifier = false;
                FStar_SMTEncoding_Env.global_cache =
                  (uu___54_4281.FStar_SMTEncoding_Env.global_cache)
              })
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____4284) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = FStar_SMTEncoding_Env.lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____4292 = head_redex env t  in
           if uu____4292
           then let uu____4299 = whnf env t  in encode_term uu____4299 env
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
              let uu____4306 =
                if
                  fvb.FStar_SMTEncoding_Env.smt_arity > (Prims.parse_int "0")
                then
                  match tok.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.FreeV uu____4330 ->
                      let sym_name =
                        let uu____4341 =
                          FStar_Util.digest_of_string tkey_hash  in
                        Prims.strcat "@kick_partial_app_" uu____4341  in
                      let uu____4344 =
                        let uu____4347 =
                          let uu____4348 =
                            let uu____4356 =
                              FStar_SMTEncoding_Term.kick_partial_app tok  in
                            (uu____4356,
                              (FStar_Pervasives_Native.Some
                                 "kick_partial_app"), sym_name)
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____4348  in
                        [uu____4347]  in
                      (uu____4344, sym_name)
                  | FStar_SMTEncoding_Term.App (uu____4363,[]) ->
                      let sym_name =
                        let uu____4368 =
                          FStar_Util.digest_of_string tkey_hash  in
                        Prims.strcat "@kick_partial_app_" uu____4368  in
                      let uu____4371 =
                        let uu____4374 =
                          let uu____4375 =
                            let uu____4383 =
                              FStar_SMTEncoding_Term.kick_partial_app tok  in
                            (uu____4383,
                              (FStar_Pervasives_Native.Some
                                 "kick_partial_app"), sym_name)
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____4375  in
                        [uu____4374]  in
                      (uu____4371, sym_name)
                  | uu____4390 -> ([], "")
                else ([], "")  in
              match uu____4306 with
              | (aux_decls,sym_name) ->
                  let uu____4413 =
                    if aux_decls = []
                    then
                      FStar_All.pipe_right []
                        FStar_SMTEncoding_Term.mk_decls_trivial
                    else
                      FStar_SMTEncoding_Term.mk_decls sym_name tkey_hash
                        aux_decls []
                     in
                  (tok, uu____4413))
       | FStar_Syntax_Syntax.Tm_type uu____4421 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4423) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.FStar_SMTEncoding_Env.current_module_name
              in
           let uu____4453 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____4453 with
            | (binders1,res) ->
                let uu____4464 =
                  (env.FStar_SMTEncoding_Env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____4464
                then
                  let uu____4471 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____4471 with
                   | (vars,guards,env',decls,uu____4496) ->
                       let fsym =
                         let uu____4510 =
                           let uu____4516 =
                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                               "f"
                              in
                           (uu____4516, FStar_SMTEncoding_Term.Term_sort)  in
                         FStar_SMTEncoding_Term.mk_fv uu____4510  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____4522 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___55_4531 =
                              env.FStar_SMTEncoding_Env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___55_4531.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___55_4531.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___55_4531.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___55_4531.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___55_4531.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___55_4531.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___55_4531.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___55_4531.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___55_4531.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___55_4531.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___55_4531.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___55_4531.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___55_4531.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___55_4531.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___55_4531.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___55_4531.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___55_4531.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___55_4531.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___55_4531.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___55_4531.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___55_4531.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___55_4531.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___55_4531.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___55_4531.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___55_4531.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___55_4531.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___55_4531.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___55_4531.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___55_4531.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___55_4531.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___55_4531.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___55_4531.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___55_4531.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___55_4531.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___55_4531.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___55_4531.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___55_4531.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___55_4531.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___55_4531.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___55_4531.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___55_4531.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___55_4531.FStar_TypeChecker_Env.nbe)
                            }) res
                          in
                       (match uu____4522 with
                        | (pre_opt,res_t) ->
                            let uu____4543 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____4543 with
                             | (res_pred,decls') ->
                                 let uu____4554 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____4567 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____4567, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____4571 =
                                         encode_formula pre env'  in
                                       (match uu____4571 with
                                        | (guard,decls0) ->
                                            let uu____4584 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____4584, decls0))
                                    in
                                 (match uu____4554 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____4598 =
                                          let uu____4609 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____4609)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t.FStar_Syntax_Syntax.pos
                                          uu____4598
                                         in
                                      let cvars =
                                        let uu____4629 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____4629
                                          (FStar_List.filter
                                             (fun x  ->
                                                let uu____4648 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    x
                                                   in
                                                let uu____4650 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    fsym
                                                   in
                                                uu____4648 <> uu____4650))
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
                                        let uu____4672 =
                                          FStar_Util.digest_of_string
                                            tkey_hash
                                           in
                                        Prims.strcat "Tm_arrow_" uu____4672
                                         in
                                      let cvar_sorts =
                                        FStar_List.map
                                          FStar_SMTEncoding_Term.fv_sort
                                          cvars
                                         in
                                      let caption =
                                        let uu____4687 =
                                          FStar_Options.log_queries ()  in
                                        if uu____4687
                                        then
                                          let uu____4690 =
                                            let uu____4692 =
                                              FStar_TypeChecker_Normalize.term_to_string
                                                env.FStar_SMTEncoding_Env.tcenv
                                                t0
                                               in
                                            FStar_Util.replace_char
                                              uu____4692 10 32
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____4690
                                        else FStar_Pervasives_Native.None  in
                                      let tdecl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (tsym, cvar_sorts,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            caption)
                                         in
                                      let t1 =
                                        let uu____4705 =
                                          let uu____4713 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              cvars
                                             in
                                          (tsym, uu____4713)  in
                                        FStar_SMTEncoding_Util.mkApp
                                          uu____4705
                                         in
                                      let t_has_kind =
                                        FStar_SMTEncoding_Term.mk_HasType t1
                                          FStar_SMTEncoding_Term.mk_Term_type
                                         in
                                      let k_assumption =
                                        let a_name =
                                          Prims.strcat "kinding_" tsym  in
                                        let uu____4732 =
                                          let uu____4740 =
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              ([[t_has_kind]], cvars,
                                                t_has_kind)
                                             in
                                          (uu____4740,
                                            (FStar_Pervasives_Native.Some
                                               a_name), a_name)
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____4732
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
                                          Prims.strcat "pre_typing_" tsym  in
                                        let uu____4757 =
                                          let uu____4765 =
                                            let uu____4766 =
                                              let uu____4777 =
                                                let uu____4778 =
                                                  let uu____4783 =
                                                    let uu____4784 =
                                                      FStar_SMTEncoding_Term.mk_PreType
                                                        f
                                                       in
                                                    FStar_SMTEncoding_Term.mk_tester
                                                      "Tm_arrow" uu____4784
                                                     in
                                                  (f_has_t, uu____4783)  in
                                                FStar_SMTEncoding_Util.mkImp
                                                  uu____4778
                                                 in
                                              ([[f_has_t]], (fsym :: cvars),
                                                uu____4777)
                                               in
                                            let uu____4802 =
                                              mkForall_fuel
                                                t0.FStar_Syntax_Syntax.pos
                                               in
                                            uu____4802 uu____4766  in
                                          (uu____4765,
                                            (FStar_Pervasives_Native.Some
                                               "pre-typing for functions"),
                                            (Prims.strcat module_name
                                               (Prims.strcat "_" a_name)))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____4757
                                         in
                                      let t_interp1 =
                                        let a_name =
                                          Prims.strcat "interpretation_" tsym
                                           in
                                        let uu____4825 =
                                          let uu____4833 =
                                            let uu____4834 =
                                              let uu____4845 =
                                                FStar_SMTEncoding_Util.mkIff
                                                  (f_has_t_z, t_interp)
                                                 in
                                              ([[f_has_t_z]], (fsym ::
                                                cvars), uu____4845)
                                               in
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              uu____4834
                                             in
                                          (uu____4833,
                                            (FStar_Pervasives_Native.Some
                                               a_name),
                                            (Prims.strcat module_name
                                               (Prims.strcat "_" a_name)))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____4825
                                         in
                                      let t_decls1 =
                                        [tdecl;
                                        k_assumption;
                                        pre_typing;
                                        t_interp1]  in
                                      let uu____4868 =
                                        let uu____4869 =
                                          let uu____4872 =
                                            let uu____4875 =
                                              FStar_SMTEncoding_Term.mk_decls
                                                tsym tkey_hash t_decls1
                                                (FStar_List.append decls
                                                   (FStar_List.append decls'
                                                      guard_decls))
                                               in
                                            FStar_List.append guard_decls
                                              uu____4875
                                             in
                                          FStar_List.append decls' uu____4872
                                           in
                                        FStar_List.append decls uu____4869
                                         in
                                      (t1, uu____4868)))))
                else
                  (let tsym =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                       (Prims.strcat module_name "_Non_total_Tm_arrow")
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
                     let uu____4896 =
                       let uu____4904 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____4904,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____4896  in
                   let fsym =
                     FStar_SMTEncoding_Term.mk_fv
                       ("f", FStar_SMTEncoding_Term.Term_sort)
                      in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym  in
                     let uu____4918 =
                       let uu____4926 =
                         let uu____4927 =
                           let uu____4938 =
                             let uu____4939 =
                               let uu____4944 =
                                 let uu____4945 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____4945
                                  in
                               (f_has_t, uu____4944)  in
                             FStar_SMTEncoding_Util.mkImp uu____4939  in
                           ([[f_has_t]], [fsym], uu____4938)  in
                         let uu____4971 =
                           mkForall_fuel t0.FStar_Syntax_Syntax.pos  in
                         uu____4971 uu____4927  in
                       (uu____4926, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____4918  in
                   let uu____4989 =
                     FStar_All.pipe_right [tdecl; t_kinding; t_interp]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                      in
                   (t1, uu____4989)))
       | FStar_Syntax_Syntax.Tm_refine uu____4992 ->
           let uu____4999 =
             let uu____5004 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Env.Weak;
                 FStar_TypeChecker_Env.HNF;
                 FStar_TypeChecker_Env.EraseUniverses]
                 env.FStar_SMTEncoding_Env.tcenv t0
                in
             match uu____5004 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____5011;
                 FStar_Syntax_Syntax.vars = uu____5012;_} ->
                 let uu____5019 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____5019 with
                  | (b,f1) ->
                      let uu____5044 =
                        let uu____5045 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____5045  in
                      (uu____5044, f1))
             | uu____5060 -> failwith "impossible"  in
           (match uu____4999 with
            | (x,f) ->
                let uu____5072 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____5072 with
                 | (base_t,decls) ->
                     let uu____5083 =
                       FStar_SMTEncoding_Env.gen_term_var env x  in
                     (match uu____5083 with
                      | (x1,xtm,env') ->
                          let uu____5100 = encode_formula f env'  in
                          (match uu____5100 with
                           | (refinement,decls') ->
                               let uu____5111 =
                                 FStar_SMTEncoding_Env.fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____5111 with
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
                                      let uu____5139 =
                                        let uu____5150 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____5161 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____5150
                                          uu____5161
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____5139
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun y  ->
                                              (let uu____5215 =
                                                 FStar_SMTEncoding_Term.fv_name
                                                   y
                                                  in
                                               uu____5215 <> x1) &&
                                                (let uu____5219 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     y
                                                    in
                                                 uu____5219 <> fsym)))
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
                                      let uu____5255 =
                                        FStar_Util.digest_of_string tkey_hash
                                         in
                                      Prims.strcat "Tm_refine_" uu____5255
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
                                      let uu____5275 =
                                        let uu____5283 =
                                          FStar_List.map
                                            FStar_SMTEncoding_Util.mkFreeV
                                            cvars1
                                           in
                                        (tsym, uu____5283)  in
                                      FStar_SMTEncoding_Util.mkApp uu____5275
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
                                      let uu____5303 =
                                        let uu____5311 =
                                          let uu____5312 =
                                            let uu____5323 =
                                              FStar_SMTEncoding_Util.mkIff
                                                (t_haseq_ref, t_haseq_base)
                                               in
                                            ([[t_haseq_ref]], cvars1,
                                              uu____5323)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            t0.FStar_Syntax_Syntax.pos
                                            uu____5312
                                           in
                                        (uu____5311,
                                          (FStar_Pervasives_Native.Some
                                             (Prims.strcat "haseq for " tsym)),
                                          (Prims.strcat "haseq" tsym))
                                         in
                                      FStar_SMTEncoding_Util.mkAssume
                                        uu____5303
                                       in
                                    let t_kinding =
                                      let uu____5337 =
                                        let uu____5345 =
                                          FStar_SMTEncoding_Term.mkForall
                                            t0.FStar_Syntax_Syntax.pos
                                            ([[t_has_kind]], cvars1,
                                              t_has_kind)
                                           in
                                        (uu____5345,
                                          (FStar_Pervasives_Native.Some
                                             "refinement kinding"),
                                          (Prims.strcat "refinement_kinding_"
                                             tsym))
                                         in
                                      FStar_SMTEncoding_Util.mkAssume
                                        uu____5337
                                       in
                                    let t_interp =
                                      let uu____5359 =
                                        let uu____5367 =
                                          let uu____5368 =
                                            let uu____5379 =
                                              FStar_SMTEncoding_Util.mkIff
                                                (x_has_t, encoding)
                                               in
                                            ([[x_has_t]], (ffv :: xfv ::
                                              cvars1), uu____5379)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            t0.FStar_Syntax_Syntax.pos
                                            uu____5368
                                           in
                                        (uu____5367,
                                          (FStar_Pervasives_Native.Some
                                             "refinement_interpretation"),
                                          (Prims.strcat
                                             "refinement_interpretation_"
                                             tsym))
                                         in
                                      FStar_SMTEncoding_Util.mkAssume
                                        uu____5359
                                       in
                                    let t_decls1 =
                                      [tdecl; t_kinding; t_interp; t_haseq1]
                                       in
                                    let uu____5411 =
                                      let uu____5412 =
                                        let uu____5415 =
                                          FStar_SMTEncoding_Term.mk_decls
                                            tsym tkey_hash t_decls1
                                            (FStar_List.append decls decls')
                                           in
                                        FStar_List.append decls' uu____5415
                                         in
                                      FStar_List.append decls uu____5412  in
                                    (t1, uu____5411))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,uu____5419) ->
           let ttm =
             let uu____5437 =
               FStar_Syntax_Unionfind.uvar_id
                 uv.FStar_Syntax_Syntax.ctx_uvar_head
                in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____5437  in
           let uu____5439 =
             encode_term_pred FStar_Pervasives_Native.None
               uv.FStar_Syntax_Syntax.ctx_uvar_typ env ttm
              in
           (match uu____5439 with
            | (t_has_k,decls) ->
                let d =
                  let uu____5451 =
                    let uu____5459 =
                      let uu____5461 =
                        let uu____5463 =
                          let uu____5465 =
                            FStar_Syntax_Unionfind.uvar_id
                              uv.FStar_Syntax_Syntax.ctx_uvar_head
                             in
                          FStar_Util.string_of_int uu____5465  in
                        FStar_Util.format1 "uvar_typing_%s" uu____5463  in
                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                        uu____5461
                       in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____5459)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____5451  in
                let uu____5471 =
                  let uu____5472 =
                    FStar_All.pipe_right [d]
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append decls uu____5472  in
                (ttm, uu____5471))
       | FStar_Syntax_Syntax.Tm_app uu____5479 ->
           let uu____5496 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____5496 with
            | (head1,args_e) ->
                let uu____5543 =
                  let uu____5558 =
                    let uu____5559 = FStar_Syntax_Subst.compress head1  in
                    uu____5559.FStar_Syntax_Syntax.n  in
                  (uu____5558, args_e)  in
                (match uu____5543 with
                 | uu____5576 when head_redex env head1 ->
                     let uu____5591 = whnf env t  in
                     encode_term uu____5591 env
                 | uu____5592 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____5615 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5633) when
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
                       FStar_Syntax_Syntax.pos = uu____5655;
                       FStar_Syntax_Syntax.vars = uu____5656;_},uu____5657),uu____5658)
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
                       FStar_Syntax_Syntax.pos = uu____5684;
                       FStar_Syntax_Syntax.vars = uu____5685;_},uu____5686),
                    (v0,uu____5688)::(v1,uu____5690)::(v2,uu____5692)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____5763 = encode_term v0 env  in
                     (match uu____5763 with
                      | (v01,decls0) ->
                          let uu____5774 = encode_term v1 env  in
                          (match uu____5774 with
                           | (v11,decls1) ->
                               let uu____5785 = encode_term v2 env  in
                               (match uu____5785 with
                                | (v21,decls2) ->
                                    let uu____5796 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____5796,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(v0,uu____5799)::(v1,uu____5801)::(v2,uu____5803)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____5870 = encode_term v0 env  in
                     (match uu____5870 with
                      | (v01,decls0) ->
                          let uu____5881 = encode_term v1 env  in
                          (match uu____5881 with
                           | (v11,decls1) ->
                               let uu____5892 = encode_term v2 env  in
                               (match uu____5892 with
                                | (v21,decls2) ->
                                    let uu____5903 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____5903,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____5905)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____5941)::(rng,uu____5943)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____5994) ->
                     let e0 =
                       let uu____6016 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg
                         env.FStar_SMTEncoding_Env.tcenv head1 uu____6016
                        in
                     ((let uu____6026 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug
                              env.FStar_SMTEncoding_Env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____6026
                       then
                         let uu____6031 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____6031
                       else ());
                      (let e =
                         let uu____6039 =
                           let uu____6044 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____6045 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____6044
                             uu____6045
                            in
                         uu____6039 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____6056),(arg,uu____6058)::[]) -> encode_term arg env
                 | uu____6093 ->
                     let uu____6108 = encode_args args_e env  in
                     (match uu____6108 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____6169 = encode_term head1 env  in
                            match uu____6169 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____6241 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____6241 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____6339  ->
                                                 fun uu____6340  ->
                                                   match (uu____6339,
                                                           uu____6340)
                                                   with
                                                   | ((bv,uu____6370),
                                                      (a,uu____6372)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____6402 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____6402
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____6403 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm
                                             in
                                          (match uu____6403 with
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
                                                 let uu____6420 =
                                                   let uu____6428 =
                                                     FStar_SMTEncoding_Term.mkForall
                                                       t0.FStar_Syntax_Syntax.pos
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____6437 =
                                                     let uu____6439 =
                                                       let uu____6441 =
                                                         FStar_SMTEncoding_Term.hash_of_term
                                                           app_tm
                                                          in
                                                       FStar_Util.digest_of_string
                                                         uu____6441
                                                        in
                                                     Prims.strcat
                                                       "partial_app_typing_"
                                                       uu____6439
                                                      in
                                                   (uu____6428,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____6437)
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____6420
                                                  in
                                               let uu____6447 =
                                                 let uu____6450 =
                                                   let uu____6453 =
                                                     let uu____6456 =
                                                       FStar_SMTEncoding_Term.mk_decls
                                                         "" tkey_hash
                                                         [e_typing]
                                                         (FStar_List.append
                                                            decls
                                                            (FStar_List.append
                                                               decls' decls''))
                                                        in
                                                     FStar_List.append
                                                       decls'' uu____6456
                                                      in
                                                   FStar_List.append decls'
                                                     uu____6453
                                                    in
                                                 FStar_List.append decls
                                                   uu____6450
                                                  in
                                               (app_tm, uu____6447))))
                             in
                          let encode_full_app fv =
                            let uu____6476 =
                              FStar_SMTEncoding_Env.lookup_free_var_sym env
                                fv
                               in
                            match uu____6476 with
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
                                   FStar_Syntax_Syntax.pos = uu____6519;
                                   FStar_Syntax_Syntax.vars = uu____6520;_},uu____6521)
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
                                   FStar_Syntax_Syntax.pos = uu____6528;
                                   FStar_Syntax_Syntax.vars = uu____6529;_},uu____6530)
                                ->
                                let uu____6535 =
                                  let uu____6536 =
                                    let uu____6541 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____6541
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____6536
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____6535
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____6571 =
                                  let uu____6572 =
                                    let uu____6577 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____6577
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____6572
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____6571
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____6606,(FStar_Util.Inl t1,uu____6608),uu____6609)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____6656,(FStar_Util.Inr c,uu____6658),uu____6659)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____6706 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____6727 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Env.Weak;
                                     FStar_TypeChecker_Env.HNF;
                                     FStar_TypeChecker_Env.EraseUniverses]
                                     env.FStar_SMTEncoding_Env.tcenv
                                     head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____6727
                                  in
                               let uu____6728 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____6728 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____6744;
                                            FStar_Syntax_Syntax.vars =
                                              uu____6745;_},uu____6746)
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
                                     | uu____6764 ->
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
           let uu____6843 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____6843 with
            | (bs1,body1,opening) ->
                let fallback uu____6866 =
                  let f =
                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                      (Prims.strcat
                         env.FStar_SMTEncoding_Env.current_module_name
                         "_Tm_abs")
                     in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding"))
                     in
                  let uu____6876 =
                    let uu____6877 =
                      FStar_SMTEncoding_Term.mk_fv
                        (f, FStar_SMTEncoding_Term.Term_sort)
                       in
                    FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV
                      uu____6877
                     in
                  let uu____6879 =
                    FStar_All.pipe_right [decl]
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  (uu____6876, uu____6879)  in
                let is_impure rc =
                  let uu____6889 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                      env.FStar_SMTEncoding_Env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____6889 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____6904 =
                          let uu____6917 =
                            FStar_TypeChecker_Env.get_range
                              env.FStar_SMTEncoding_Env.tcenv
                             in
                          FStar_TypeChecker_Util.new_implicit_var
                            "SMTEncoding codomain" uu____6917
                            env.FStar_SMTEncoding_Env.tcenv
                            FStar_Syntax_Util.ktype0
                           in
                        (match uu____6904 with
                         | (t1,uu____6920,uu____6921) -> t1)
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  let uu____6939 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                     in
                  if uu____6939
                  then
                    let uu____6944 = FStar_Syntax_Syntax.mk_Total res_typ  in
                    FStar_Pervasives_Native.Some uu____6944
                  else
                    (let uu____6947 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid
                        in
                     if uu____6947
                     then
                       let uu____6952 = FStar_Syntax_Syntax.mk_GTotal res_typ
                          in
                       FStar_Pervasives_Native.Some uu____6952
                     else FStar_Pervasives_Native.None)
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____6960 =
                         let uu____6966 =
                           let uu____6968 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____6968
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____6966)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____6960);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____6973 =
                       (is_impure rc) &&
                         (let uu____6976 =
                            FStar_TypeChecker_Env.is_reifiable_rc
                              env.FStar_SMTEncoding_Env.tcenv rc
                             in
                          Prims.op_Negation uu____6976)
                        in
                     if uu____6973
                     then fallback ()
                     else
                       (let uu____6985 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____6985 with
                        | (vars,guards,envbody,decls,uu____7010) ->
                            let body2 =
                              let uu____7024 =
                                FStar_TypeChecker_Env.is_reifiable_rc
                                  env.FStar_SMTEncoding_Env.tcenv rc
                                 in
                              if uu____7024
                              then
                                FStar_TypeChecker_Util.reify_body
                                  env.FStar_SMTEncoding_Env.tcenv body1
                              else body1  in
                            let uu____7029 = encode_term body2 envbody  in
                            (match uu____7029 with
                             | (body3,decls') ->
                                 let uu____7040 =
                                   let uu____7049 = codomain_eff rc  in
                                   match uu____7049 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____7068 = encode_term tfun env
                                          in
                                       (match uu____7068 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____7040 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____7102 =
                                          let uu____7113 =
                                            let uu____7114 =
                                              let uu____7119 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____7119, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____7114
                                             in
                                          ([], vars, uu____7113)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t0.FStar_Syntax_Syntax.pos
                                          uu____7102
                                         in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body
                                         in
                                      let uu____7127 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            (cvars, key_body)
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____7143 =
                                              let uu____7146 =
                                                let uu____7157 =
                                                  FStar_SMTEncoding_Term.free_variables
                                                    t1
                                                   in
                                                FStar_List.append uu____7157
                                                  cvars
                                                 in
                                              FStar_Util.remove_dups
                                                FStar_SMTEncoding_Term.fv_eq
                                                uu____7146
                                               in
                                            let uu____7184 =
                                              FStar_SMTEncoding_Util.mkAnd
                                                (key_body, t1)
                                               in
                                            (uu____7143, uu____7184)
                                         in
                                      (match uu____7127 with
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
                                           let uu____7206 =
                                             is_an_eta_expansion env vars
                                               body3
                                              in
                                           (match uu____7206 with
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
                                                  let uu____7222 =
                                                    FStar_Util.digest_of_string
                                                      tkey_hash
                                                     in
                                                  Prims.strcat "Tm_abs_"
                                                    uu____7222
                                                   in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None)
                                                   in
                                                let f =
                                                  let uu____7231 =
                                                    let uu____7239 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    (fsym, uu____7239)  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____7231
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
                                                      let uu____7256 =
                                                        let uu____7257 =
                                                          let uu____7265 =
                                                            FStar_SMTEncoding_Term.mkForall
                                                              t0.FStar_Syntax_Syntax.pos
                                                              ([[f]], cvars1,
                                                                f_has_t)
                                                             in
                                                          (uu____7265,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name)
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____7257
                                                         in
                                                      [uu____7256]
                                                   in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym
                                                     in
                                                  let uu____7280 =
                                                    let uu____7288 =
                                                      let uu____7289 =
                                                        let uu____7300 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3)
                                                           in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____7300)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        t0.FStar_Syntax_Syntax.pos
                                                        uu____7289
                                                       in
                                                    (uu____7288,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____7280
                                                   in
                                                let f_decls =
                                                  FStar_List.append (fdecl ::
                                                    typing_f) [interp_f]
                                                   in
                                                let uu____7314 =
                                                  let uu____7315 =
                                                    let uu____7318 =
                                                      let uu____7321 =
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
                                                        decls'' uu____7321
                                                       in
                                                    FStar_List.append decls'
                                                      uu____7318
                                                     in
                                                  FStar_List.append decls
                                                    uu____7315
                                                   in
                                                (f, uu____7314))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____7324,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____7325;
                          FStar_Syntax_Syntax.lbunivs = uu____7326;
                          FStar_Syntax_Syntax.lbtyp = uu____7327;
                          FStar_Syntax_Syntax.lbeff = uu____7328;
                          FStar_Syntax_Syntax.lbdef = uu____7329;
                          FStar_Syntax_Syntax.lbattrs = uu____7330;
                          FStar_Syntax_Syntax.lbpos = uu____7331;_}::uu____7332),uu____7333)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____7367;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____7369;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____7371;
                FStar_Syntax_Syntax.lbpos = uu____7372;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____7399 ->
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
              let uu____7471 =
                let uu____7476 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____7476 env  in
              match uu____7471 with
              | (ee1,decls1) ->
                  let uu____7501 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____7501 with
                   | (xs,e21) ->
                       let uu____7526 = FStar_List.hd xs  in
                       (match uu____7526 with
                        | (x1,uu____7544) ->
                            let env' =
                              FStar_SMTEncoding_Env.push_term_var env x1 ee1
                               in
                            let uu____7550 = encode_body e21 env'  in
                            (match uu____7550 with
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
            let uu____7580 =
              let uu____7588 =
                let uu____7589 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____7589  in
              FStar_SMTEncoding_Env.gen_term_var env uu____7588  in
            match uu____7580 with
            | (scrsym,scr',env1) ->
                let uu____7599 = encode_term e env1  in
                (match uu____7599 with
                 | (scr,decls) ->
                     let uu____7610 =
                       let encode_branch b uu____7639 =
                         match uu____7639 with
                         | (else_case,decls1) ->
                             let uu____7658 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____7658 with
                              | (p,w,br) ->
                                  let uu____7684 = encode_pat env1 p  in
                                  (match uu____7684 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____7721  ->
                                                   match uu____7721 with
                                                   | (x,t) ->
                                                       FStar_SMTEncoding_Env.push_term_var
                                                         env2 x t) env1)
                                          in
                                       let uu____7728 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____7750 =
                                               encode_term w1 env2  in
                                             (match uu____7750 with
                                              | (w2,decls2) ->
                                                  let uu____7763 =
                                                    let uu____7764 =
                                                      let uu____7769 =
                                                        let uu____7770 =
                                                          let uu____7775 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____7775)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____7770
                                                         in
                                                      (guard, uu____7769)  in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____7764
                                                     in
                                                  (uu____7763, decls2))
                                          in
                                       (match uu____7728 with
                                        | (guard1,decls2) ->
                                            let uu____7790 =
                                              encode_br br env2  in
                                            (match uu____7790 with
                                             | (br1,decls3) ->
                                                 let uu____7803 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____7803,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____7610 with
                      | (match_tm,decls1) ->
                          let uu____7824 =
                            let uu____7825 =
                              let uu____7836 =
                                let uu____7843 =
                                  let uu____7848 =
                                    FStar_SMTEncoding_Term.mk_fv
                                      (scrsym,
                                        FStar_SMTEncoding_Term.Term_sort)
                                     in
                                  (uu____7848, scr)  in
                                [uu____7843]  in
                              (uu____7836, match_tm)  in
                            FStar_SMTEncoding_Term.mkLet' uu____7825
                              FStar_Range.dummyRange
                             in
                          (uu____7824, decls1)))

and (encode_pat :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.pat -> (FStar_SMTEncoding_Env.env_t * pattern))
  =
  fun env  ->
    fun pat  ->
      (let uu____7871 =
         FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
           FStar_Options.Medium
          in
       if uu____7871
       then
         let uu____7874 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____7874
       else ());
      (let uu____7879 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____7879 with
       | (vars,pat_term) ->
           let uu____7896 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____7938  ->
                     fun v1  ->
                       match uu____7938 with
                       | (env1,vars1) ->
                           let uu____7974 =
                             FStar_SMTEncoding_Env.gen_term_var env1 v1  in
                           (match uu____7974 with
                            | (xx,uu____7993,env2) ->
                                let uu____7997 =
                                  let uu____8004 =
                                    let uu____8009 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xx,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    (v1, uu____8009)  in
                                  uu____8004 :: vars1  in
                                (env2, uu____7997))) (env, []))
              in
           (match uu____7896 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____8064 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____8065 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____8066 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____8074 = encode_const c env1  in
                      (match uu____8074 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____8082::uu____8083 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____8087 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon
                            env1.FStar_SMTEncoding_Env.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____8110 =
                          FStar_TypeChecker_Env.datacons_of_typ
                            env1.FStar_SMTEncoding_Env.tcenv tc_name
                           in
                        match uu____8110 with
                        | (uu____8118,uu____8119::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____8124 ->
                            FStar_SMTEncoding_Env.mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____8160  ->
                                  match uu____8160 with
                                  | (arg,uu____8170) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____8179 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____8179))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____8211) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____8242 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____8267 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____8313  ->
                                  match uu____8313 with
                                  | (arg,uu____8329) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____8338 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____8338))
                         in
                      FStar_All.pipe_right uu____8267 FStar_List.flatten
                   in
                let pat_term1 uu____8369 = encode_term pat_term env1  in
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
      let uu____8379 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____8427  ->
                fun uu____8428  ->
                  match (uu____8427, uu____8428) with
                  | ((tms,decls),(t,uu____8468)) ->
                      let uu____8495 = encode_term t env  in
                      (match uu____8495 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____8379 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____8552 = FStar_Syntax_Util.list_elements e  in
        match uu____8552 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____8583 =
          let uu____8600 = FStar_Syntax_Util.unmeta p  in
          FStar_All.pipe_right uu____8600 FStar_Syntax_Util.head_and_args  in
        match uu____8583 with
        | (head1,args) ->
            let uu____8651 =
              let uu____8666 =
                let uu____8667 = FStar_Syntax_Util.un_uinst head1  in
                uu____8667.FStar_Syntax_Syntax.n  in
              (uu____8666, args)  in
            (match uu____8651 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____8689,uu____8690)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____8742 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or1 t1 =
          let uu____8797 =
            let uu____8814 = FStar_Syntax_Util.unmeta t1  in
            FStar_All.pipe_right uu____8814 FStar_Syntax_Util.head_and_args
             in
          match uu____8797 with
          | (head1,args) ->
              let uu____8861 =
                let uu____8876 =
                  let uu____8877 = FStar_Syntax_Util.un_uinst head1  in
                  uu____8877.FStar_Syntax_Syntax.n  in
                (uu____8876, args)  in
              (match uu____8861 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____8896)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____8933 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____8963 = smt_pat_or1 t1  in
            (match uu____8963 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____8985 = list_elements1 e  in
                 FStar_All.pipe_right uu____8985
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____9015 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____9015
                           (FStar_List.map one_pat)))
             | uu____9038 ->
                 let uu____9043 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____9043])
        | uu____9094 ->
            let uu____9097 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____9097]
         in
      let uu____9148 =
        let uu____9163 =
          let uu____9164 = FStar_Syntax_Subst.compress t  in
          uu____9164.FStar_Syntax_Syntax.n  in
        match uu____9163 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____9203 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____9203 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____9238;
                        FStar_Syntax_Syntax.effect_name = uu____9239;
                        FStar_Syntax_Syntax.result_typ = uu____9240;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____9242)::(post,uu____9244)::(pats,uu____9246)::[];
                        FStar_Syntax_Syntax.flags = uu____9247;_}
                      ->
                      let uu____9308 = lemma_pats pats  in
                      (binders1, pre, post, uu____9308)
                  | uu____9319 -> failwith "impos"))
        | uu____9335 -> failwith "Impos"  in
      match uu____9148 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___56_9372 = env  in
            {
              FStar_SMTEncoding_Env.bvar_bindings =
                (uu___56_9372.FStar_SMTEncoding_Env.bvar_bindings);
              FStar_SMTEncoding_Env.fvar_bindings =
                (uu___56_9372.FStar_SMTEncoding_Env.fvar_bindings);
              FStar_SMTEncoding_Env.depth =
                (uu___56_9372.FStar_SMTEncoding_Env.depth);
              FStar_SMTEncoding_Env.tcenv =
                (uu___56_9372.FStar_SMTEncoding_Env.tcenv);
              FStar_SMTEncoding_Env.warn =
                (uu___56_9372.FStar_SMTEncoding_Env.warn);
              FStar_SMTEncoding_Env.nolabels =
                (uu___56_9372.FStar_SMTEncoding_Env.nolabels);
              FStar_SMTEncoding_Env.use_zfuel_name = true;
              FStar_SMTEncoding_Env.encode_non_total_function_typ =
                (uu___56_9372.FStar_SMTEncoding_Env.encode_non_total_function_typ);
              FStar_SMTEncoding_Env.current_module_name =
                (uu___56_9372.FStar_SMTEncoding_Env.current_module_name);
              FStar_SMTEncoding_Env.encoding_quantifier =
                (uu___56_9372.FStar_SMTEncoding_Env.encoding_quantifier);
              FStar_SMTEncoding_Env.global_cache =
                (uu___56_9372.FStar_SMTEncoding_Env.global_cache)
            }  in
          let uu____9374 =
            encode_binders FStar_Pervasives_Native.None binders env1  in
          (match uu____9374 with
           | (vars,guards,env2,decls,uu____9399) ->
               let uu____9412 = encode_smt_patterns patterns env2  in
               (match uu____9412 with
                | (pats,decls') ->
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
                    let env3 =
                      let uu___57_9439 = env2  in
                      {
                        FStar_SMTEncoding_Env.bvar_bindings =
                          (uu___57_9439.FStar_SMTEncoding_Env.bvar_bindings);
                        FStar_SMTEncoding_Env.fvar_bindings =
                          (uu___57_9439.FStar_SMTEncoding_Env.fvar_bindings);
                        FStar_SMTEncoding_Env.depth =
                          (uu___57_9439.FStar_SMTEncoding_Env.depth);
                        FStar_SMTEncoding_Env.tcenv =
                          (uu___57_9439.FStar_SMTEncoding_Env.tcenv);
                        FStar_SMTEncoding_Env.warn =
                          (uu___57_9439.FStar_SMTEncoding_Env.warn);
                        FStar_SMTEncoding_Env.nolabels = true;
                        FStar_SMTEncoding_Env.use_zfuel_name =
                          (uu___57_9439.FStar_SMTEncoding_Env.use_zfuel_name);
                        FStar_SMTEncoding_Env.encode_non_total_function_typ =
                          (uu___57_9439.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                        FStar_SMTEncoding_Env.current_module_name =
                          (uu___57_9439.FStar_SMTEncoding_Env.current_module_name);
                        FStar_SMTEncoding_Env.encoding_quantifier =
                          (uu___57_9439.FStar_SMTEncoding_Env.encoding_quantifier);
                        FStar_SMTEncoding_Env.global_cache =
                          (uu___57_9439.FStar_SMTEncoding_Env.global_cache)
                      }  in
                    let uu____9441 =
                      let uu____9446 = FStar_Syntax_Util.unmeta pre  in
                      encode_formula uu____9446 env3  in
                    (match uu____9441 with
                     | (pre1,decls'') ->
                         let uu____9453 =
                           let uu____9458 = FStar_Syntax_Util.unmeta post1
                              in
                           encode_formula uu____9458 env3  in
                         (match uu____9453 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append decls'
                                     (FStar_List.append decls'' decls'''))
                                 in
                              let uu____9468 =
                                let uu____9469 =
                                  let uu____9480 =
                                    let uu____9481 =
                                      let uu____9486 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards)
                                         in
                                      (uu____9486, post2)  in
                                    FStar_SMTEncoding_Util.mkImp uu____9481
                                     in
                                  (pats, vars, uu____9480)  in
                                FStar_SMTEncoding_Term.mkForall
                                  t.FStar_Syntax_Syntax.pos uu____9469
                                 in
                              (uu____9468, decls1)))))

and (encode_smt_patterns :
  FStar_Syntax_Syntax.arg Prims.list Prims.list ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term Prims.list Prims.list *
        FStar_SMTEncoding_Term.decls_t))
  =
  fun pats_l  ->
    fun env  ->
      let env1 =
        let uu___58_9506 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___58_9506.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___58_9506.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___58_9506.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___58_9506.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___58_9506.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___58_9506.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___58_9506.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___58_9506.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___58_9506.FStar_SMTEncoding_Env.encoding_quantifier);
          FStar_SMTEncoding_Env.global_cache =
            (uu___58_9506.FStar_SMTEncoding_Env.global_cache)
        }  in
      let encode_smt_pattern t =
        let uu____9522 = FStar_Syntax_Util.head_and_args t  in
        match uu____9522 with
        | (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____9585::(x,uu____9587)::(t1,uu____9589)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____9656 = encode_term x env1  in
                 (match uu____9656 with
                  | (x1,decls) ->
                      let uu____9667 = encode_term t1 env1  in
                      (match uu____9667 with
                       | (t2,decls') ->
                           let uu____9678 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                           (uu____9678, (FStar_List.append decls decls'))))
             | uu____9679 -> encode_term t env1)
         in
      FStar_List.fold_right
        (fun pats  ->
           fun uu____9722  ->
             match uu____9722 with
             | (pats_l1,decls) ->
                 let uu____9767 =
                   FStar_List.fold_right
                     (fun uu____9802  ->
                        fun uu____9803  ->
                          match (uu____9802, uu____9803) with
                          | ((p,uu____9845),(pats1,decls1)) ->
                              let uu____9880 = encode_smt_pattern p  in
                              (match uu____9880 with
                               | (t,d) ->
                                   let uu____9895 =
                                     FStar_SMTEncoding_Term.check_pattern_ok
                                       t
                                      in
                                   (match uu____9895 with
                                    | FStar_Pervasives_Native.None  ->
                                        ((t :: pats1),
                                          (FStar_List.append d decls1))
                                    | FStar_Pervasives_Native.Some
                                        illegal_subterm ->
                                        ((let uu____9912 =
                                            let uu____9918 =
                                              let uu____9920 =
                                                FStar_Syntax_Print.term_to_string
                                                  p
                                                 in
                                              let uu____9922 =
                                                FStar_SMTEncoding_Term.print_smt_term
                                                  illegal_subterm
                                                 in
                                              FStar_Util.format2
                                                "Pattern %s contains illegal sub-term (%s); dropping it"
                                                uu____9920 uu____9922
                                               in
                                            (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                                              uu____9918)
                                             in
                                          FStar_Errors.log_issue
                                            p.FStar_Syntax_Syntax.pos
                                            uu____9912);
                                         (pats1,
                                           (FStar_List.append d decls1))))))
                     pats ([], decls)
                    in
                 (match uu____9767 with
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
        let uu____9982 =
          FStar_All.pipe_left
            (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____9982
        then
          let uu____9987 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____9989 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____9987 uu____9989
        else ()  in
      let enc f r l =
        let uu____10031 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10063 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____10063 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____10031 with
        | (decls,args) ->
            let uu____10094 =
              let uu___59_10095 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___59_10095.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___59_10095.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10094, decls)
         in
      let const_op f r uu____10130 =
        let uu____10143 = f r  in (uu____10143, [])  in
      let un_op f l =
        let uu____10166 = FStar_List.hd l  in
        FStar_All.pipe_left f uu____10166  in
      let bin_op f uu___50_10186 =
        match uu___50_10186 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10197 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____10238 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____10263  ->
                 match uu____10263 with
                 | (t,uu____10279) ->
                     let uu____10284 = encode_formula t env  in
                     (match uu____10284 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____10238 with
        | (decls,phis) ->
            let uu____10313 =
              let uu___60_10314 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___60_10314.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___60_10314.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10313, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____10377  ->
               match uu____10377 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____10398) -> false
                    | uu____10401 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____10420 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____10420
        else
          (let uu____10437 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____10437 r rf)
         in
      let eq3_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____10509 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::t1::v0::v1::[] ->
                     let uu____10541 =
                       let uu____10546 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____10547 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____10546, uu____10547)  in
                     FStar_SMTEncoding_Util.mkAnd uu____10541
                 | uu____10548 -> failwith "Impossible")
             in
          uu____10509 r args
        else
          (let uu____10554 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____10554)
         in
      let h_equals_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____10626 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::v0::t1::v1::[] ->
                     let uu____10658 =
                       let uu____10663 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____10664 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____10663, uu____10664)  in
                     FStar_SMTEncoding_Util.mkAnd uu____10658
                 | uu____10665 -> failwith "Impossible")
             in
          uu____10626 r args
        else
          (let uu____10671 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____10671)
         in
      let mk_imp1 r uu___51_10706 =
        match uu___51_10706 with
        | (lhs,uu____10712)::(rhs,uu____10714)::[] ->
            let uu____10755 = encode_formula rhs env  in
            (match uu____10755 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____10770) ->
                      (l1, decls1)
                  | uu____10775 ->
                      let uu____10776 = encode_formula lhs env  in
                      (match uu____10776 with
                       | (l2,decls2) ->
                           let uu____10787 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____10787, (FStar_List.append decls1 decls2)))))
        | uu____10788 -> failwith "impossible"  in
      let mk_ite r uu___52_10816 =
        match uu___52_10816 with
        | (guard,uu____10822)::(_then,uu____10824)::(_else,uu____10826)::[]
            ->
            let uu____10883 = encode_formula guard env  in
            (match uu____10883 with
             | (g,decls1) ->
                 let uu____10894 = encode_formula _then env  in
                 (match uu____10894 with
                  | (t,decls2) ->
                      let uu____10905 = encode_formula _else env  in
                      (match uu____10905 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____10917 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____10947 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l
           in
        f uu____10947  in
      let connectives =
        let uu____10977 =
          let uu____11002 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____11002)  in
        let uu____11045 =
          let uu____11072 =
            let uu____11097 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____11097)  in
          let uu____11140 =
            let uu____11167 =
              let uu____11194 =
                let uu____11219 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____11219)  in
              let uu____11262 =
                let uu____11289 =
                  let uu____11316 =
                    let uu____11341 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____11341)  in
                  [uu____11316;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.c_eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq3_op);
                  (FStar_Parser_Const.c_eq3_lid, h_equals_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11289  in
              uu____11194 :: uu____11262  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11167  in
          uu____11072 :: uu____11140  in
        uu____10977 :: uu____11045  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____11886 = encode_formula phi' env  in
            (match uu____11886 with
             | (phi2,decls) ->
                 let uu____11897 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____11897, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____11899 ->
            let uu____11906 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____11906 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____11945 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____11945 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____11957;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____11959;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____11961;
                 FStar_Syntax_Syntax.lbpos = uu____11962;_}::[]),e2)
            ->
            let uu____11989 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____11989 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____12042::(x,uu____12044)::(t,uu____12046)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12113 = encode_term x env  in
                 (match uu____12113 with
                  | (x1,decls) ->
                      let uu____12124 = encode_term t env  in
                      (match uu____12124 with
                       | (t1,decls') ->
                           let uu____12135 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____12135, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12138)::(msg,uu____12140)::(phi2,uu____12142)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12209 =
                   let uu____12214 =
                     let uu____12215 = FStar_Syntax_Subst.compress r  in
                     uu____12215.FStar_Syntax_Syntax.n  in
                   let uu____12218 =
                     let uu____12219 = FStar_Syntax_Subst.compress msg  in
                     uu____12219.FStar_Syntax_Syntax.n  in
                   (uu____12214, uu____12218)  in
                 (match uu____12209 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12228))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____12239 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____12246)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____12281 when head_redex env head2 ->
                 let uu____12296 = whnf env phi1  in
                 encode_formula uu____12296 env
             | uu____12297 ->
                 let uu____12312 = encode_term phi1 env  in
                 (match uu____12312 with
                  | (tt,decls) ->
                      let tt1 =
                        let uu____12324 =
                          let uu____12326 =
                            FStar_Range.use_range
                              tt.FStar_SMTEncoding_Term.rng
                             in
                          let uu____12327 =
                            FStar_Range.use_range
                              phi1.FStar_Syntax_Syntax.pos
                             in
                          FStar_Range.rng_included uu____12326 uu____12327
                           in
                        if uu____12324
                        then tt
                        else
                          (let uu___61_12331 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___61_12331.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___61_12331.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      let uu____12332 = FStar_SMTEncoding_Term.mk_Valid tt1
                         in
                      (uu____12332, decls)))
        | uu____12333 ->
            let uu____12334 = encode_term phi1 env  in
            (match uu____12334 with
             | (tt,decls) ->
                 let tt1 =
                   let uu____12346 =
                     let uu____12348 =
                       FStar_Range.use_range tt.FStar_SMTEncoding_Term.rng
                        in
                     let uu____12349 =
                       FStar_Range.use_range phi1.FStar_Syntax_Syntax.pos  in
                     FStar_Range.rng_included uu____12348 uu____12349  in
                   if uu____12346
                   then tt
                   else
                     (let uu___62_12353 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___62_12353.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___62_12353.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 let uu____12354 = FStar_SMTEncoding_Term.mk_Valid tt1  in
                 (uu____12354, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____12398 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____12398 with
        | (vars,guards,env2,decls,uu____12437) ->
            let uu____12450 = encode_smt_patterns ps env2  in
            (match uu____12450 with
             | (pats,decls') ->
                 let uu____12487 = encode_formula body env2  in
                 (match uu____12487 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12519;
                             FStar_SMTEncoding_Term.rng = uu____12520;_}::[])::[]
                            when
                            let uu____12540 =
                              FStar_Ident.text_of_lid
                                FStar_Parser_Const.guard_free
                               in
                            uu____12540 = gf -> []
                        | uu____12543 -> guards  in
                      let uu____12548 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____12548, body1,
                        (FStar_List.append decls
                           (FStar_List.append decls' decls'')))))
         in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi  in
       let uu____12559 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____12559 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12568 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____12674  ->
                     match uu____12674 with
                     | (l,uu____12699) -> FStar_Ident.lid_equals op l))
              in
           (match uu____12568 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____12768,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____12860 = encode_q_body env vars pats body  in
             match uu____12860 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____12905 =
                     let uu____12916 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____12916)  in
                   FStar_SMTEncoding_Term.mkForall
                     phi1.FStar_Syntax_Syntax.pos uu____12905
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____12947 = encode_q_body env vars pats body  in
             match uu____12947 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____12991 =
                   let uu____12992 =
                     let uu____13003 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____13003)  in
                   FStar_SMTEncoding_Term.mkExists
                     phi1.FStar_Syntax_Syntax.pos uu____12992
                    in
                 (uu____12991, decls))))
