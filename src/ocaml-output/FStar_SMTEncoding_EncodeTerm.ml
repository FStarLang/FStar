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
               (fun uu___359_382  ->
                  match uu___359_382 with
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
  fun uu___360_672  ->
    match uu___360_672 with
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
      | c1 ->
          let uu____2003 =
            let uu____2005 = FStar_Syntax_Print.const_to_string c1  in
            FStar_Util.format1 "Unhandled constant: %s" uu____2005  in
          failwith uu____2003

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
        (let uu____2034 =
           FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
             FStar_Options.Medium
            in
         if uu____2034
         then
           let uu____2037 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____2037
         else ());
        (let uu____2043 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2125  ->
                   fun b  ->
                     match uu____2125 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2190 =
                           let x = FStar_Pervasives_Native.fst b  in
                           let uu____2206 =
                             FStar_SMTEncoding_Env.gen_term_var env1 x  in
                           match uu____2206 with
                           | (xxsym,xx,env') ->
                               let uu____2231 =
                                 let uu____2236 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____2236 env1 xx
                                  in
                               (match uu____2231 with
                                | (guard_x_t,decls') ->
                                    let uu____2251 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xxsym,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    (uu____2251, guard_x_t, env', decls', x))
                            in
                         (match uu____2190 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____2043 with
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
          let uu____2351 = encode_term t env  in
          match uu____2351 with
          | (t1,decls) ->
              let uu____2362 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____2362, decls)

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
          let uu____2373 = encode_term t env  in
          match uu____2373 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____2388 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____2388, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____2390 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____2390, decls))

and (encode_arith_term :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____2396 = encode_args args_e env  in
        match uu____2396 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____2415 -> failwith "Impossible"  in
            let unary arg_tms1 =
              let uu____2427 = FStar_List.hd arg_tms1  in
              FStar_SMTEncoding_Term.unboxInt uu____2427  in
            let binary arg_tms1 =
              let uu____2442 =
                let uu____2443 = FStar_List.hd arg_tms1  in
                FStar_SMTEncoding_Term.unboxInt uu____2443  in
              let uu____2444 =
                let uu____2445 =
                  let uu____2446 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____2446  in
                FStar_SMTEncoding_Term.unboxInt uu____2445  in
              (uu____2442, uu____2444)  in
            let mk_default uu____2454 =
              let uu____2455 =
                FStar_SMTEncoding_Env.lookup_free_var_sym env
                  head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____2455 with
              | (fname,fuel_args,arity) ->
                  let args = FStar_List.append fuel_args arg_tms  in
                  maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity
                    args
               in
            let mk_l op mk_args ts =
              let uu____2532 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____2532
              then
                let uu____2535 =
                  let uu____2536 = mk_args ts  in op uu____2536  in
                FStar_All.pipe_right uu____2535 FStar_SMTEncoding_Term.boxInt
              else mk_default ()  in
            let mk_nl nm op ts =
              let uu____2574 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____2574
              then
                let uu____2577 = binary ts  in
                match uu____2577 with
                | (t1,t2) ->
                    let uu____2584 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____2584
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____2590 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____2590
                 then
                   let uu____2593 =
                     let uu____2594 = binary ts  in op uu____2594  in
                   FStar_All.pipe_right uu____2593
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
            let uu____2759 =
              let uu____2769 =
                FStar_List.tryFind
                  (fun uu____2793  ->
                     match uu____2793 with
                     | (l,uu____2804) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____2769 FStar_Util.must  in
            (match uu____2759 with
             | (uu____2848,op) ->
                 let uu____2860 = op arg_tms  in (uu____2860, decls))

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
        let uu____2868 = FStar_List.hd args_e  in
        match uu____2868 with
        | (tm_sz,uu____2876) ->
            let uu____2885 = uu____2868  in
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let uu____2894 =
                FStar_Util.smap_try_find env.FStar_SMTEncoding_Env.cache
                  sz_key
                 in
              match uu____2894 with
              | FStar_Pervasives_Native.Some cache_entry ->
                  FStar_SMTEncoding_Env.use_cache_entry cache_entry
              | FStar_Pervasives_Native.None  ->
                  let t_decls1 = FStar_SMTEncoding_Term.mkBvConstructor sz
                     in
                  ((let uu____2902 =
                      FStar_SMTEncoding_Env.mk_cache_entry env "" [] t_decls1
                       in
                    FStar_Util.smap_add env.FStar_SMTEncoding_Env.cache
                      sz_key uu____2902);
                   t_decls1)
               in
            let uu____2904 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____2930::(sz_arg,uu____2932)::uu____2933::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____3000 =
                    let uu____3001 = FStar_List.tail args_e  in
                    FStar_List.tail uu____3001  in
                  let uu____3004 =
                    let uu____3008 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____3008  in
                  (uu____3000, uu____3004)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____3015::(sz_arg,uu____3017)::uu____3018::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____3085 =
                    let uu____3087 = FStar_Syntax_Print.term_to_string sz_arg
                       in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____3087
                     in
                  failwith uu____3085
              | uu____3097 ->
                  let uu____3112 = FStar_List.tail args_e  in
                  (uu____3112, FStar_Pervasives_Native.None)
               in
            (match uu____2904 with
             | (arg_tms,ext_sz) ->
                 let uu____3131 = encode_args arg_tms env  in
                 (match uu____3131 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____3152 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____3164 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____3164  in
                      let unary_arith arg_tms2 =
                        let uu____3175 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____3175  in
                      let binary arg_tms2 =
                        let uu____3190 =
                          let uu____3191 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3191
                           in
                        let uu____3192 =
                          let uu____3193 =
                            let uu____3194 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____3194  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3193
                           in
                        (uu____3190, uu____3192)  in
                      let binary_arith arg_tms2 =
                        let uu____3211 =
                          let uu____3212 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3212
                           in
                        let uu____3213 =
                          let uu____3214 =
                            let uu____3215 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____3215  in
                          FStar_SMTEncoding_Term.unboxInt uu____3214  in
                        (uu____3211, uu____3213)  in
                      let mk_bv op mk_args resBox ts =
                        let uu____3273 =
                          let uu____3274 = mk_args ts  in op uu____3274  in
                        FStar_All.pipe_right uu____3273 resBox  in
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
                        let uu____3406 =
                          let uu____3411 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____3411  in
                        let uu____3420 =
                          let uu____3425 =
                            let uu____3427 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____3427  in
                          FStar_SMTEncoding_Term.boxBitVec uu____3425  in
                        mk_bv uu____3406 unary uu____3420 arg_tms2  in
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
                      let uu____3667 =
                        let uu____3677 =
                          FStar_List.tryFind
                            (fun uu____3701  ->
                               match uu____3701 with
                               | (l,uu____3712) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____3677 FStar_Util.must  in
                      (match uu____3667 with
                       | (uu____3758,op) ->
                           let uu____3770 = op arg_tms1  in
                           (uu____3770, (FStar_List.append sz_decls decls)))))

and (encode_deeply_embedded_quantifier :
  FStar_Syntax_Syntax.term ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let env1 =
        let uu___364_3780 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___364_3780.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___364_3780.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___364_3780.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___364_3780.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___364_3780.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.cache =
            (uu___364_3780.FStar_SMTEncoding_Env.cache);
          FStar_SMTEncoding_Env.nolabels =
            (uu___364_3780.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name =
            (uu___364_3780.FStar_SMTEncoding_Env.use_zfuel_name);
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___364_3780.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___364_3780.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier = true
        }  in
      let uu____3782 = encode_term t env1  in
      match uu____3782 with
      | (tm,decls) ->
          let vars = FStar_SMTEncoding_Term.free_variables tm  in
          let valid_tm = FStar_SMTEncoding_Term.mk_Valid tm  in
          let key =
            FStar_SMTEncoding_Term.mkForall t.FStar_Syntax_Syntax.pos
              ([], vars, valid_tm)
             in
          let tkey_hash = FStar_SMTEncoding_Term.hash_of_term key  in
          let uu____3804 =
            FStar_Util.smap_try_find env1.FStar_SMTEncoding_Env.cache
              tkey_hash
             in
          (match uu____3804 with
           | FStar_Pervasives_Native.Some cache_entry ->
               (tm,
                 (FStar_List.append decls
                    (FStar_SMTEncoding_Env.use_cache_entry cache_entry)))
           | uu____3812 ->
               (match tm.FStar_SMTEncoding_Term.tm with
                | FStar_SMTEncoding_Term.App
                    (uu____3819,{
                                  FStar_SMTEncoding_Term.tm =
                                    FStar_SMTEncoding_Term.FreeV uu____3820;
                                  FStar_SMTEncoding_Term.freevars =
                                    uu____3821;
                                  FStar_SMTEncoding_Term.rng = uu____3822;_}::
                     {
                       FStar_SMTEncoding_Term.tm =
                         FStar_SMTEncoding_Term.FreeV uu____3823;
                       FStar_SMTEncoding_Term.freevars = uu____3824;
                       FStar_SMTEncoding_Term.rng = uu____3825;_}::[])
                    ->
                    (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                       (FStar_Errors.Warning_QuantifierWithoutPattern,
                         "Not encoding deeply embedded, unguarded quantifier to SMT");
                     (tm, decls))
                | uu____3871 ->
                    let uu____3872 = encode_formula t env1  in
                    (match uu____3872 with
                     | (phi,decls') ->
                         let interp =
                           match vars with
                           | [] ->
                               let uu____3892 =
                                 let uu____3897 =
                                   FStar_SMTEncoding_Term.mk_Valid tm  in
                                 (uu____3897, phi)  in
                               FStar_SMTEncoding_Util.mkIff uu____3892
                           | uu____3898 ->
                               let uu____3899 =
                                 let uu____3910 =
                                   let uu____3911 =
                                     let uu____3916 =
                                       FStar_SMTEncoding_Term.mk_Valid tm  in
                                     (uu____3916, phi)  in
                                   FStar_SMTEncoding_Util.mkIff uu____3911
                                    in
                                 ([[valid_tm]], vars, uu____3910)  in
                               FStar_SMTEncoding_Term.mkForall
                                 t.FStar_Syntax_Syntax.pos uu____3899
                            in
                         let ax =
                           let uu____3926 =
                             let uu____3934 =
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 "l_quant_interp"
                                in
                             (interp,
                               (FStar_Pervasives_Native.Some
                                  "Interpretation of deeply embedded quantifier"),
                               uu____3934)
                              in
                           FStar_SMTEncoding_Util.mkAssume uu____3926  in
                         let decls1 =
                           FStar_List.append decls
                             (FStar_List.append decls' [ax])
                            in
                         ((let uu____3944 =
                             FStar_SMTEncoding_Env.mk_cache_entry env1 "" []
                               decls1
                              in
                           FStar_Util.smap_add
                             env1.FStar_SMTEncoding_Env.cache tkey_hash
                             uu____3944);
                          (tm, decls1)))))

and (encode_term :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____3954 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____3954
       then
         let uu____3959 = FStar_Syntax_Print.tag_of_term t  in
         let uu____3961 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____3963 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____3959 uu____3961
           uu____3963
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____3972 ->
           let uu____3995 =
             let uu____3997 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____4000 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____4002 = FStar_Syntax_Print.term_to_string t0  in
             let uu____4004 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____3997
               uu____4000 uu____4002 uu____4004
              in
           failwith uu____3995
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____4011 =
             let uu____4013 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____4016 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____4018 = FStar_Syntax_Print.term_to_string t0  in
             let uu____4020 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____4013
               uu____4016 uu____4018 uu____4020
              in
           failwith uu____4011
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let e = FStar_Syntax_Util.unfold_lazy i  in
           ((let uu____4030 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____4030
             then
               let uu____4035 = FStar_Syntax_Print.term_to_string t0  in
               let uu____4037 = FStar_Syntax_Print.term_to_string e  in
               FStar_Util.print2 ">> Unfolded (%s) ~> (%s)\n" uu____4035
                 uu____4037
             else ());
            encode_term e env)
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____4043 =
             let uu____4045 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____4045
              in
           failwith uu____4043
       | FStar_Syntax_Syntax.Tm_ascribed (t1,(k,uu____4054),uu____4055) ->
           let uu____4104 =
             match k with
             | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
             | uu____4114 -> false  in
           if uu____4104
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t1 env
       | FStar_Syntax_Syntax.Tm_quoted (qt,uu____4132) ->
           let tv =
             let uu____4138 =
               let uu____4145 = FStar_Reflection_Basic.inspect_ln qt  in
               FStar_Syntax_Embeddings.embed
                 FStar_Reflection_Embeddings.e_term_view uu____4145
                in
             uu____4138 t.FStar_Syntax_Syntax.pos
               FStar_Pervasives_Native.None
               FStar_Syntax_Embeddings.id_norm_cb
              in
           ((let uu____4172 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____4172
             then
               let uu____4177 = FStar_Syntax_Print.term_to_string t0  in
               let uu____4179 = FStar_Syntax_Print.term_to_string tv  in
               FStar_Util.print2 ">> Inspected (%s) ~> (%s)\n" uu____4177
                 uu____4179
             else ());
            (let t1 =
               let uu____4187 =
                 let uu____4198 = FStar_Syntax_Syntax.as_arg tv  in
                 [uu____4198]  in
               FStar_Syntax_Util.mk_app
                 (FStar_Reflection_Data.refl_constant_term
                    FStar_Reflection_Data.fstar_refl_pack_ln) uu____4187
                in
             encode_term t1 env))
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_pattern uu____4224) ->
           encode_term t1
             (let uu___365_4242 = env  in
              {
                FStar_SMTEncoding_Env.bvar_bindings =
                  (uu___365_4242.FStar_SMTEncoding_Env.bvar_bindings);
                FStar_SMTEncoding_Env.fvar_bindings =
                  (uu___365_4242.FStar_SMTEncoding_Env.fvar_bindings);
                FStar_SMTEncoding_Env.depth =
                  (uu___365_4242.FStar_SMTEncoding_Env.depth);
                FStar_SMTEncoding_Env.tcenv =
                  (uu___365_4242.FStar_SMTEncoding_Env.tcenv);
                FStar_SMTEncoding_Env.warn =
                  (uu___365_4242.FStar_SMTEncoding_Env.warn);
                FStar_SMTEncoding_Env.cache =
                  (uu___365_4242.FStar_SMTEncoding_Env.cache);
                FStar_SMTEncoding_Env.nolabels =
                  (uu___365_4242.FStar_SMTEncoding_Env.nolabels);
                FStar_SMTEncoding_Env.use_zfuel_name =
                  (uu___365_4242.FStar_SMTEncoding_Env.use_zfuel_name);
                FStar_SMTEncoding_Env.encode_non_total_function_typ =
                  (uu___365_4242.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                FStar_SMTEncoding_Env.current_module_name =
                  (uu___365_4242.FStar_SMTEncoding_Env.current_module_name);
                FStar_SMTEncoding_Env.encoding_quantifier = false
              })
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____4245) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = FStar_SMTEncoding_Env.lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____4253 = head_redex env t  in
           if uu____4253
           then let uu____4260 = whnf env t  in encode_term uu____4260 env
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
                  | FStar_SMTEncoding_Term.FreeV uu____4268 ->
                      let uu____4277 =
                        let uu____4278 =
                          let uu____4286 =
                            FStar_SMTEncoding_Term.kick_partial_app tok  in
                          let uu____4287 =
                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                              "@kick_partial_app"
                             in
                          (uu____4286,
                            (FStar_Pervasives_Native.Some "kick_partial_app"),
                            uu____4287)
                           in
                        FStar_SMTEncoding_Util.mkAssume uu____4278  in
                      [uu____4277]
                  | FStar_SMTEncoding_Term.App (uu____4293,[]) ->
                      let uu____4296 =
                        let uu____4297 =
                          let uu____4305 =
                            FStar_SMTEncoding_Term.kick_partial_app tok  in
                          let uu____4306 =
                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                              "@kick_partial_app"
                             in
                          (uu____4305,
                            (FStar_Pervasives_Native.Some "kick_partial_app"),
                            uu____4306)
                           in
                        FStar_SMTEncoding_Util.mkAssume uu____4297  in
                      [uu____4296]
                  | uu____4312 -> []
                else []  in
              (tok, aux_decls))
       | FStar_Syntax_Syntax.Tm_type uu____4315 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4317) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.FStar_SMTEncoding_Env.current_module_name
              in
           let uu____4347 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____4347 with
            | (binders1,res) ->
                let uu____4358 =
                  (env.FStar_SMTEncoding_Env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____4358
                then
                  let uu____4365 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____4365 with
                   | (vars,guards,env',decls,uu____4390) ->
                       let fsym =
                         let uu____4404 =
                           let uu____4410 =
                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                               "f"
                              in
                           (uu____4410, FStar_SMTEncoding_Term.Term_sort)  in
                         FStar_SMTEncoding_Term.mk_fv uu____4404  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____4416 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___366_4425 =
                              env.FStar_SMTEncoding_Env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___366_4425.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___366_4425.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___366_4425.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___366_4425.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___366_4425.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___366_4425.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___366_4425.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___366_4425.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___366_4425.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___366_4425.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___366_4425.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___366_4425.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___366_4425.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___366_4425.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___366_4425.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___366_4425.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___366_4425.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___366_4425.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___366_4425.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___366_4425.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___366_4425.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___366_4425.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___366_4425.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___366_4425.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___366_4425.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___366_4425.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___366_4425.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___366_4425.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___366_4425.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___366_4425.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___366_4425.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___366_4425.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___366_4425.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___366_4425.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___366_4425.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___366_4425.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___366_4425.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___366_4425.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___366_4425.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___366_4425.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___366_4425.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___366_4425.FStar_TypeChecker_Env.nbe)
                            }) res
                          in
                       (match uu____4416 with
                        | (pre_opt,res_t) ->
                            let uu____4437 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____4437 with
                             | (res_pred,decls') ->
                                 let uu____4448 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____4461 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____4461, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____4465 =
                                         encode_formula pre env'  in
                                       (match uu____4465 with
                                        | (guard,decls0) ->
                                            let uu____4478 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____4478, decls0))
                                    in
                                 (match uu____4448 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____4492 =
                                          let uu____4503 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____4503)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t.FStar_Syntax_Syntax.pos
                                          uu____4492
                                         in
                                      let cvars =
                                        let uu____4523 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____4523
                                          (FStar_List.filter
                                             (fun x  ->
                                                let uu____4542 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    x
                                                   in
                                                let uu____4544 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    fsym
                                                   in
                                                uu____4542 <> uu____4544))
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
                                      let uu____4564 =
                                        FStar_Util.smap_try_find
                                          env.FStar_SMTEncoding_Env.cache
                                          tkey_hash
                                         in
                                      (match uu____4564 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____4572 =
                                             let uu____4573 =
                                               let uu____4581 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV)
                                                  in
                                               ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                                 uu____4581)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4573
                                              in
                                           (uu____4572,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (FStar_SMTEncoding_Env.use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____4593 =
                                               let uu____4595 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____4595
                                                in
                                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                               uu____4593
                                              in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_SMTEncoding_Term.fv_sort
                                               cvars
                                              in
                                           let caption =
                                             let uu____4610 =
                                               FStar_Options.log_queries ()
                                                in
                                             if uu____4610
                                             then
                                               let uu____4613 =
                                                 let uu____4615 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env.FStar_SMTEncoding_Env.tcenv
                                                     t0
                                                    in
                                                 FStar_Util.replace_char
                                                   uu____4615 10 32
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____4613
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
                                             let uu____4628 =
                                               let uu____4636 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars
                                                  in
                                               (tsym, uu____4636)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4628
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
                                             let uu____4655 =
                                               let uu____4663 =
                                                 FStar_SMTEncoding_Term.mkForall
                                                   t0.FStar_Syntax_Syntax.pos
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind)
                                                  in
                                               (uu____4663,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name)
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4655
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
                                             let uu____4680 =
                                               let uu____4688 =
                                                 let uu____4689 =
                                                   let uu____4700 =
                                                     let uu____4701 =
                                                       let uu____4706 =
                                                         let uu____4707 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f
                                                            in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____4707
                                                          in
                                                       (f_has_t, uu____4706)
                                                        in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____4701
                                                      in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____4700)
                                                    in
                                                 let uu____4725 =
                                                   mkForall_fuel
                                                     t0.FStar_Syntax_Syntax.pos
                                                    in
                                                 uu____4725 uu____4689  in
                                               (uu____4688,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4680
                                              in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym
                                                in
                                             let uu____4748 =
                                               let uu____4756 =
                                                 let uu____4757 =
                                                   let uu____4768 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp)
                                                      in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____4768)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   t0.FStar_Syntax_Syntax.pos
                                                   uu____4757
                                                  in
                                               (uu____4756,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4748
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
                                           ((let uu____4792 =
                                               FStar_SMTEncoding_Env.mk_cache_entry
                                                 env tsym cvar_sorts t_decls1
                                                in
                                             FStar_Util.smap_add
                                               env.FStar_SMTEncoding_Env.cache
                                               tkey_hash uu____4792);
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
                     let uu____4811 =
                       let uu____4819 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____4819,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____4811  in
                   let fsym =
                     FStar_SMTEncoding_Term.mk_fv
                       ("f", FStar_SMTEncoding_Term.Term_sort)
                      in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym  in
                     let uu____4833 =
                       let uu____4841 =
                         let uu____4842 =
                           let uu____4853 =
                             let uu____4854 =
                               let uu____4859 =
                                 let uu____4860 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____4860
                                  in
                               (f_has_t, uu____4859)  in
                             FStar_SMTEncoding_Util.mkImp uu____4854  in
                           ([[f_has_t]], [fsym], uu____4853)  in
                         let uu____4886 =
                           mkForall_fuel t0.FStar_Syntax_Syntax.pos  in
                         uu____4886 uu____4842  in
                       (uu____4841, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____4833  in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____4904 ->
           let uu____4911 =
             let uu____4916 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Env.Weak;
                 FStar_TypeChecker_Env.HNF;
                 FStar_TypeChecker_Env.EraseUniverses]
                 env.FStar_SMTEncoding_Env.tcenv t0
                in
             match uu____4916 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____4923;
                 FStar_Syntax_Syntax.vars = uu____4924;_} ->
                 let uu____4931 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____4931 with
                  | (b,f1) ->
                      let uu____4956 =
                        let uu____4957 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____4957  in
                      (uu____4956, f1))
             | uu____4972 -> failwith "impossible"  in
           (match uu____4911 with
            | (x,f) ->
                let uu____4984 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____4984 with
                 | (base_t,decls) ->
                     let uu____4995 =
                       FStar_SMTEncoding_Env.gen_term_var env x  in
                     (match uu____4995 with
                      | (x1,xtm,env') ->
                          let uu____5012 = encode_formula f env'  in
                          (match uu____5012 with
                           | (refinement,decls') ->
                               let uu____5023 =
                                 FStar_SMTEncoding_Env.fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____5023 with
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
                                      let uu____5051 =
                                        let uu____5062 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____5073 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____5062
                                          uu____5073
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____5051
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun y  ->
                                              (let uu____5127 =
                                                 FStar_SMTEncoding_Term.fv_name
                                                   y
                                                  in
                                               uu____5127 <> x1) &&
                                                (let uu____5131 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     y
                                                    in
                                                 uu____5131 <> fsym)))
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
                                    let uu____5163 =
                                      FStar_Util.smap_try_find
                                        env.FStar_SMTEncoding_Env.cache
                                        tkey_hash
                                       in
                                    (match uu____5163 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____5171 =
                                           let uu____5172 =
                                             let uu____5180 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV)
                                                in
                                             ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                               uu____5180)
                                              in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____5172
                                            in
                                         (uu____5171,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (FStar_SMTEncoding_Env.use_cache_entry
                                                    cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.FStar_SMTEncoding_Env.current_module_name
                                            in
                                         let tsym =
                                           let uu____5194 =
                                             let uu____5196 =
                                               let uu____5198 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____5198
                                                in
                                             Prims.strcat module_name
                                               uu____5196
                                              in
                                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                             uu____5194
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
                                           let uu____5218 =
                                             let uu____5226 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1
                                                in
                                             (tsym, uu____5226)  in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____5218
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
                                           let uu____5246 =
                                             let uu____5254 =
                                               let uu____5255 =
                                                 let uu____5266 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base)
                                                    in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____5266)
                                                  in
                                               FStar_SMTEncoding_Term.mkForall
                                                 t0.FStar_Syntax_Syntax.pos
                                                 uu____5255
                                                in
                                             (uu____5254,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____5246
                                            in
                                         let t_kinding =
                                           let uu____5280 =
                                             let uu____5288 =
                                               FStar_SMTEncoding_Term.mkForall
                                                 t0.FStar_Syntax_Syntax.pos
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind)
                                                in
                                             (uu____5288,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____5280
                                            in
                                         let t_interp =
                                           let uu____5302 =
                                             let uu____5310 =
                                               let uu____5311 =
                                                 let uu____5322 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding)
                                                    in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____5322)
                                                  in
                                               FStar_SMTEncoding_Term.mkForall
                                                 t0.FStar_Syntax_Syntax.pos
                                                 uu____5311
                                                in
                                             (uu____5310,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement_interpretation"),
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____5302
                                            in
                                         let t_decls1 =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1])
                                            in
                                         ((let uu____5355 =
                                             FStar_SMTEncoding_Env.mk_cache_entry
                                               env tsym cvar_sorts t_decls1
                                              in
                                           FStar_Util.smap_add
                                             env.FStar_SMTEncoding_Env.cache
                                             tkey_hash uu____5355);
                                          (t1, t_decls1))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,uu____5357) ->
           let ttm =
             let uu____5375 =
               FStar_Syntax_Unionfind.uvar_id
                 uv.FStar_Syntax_Syntax.ctx_uvar_head
                in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____5375  in
           let uu____5377 =
             encode_term_pred FStar_Pervasives_Native.None
               uv.FStar_Syntax_Syntax.ctx_uvar_typ env ttm
              in
           (match uu____5377 with
            | (t_has_k,decls) ->
                let d =
                  let uu____5389 =
                    let uu____5397 =
                      let uu____5399 =
                        let uu____5401 =
                          let uu____5403 =
                            FStar_Syntax_Unionfind.uvar_id
                              uv.FStar_Syntax_Syntax.ctx_uvar_head
                             in
                          FStar_Util.string_of_int uu____5403  in
                        FStar_Util.format1 "uvar_typing_%s" uu____5401  in
                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                        uu____5399
                       in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____5397)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____5389  in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____5409 ->
           let uu____5426 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____5426 with
            | (head1,args_e) ->
                let uu____5473 =
                  let uu____5488 =
                    let uu____5489 = FStar_Syntax_Subst.compress head1  in
                    uu____5489.FStar_Syntax_Syntax.n  in
                  (uu____5488, args_e)  in
                (match uu____5473 with
                 | uu____5506 when head_redex env head1 ->
                     let uu____5521 = whnf env t  in
                     encode_term uu____5521 env
                 | uu____5522 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____5545 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5563) when
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
                       FStar_Syntax_Syntax.pos = uu____5585;
                       FStar_Syntax_Syntax.vars = uu____5586;_},uu____5587),uu____5588)
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
                       FStar_Syntax_Syntax.pos = uu____5614;
                       FStar_Syntax_Syntax.vars = uu____5615;_},uu____5616),
                    (v0,uu____5618)::(v1,uu____5620)::(v2,uu____5622)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____5693 = encode_term v0 env  in
                     (match uu____5693 with
                      | (v01,decls0) ->
                          let uu____5704 = encode_term v1 env  in
                          (match uu____5704 with
                           | (v11,decls1) ->
                               let uu____5715 = encode_term v2 env  in
                               (match uu____5715 with
                                | (v21,decls2) ->
                                    let uu____5726 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____5726,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(v0,uu____5729)::(v1,uu____5731)::(v2,uu____5733)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____5800 = encode_term v0 env  in
                     (match uu____5800 with
                      | (v01,decls0) ->
                          let uu____5811 = encode_term v1 env  in
                          (match uu____5811 with
                           | (v11,decls1) ->
                               let uu____5822 = encode_term v2 env  in
                               (match uu____5822 with
                                | (v21,decls2) ->
                                    let uu____5833 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____5833,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____5835)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____5871)::(rng,uu____5873)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____5924) ->
                     let e0 =
                       let uu____5946 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg
                         env.FStar_SMTEncoding_Env.tcenv head1 uu____5946
                        in
                     ((let uu____5956 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug
                              env.FStar_SMTEncoding_Env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____5956
                       then
                         let uu____5961 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____5961
                       else ());
                      (let e =
                         let uu____5969 =
                           let uu____5974 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____5975 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____5974
                             uu____5975
                            in
                         uu____5969 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____5986),(arg,uu____5988)::[]) -> encode_term arg env
                 | uu____6023 ->
                     let uu____6038 = encode_args args_e env  in
                     (match uu____6038 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____6099 = encode_term head1 env  in
                            match uu____6099 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____6171 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____6171 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____6269  ->
                                                 fun uu____6270  ->
                                                   match (uu____6269,
                                                           uu____6270)
                                                   with
                                                   | ((bv,uu____6300),
                                                      (a,uu____6302)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____6332 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____6332
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____6333 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm
                                             in
                                          (match uu____6333 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type
                                                  in
                                               let e_typing =
                                                 let uu____6348 =
                                                   let uu____6356 =
                                                     FStar_SMTEncoding_Term.mkForall
                                                       t0.FStar_Syntax_Syntax.pos
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____6365 =
                                                     let uu____6367 =
                                                       let uu____6369 =
                                                         let uu____6371 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm
                                                            in
                                                         FStar_Util.digest_of_string
                                                           uu____6371
                                                          in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____6369
                                                        in
                                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                       uu____6367
                                                      in
                                                   (uu____6356,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____6365)
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____6348
                                                  in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing])))))))
                             in
                          let encode_full_app fv =
                            let uu____6393 =
                              FStar_SMTEncoding_Env.lookup_free_var_sym env
                                fv
                               in
                            match uu____6393 with
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
                                   FStar_Syntax_Syntax.pos = uu____6436;
                                   FStar_Syntax_Syntax.vars = uu____6437;_},uu____6438)
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
                                   FStar_Syntax_Syntax.pos = uu____6445;
                                   FStar_Syntax_Syntax.vars = uu____6446;_},uu____6447)
                                ->
                                let uu____6452 =
                                  let uu____6453 =
                                    let uu____6458 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____6458
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____6453
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____6452
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____6488 =
                                  let uu____6489 =
                                    let uu____6494 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____6494
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____6489
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____6488
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____6523,(FStar_Util.Inl t1,uu____6525),uu____6526)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____6573,(FStar_Util.Inr c,uu____6575),uu____6576)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____6623 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____6644 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Env.Weak;
                                     FStar_TypeChecker_Env.HNF;
                                     FStar_TypeChecker_Env.EraseUniverses]
                                     env.FStar_SMTEncoding_Env.tcenv
                                     head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____6644
                                  in
                               let uu____6645 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____6645 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____6661;
                                            FStar_Syntax_Syntax.vars =
                                              uu____6662;_},uu____6663)
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
                                     | uu____6681 ->
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
           let uu____6760 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____6760 with
            | (bs1,body1,opening) ->
                let fallback uu____6785 =
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
                  let uu____6795 =
                    let uu____6796 =
                      FStar_SMTEncoding_Term.mk_fv
                        (f, FStar_SMTEncoding_Term.Term_sort)
                       in
                    FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV
                      uu____6796
                     in
                  (uu____6795, [decl])  in
                let is_impure rc =
                  let uu____6807 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                      env.FStar_SMTEncoding_Env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____6807 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____6822 =
                          let uu____6835 =
                            FStar_TypeChecker_Env.get_range
                              env.FStar_SMTEncoding_Env.tcenv
                             in
                          FStar_TypeChecker_Util.new_implicit_var
                            "SMTEncoding codomain" uu____6835
                            env.FStar_SMTEncoding_Env.tcenv
                            FStar_Syntax_Util.ktype0
                           in
                        (match uu____6822 with
                         | (t1,uu____6838,uu____6839) -> t1)
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  let uu____6857 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                     in
                  if uu____6857
                  then
                    let uu____6862 = FStar_Syntax_Syntax.mk_Total res_typ  in
                    FStar_Pervasives_Native.Some uu____6862
                  else
                    (let uu____6865 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid
                        in
                     if uu____6865
                     then
                       let uu____6870 = FStar_Syntax_Syntax.mk_GTotal res_typ
                          in
                       FStar_Pervasives_Native.Some uu____6870
                     else FStar_Pervasives_Native.None)
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____6878 =
                         let uu____6884 =
                           let uu____6886 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____6886
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____6884)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____6878);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____6891 =
                       (is_impure rc) &&
                         (let uu____6894 =
                            FStar_TypeChecker_Env.is_reifiable_rc
                              env.FStar_SMTEncoding_Env.tcenv rc
                             in
                          Prims.op_Negation uu____6894)
                        in
                     if uu____6891
                     then fallback ()
                     else
                       (let cache_size =
                          FStar_Util.smap_size
                            env.FStar_SMTEncoding_Env.cache
                           in
                        let uu____6905 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____6905 with
                        | (vars,guards,envbody,decls,uu____6930) ->
                            let body2 =
                              let uu____6944 =
                                FStar_TypeChecker_Env.is_reifiable_rc
                                  env.FStar_SMTEncoding_Env.tcenv rc
                                 in
                              if uu____6944
                              then
                                FStar_TypeChecker_Util.reify_body
                                  env.FStar_SMTEncoding_Env.tcenv body1
                              else body1  in
                            let uu____6949 = encode_term body2 envbody  in
                            (match uu____6949 with
                             | (body3,decls') ->
                                 let uu____6960 =
                                   let uu____6969 = codomain_eff rc  in
                                   match uu____6969 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____6988 = encode_term tfun env
                                          in
                                       (match uu____6988 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____6960 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____7022 =
                                          let uu____7033 =
                                            let uu____7034 =
                                              let uu____7039 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____7039, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____7034
                                             in
                                          ([], vars, uu____7033)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t0.FStar_Syntax_Syntax.pos
                                          uu____7022
                                         in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body
                                         in
                                      let uu____7047 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            (cvars, key_body)
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____7063 =
                                              let uu____7066 =
                                                let uu____7077 =
                                                  FStar_SMTEncoding_Term.free_variables
                                                    t1
                                                   in
                                                FStar_List.append uu____7077
                                                  cvars
                                                 in
                                              FStar_Util.remove_dups
                                                FStar_SMTEncoding_Term.fv_eq
                                                uu____7066
                                               in
                                            let uu____7104 =
                                              FStar_SMTEncoding_Util.mkAnd
                                                (key_body, t1)
                                               in
                                            (uu____7063, uu____7104)
                                         in
                                      (match uu____7047 with
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
                                           let uu____7126 =
                                             FStar_Util.smap_try_find
                                               env.FStar_SMTEncoding_Env.cache
                                               tkey_hash
                                              in
                                           (match uu____7126 with
                                            | FStar_Pervasives_Native.Some
                                                cache_entry ->
                                                let uu____7134 =
                                                  let uu____7135 =
                                                    let uu____7143 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                                      uu____7143)
                                                     in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____7135
                                                   in
                                                (uu____7134,
                                                  (FStar_List.append decls
                                                     (FStar_List.append
                                                        decls'
                                                        (FStar_List.append
                                                           decls''
                                                           (FStar_SMTEncoding_Env.use_cache_entry
                                                              cache_entry)))))
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                let uu____7149 =
                                                  is_an_eta_expansion env
                                                    vars body3
                                                   in
                                                (match uu____7149 with
                                                 | FStar_Pervasives_Native.Some
                                                     t1 ->
                                                     let decls1 =
                                                       let uu____7158 =
                                                         let uu____7160 =
                                                           FStar_Util.smap_size
                                                             env.FStar_SMTEncoding_Env.cache
                                                            in
                                                         uu____7160 =
                                                           cache_size
                                                          in
                                                       if uu____7158
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
                                                         let uu____7175 =
                                                           let uu____7177 =
                                                             FStar_Util.digest_of_string
                                                               tkey_hash
                                                              in
                                                           Prims.strcat
                                                             "Tm_abs_"
                                                             uu____7177
                                                            in
                                                         FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                           uu____7175
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
                                                       let uu____7187 =
                                                         let uu____7195 =
                                                           FStar_List.map
                                                             FStar_SMTEncoding_Util.mkFreeV
                                                             cvars1
                                                            in
                                                         (fsym, uu____7195)
                                                          in
                                                       FStar_SMTEncoding_Util.mkApp
                                                         uu____7187
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
                                                           let uu____7212 =
                                                             let uu____7213 =
                                                               let uu____7221
                                                                 =
                                                                 FStar_SMTEncoding_Term.mkForall
                                                                   t0.FStar_Syntax_Syntax.pos
                                                                   ([[f]],
                                                                    cvars1,
                                                                    f_has_t)
                                                                  in
                                                               (uu____7221,
                                                                 (FStar_Pervasives_Native.Some
                                                                    a_name),
                                                                 a_name)
                                                                in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____7213
                                                              in
                                                           [uu____7212]
                                                        in
                                                     let interp_f =
                                                       let a_name =
                                                         Prims.strcat
                                                           "interpretation_"
                                                           fsym
                                                          in
                                                       let uu____7236 =
                                                         let uu____7244 =
                                                           let uu____7245 =
                                                             let uu____7256 =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (app, body3)
                                                                in
                                                             ([[app]],
                                                               (FStar_List.append
                                                                  vars cvars1),
                                                               uu____7256)
                                                              in
                                                           FStar_SMTEncoding_Term.mkForall
                                                             t0.FStar_Syntax_Syntax.pos
                                                             uu____7245
                                                            in
                                                         (uu____7244,
                                                           (FStar_Pervasives_Native.Some
                                                              a_name),
                                                           a_name)
                                                          in
                                                       FStar_SMTEncoding_Util.mkAssume
                                                         uu____7236
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
                                                     ((let uu____7271 =
                                                         FStar_SMTEncoding_Env.mk_cache_entry
                                                           env fsym
                                                           cvar_sorts f_decls
                                                          in
                                                       FStar_Util.smap_add
                                                         env.FStar_SMTEncoding_Env.cache
                                                         tkey_hash uu____7271);
                                                      (f, f_decls))))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____7272,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____7273;
                          FStar_Syntax_Syntax.lbunivs = uu____7274;
                          FStar_Syntax_Syntax.lbtyp = uu____7275;
                          FStar_Syntax_Syntax.lbeff = uu____7276;
                          FStar_Syntax_Syntax.lbdef = uu____7277;
                          FStar_Syntax_Syntax.lbattrs = uu____7278;
                          FStar_Syntax_Syntax.lbpos = uu____7279;_}::uu____7280),uu____7281)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____7315;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____7317;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____7319;
                FStar_Syntax_Syntax.lbpos = uu____7320;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____7347 ->
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
              let uu____7419 =
                let uu____7424 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____7424 env  in
              match uu____7419 with
              | (ee1,decls1) ->
                  let uu____7449 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____7449 with
                   | (xs,e21) ->
                       let uu____7474 = FStar_List.hd xs  in
                       (match uu____7474 with
                        | (x1,uu____7492) ->
                            let env' =
                              FStar_SMTEncoding_Env.push_term_var env x1 ee1
                               in
                            let uu____7498 = encode_body e21 env'  in
                            (match uu____7498 with
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
            let uu____7528 =
              let uu____7536 =
                let uu____7537 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____7537  in
              FStar_SMTEncoding_Env.gen_term_var env uu____7536  in
            match uu____7528 with
            | (scrsym,scr',env1) ->
                let uu____7547 = encode_term e env1  in
                (match uu____7547 with
                 | (scr,decls) ->
                     let uu____7558 =
                       let encode_branch b uu____7587 =
                         match uu____7587 with
                         | (else_case,decls1) ->
                             let uu____7606 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____7606 with
                              | (p,w,br) ->
                                  let uu____7632 = encode_pat env1 p  in
                                  (match uu____7632 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____7669  ->
                                                   match uu____7669 with
                                                   | (x,t) ->
                                                       FStar_SMTEncoding_Env.push_term_var
                                                         env2 x t) env1)
                                          in
                                       let uu____7676 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____7698 =
                                               encode_term w1 env2  in
                                             (match uu____7698 with
                                              | (w2,decls2) ->
                                                  let uu____7711 =
                                                    let uu____7712 =
                                                      let uu____7717 =
                                                        let uu____7718 =
                                                          let uu____7723 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____7723)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____7718
                                                         in
                                                      (guard, uu____7717)  in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____7712
                                                     in
                                                  (uu____7711, decls2))
                                          in
                                       (match uu____7676 with
                                        | (guard1,decls2) ->
                                            let uu____7738 =
                                              encode_br br env2  in
                                            (match uu____7738 with
                                             | (br1,decls3) ->
                                                 let uu____7751 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____7751,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____7558 with
                      | (match_tm,decls1) ->
                          let uu____7772 =
                            let uu____7773 =
                              let uu____7784 =
                                let uu____7791 =
                                  let uu____7796 =
                                    FStar_SMTEncoding_Term.mk_fv
                                      (scrsym,
                                        FStar_SMTEncoding_Term.Term_sort)
                                     in
                                  (uu____7796, scr)  in
                                [uu____7791]  in
                              (uu____7784, match_tm)  in
                            FStar_SMTEncoding_Term.mkLet' uu____7773
                              FStar_Range.dummyRange
                             in
                          (uu____7772, decls1)))

and (encode_pat :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.pat -> (FStar_SMTEncoding_Env.env_t * pattern))
  =
  fun env  ->
    fun pat  ->
      (let uu____7819 =
         FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
           FStar_Options.Medium
          in
       if uu____7819
       then
         let uu____7822 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____7822
       else ());
      (let uu____7827 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____7827 with
       | (vars,pat_term) ->
           let uu____7844 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____7886  ->
                     fun v1  ->
                       match uu____7886 with
                       | (env1,vars1) ->
                           let uu____7922 =
                             FStar_SMTEncoding_Env.gen_term_var env1 v1  in
                           (match uu____7922 with
                            | (xx,uu____7941,env2) ->
                                let uu____7945 =
                                  let uu____7952 =
                                    let uu____7957 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xx,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    (v1, uu____7957)  in
                                  uu____7952 :: vars1  in
                                (env2, uu____7945))) (env, []))
              in
           (match uu____7844 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____8012 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____8013 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____8014 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____8022 = encode_const c env1  in
                      (match uu____8022 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____8030::uu____8031 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____8035 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon
                            env1.FStar_SMTEncoding_Env.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____8058 =
                          FStar_TypeChecker_Env.datacons_of_typ
                            env1.FStar_SMTEncoding_Env.tcenv tc_name
                           in
                        match uu____8058 with
                        | (uu____8066,uu____8067::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____8072 ->
                            FStar_SMTEncoding_Env.mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____8108  ->
                                  match uu____8108 with
                                  | (arg,uu____8118) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____8127 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____8127))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____8159) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____8190 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____8215 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____8261  ->
                                  match uu____8261 with
                                  | (arg,uu____8277) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____8286 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____8286))
                         in
                      FStar_All.pipe_right uu____8215 FStar_List.flatten
                   in
                let pat_term1 uu____8317 = encode_term pat_term env1  in
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
      let uu____8327 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____8375  ->
                fun uu____8376  ->
                  match (uu____8375, uu____8376) with
                  | ((tms,decls),(t,uu____8416)) ->
                      let uu____8443 = encode_term t env  in
                      (match uu____8443 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____8327 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____8500 = FStar_Syntax_Util.list_elements e  in
        match uu____8500 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____8531 =
          let uu____8548 = FStar_Syntax_Util.unmeta p  in
          FStar_All.pipe_right uu____8548 FStar_Syntax_Util.head_and_args  in
        match uu____8531 with
        | (head1,args) ->
            let uu____8599 =
              let uu____8614 =
                let uu____8615 = FStar_Syntax_Util.un_uinst head1  in
                uu____8615.FStar_Syntax_Syntax.n  in
              (uu____8614, args)  in
            (match uu____8599 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____8637,uu____8638)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____8690 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or1 t1 =
          let uu____8745 =
            let uu____8762 = FStar_Syntax_Util.unmeta t1  in
            FStar_All.pipe_right uu____8762 FStar_Syntax_Util.head_and_args
             in
          match uu____8745 with
          | (head1,args) ->
              let uu____8809 =
                let uu____8824 =
                  let uu____8825 = FStar_Syntax_Util.un_uinst head1  in
                  uu____8825.FStar_Syntax_Syntax.n  in
                (uu____8824, args)  in
              (match uu____8809 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____8844)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____8881 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____8911 = smt_pat_or1 t1  in
            (match uu____8911 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____8933 = list_elements1 e  in
                 FStar_All.pipe_right uu____8933
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____8963 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____8963
                           (FStar_List.map one_pat)))
             | uu____8986 ->
                 let uu____8991 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____8991])
        | uu____9042 ->
            let uu____9045 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____9045]
         in
      let uu____9096 =
        let uu____9111 =
          let uu____9112 = FStar_Syntax_Subst.compress t  in
          uu____9112.FStar_Syntax_Syntax.n  in
        match uu____9111 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____9151 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____9151 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____9186;
                        FStar_Syntax_Syntax.effect_name = uu____9187;
                        FStar_Syntax_Syntax.result_typ = uu____9188;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____9190)::(post,uu____9192)::(pats,uu____9194)::[];
                        FStar_Syntax_Syntax.flags = uu____9195;_}
                      ->
                      let uu____9256 = lemma_pats pats  in
                      (binders1, pre, post, uu____9256)
                  | uu____9267 -> failwith "impos"))
        | uu____9283 -> failwith "Impos"  in
      match uu____9096 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___367_9320 = env  in
            {
              FStar_SMTEncoding_Env.bvar_bindings =
                (uu___367_9320.FStar_SMTEncoding_Env.bvar_bindings);
              FStar_SMTEncoding_Env.fvar_bindings =
                (uu___367_9320.FStar_SMTEncoding_Env.fvar_bindings);
              FStar_SMTEncoding_Env.depth =
                (uu___367_9320.FStar_SMTEncoding_Env.depth);
              FStar_SMTEncoding_Env.tcenv =
                (uu___367_9320.FStar_SMTEncoding_Env.tcenv);
              FStar_SMTEncoding_Env.warn =
                (uu___367_9320.FStar_SMTEncoding_Env.warn);
              FStar_SMTEncoding_Env.cache =
                (uu___367_9320.FStar_SMTEncoding_Env.cache);
              FStar_SMTEncoding_Env.nolabels =
                (uu___367_9320.FStar_SMTEncoding_Env.nolabels);
              FStar_SMTEncoding_Env.use_zfuel_name = true;
              FStar_SMTEncoding_Env.encode_non_total_function_typ =
                (uu___367_9320.FStar_SMTEncoding_Env.encode_non_total_function_typ);
              FStar_SMTEncoding_Env.current_module_name =
                (uu___367_9320.FStar_SMTEncoding_Env.current_module_name);
              FStar_SMTEncoding_Env.encoding_quantifier =
                (uu___367_9320.FStar_SMTEncoding_Env.encoding_quantifier)
            }  in
          let uu____9322 =
            encode_binders FStar_Pervasives_Native.None binders env1  in
          (match uu____9322 with
           | (vars,guards,env2,decls,uu____9347) ->
               let uu____9360 = encode_smt_patterns patterns env2  in
               (match uu____9360 with
                | (pats,decls') ->
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
                    let env3 =
                      let uu___368_9393 = env2  in
                      {
                        FStar_SMTEncoding_Env.bvar_bindings =
                          (uu___368_9393.FStar_SMTEncoding_Env.bvar_bindings);
                        FStar_SMTEncoding_Env.fvar_bindings =
                          (uu___368_9393.FStar_SMTEncoding_Env.fvar_bindings);
                        FStar_SMTEncoding_Env.depth =
                          (uu___368_9393.FStar_SMTEncoding_Env.depth);
                        FStar_SMTEncoding_Env.tcenv =
                          (uu___368_9393.FStar_SMTEncoding_Env.tcenv);
                        FStar_SMTEncoding_Env.warn =
                          (uu___368_9393.FStar_SMTEncoding_Env.warn);
                        FStar_SMTEncoding_Env.cache =
                          (uu___368_9393.FStar_SMTEncoding_Env.cache);
                        FStar_SMTEncoding_Env.nolabels = true;
                        FStar_SMTEncoding_Env.use_zfuel_name =
                          (uu___368_9393.FStar_SMTEncoding_Env.use_zfuel_name);
                        FStar_SMTEncoding_Env.encode_non_total_function_typ =
                          (uu___368_9393.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                        FStar_SMTEncoding_Env.current_module_name =
                          (uu___368_9393.FStar_SMTEncoding_Env.current_module_name);
                        FStar_SMTEncoding_Env.encoding_quantifier =
                          (uu___368_9393.FStar_SMTEncoding_Env.encoding_quantifier)
                      }  in
                    let uu____9395 =
                      let uu____9400 = FStar_Syntax_Util.unmeta pre  in
                      encode_formula uu____9400 env3  in
                    (match uu____9395 with
                     | (pre1,decls'') ->
                         let uu____9407 =
                           let uu____9412 = FStar_Syntax_Util.unmeta post1
                              in
                           encode_formula uu____9412 env3  in
                         (match uu____9407 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append decls'
                                     (FStar_List.append decls'' decls'''))
                                 in
                              let uu____9422 =
                                let uu____9423 =
                                  let uu____9434 =
                                    let uu____9435 =
                                      let uu____9440 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards)
                                         in
                                      (uu____9440, post2)  in
                                    FStar_SMTEncoding_Util.mkImp uu____9435
                                     in
                                  (pats, vars, uu____9434)  in
                                FStar_SMTEncoding_Term.mkForall
                                  t.FStar_Syntax_Syntax.pos uu____9423
                                 in
                              (uu____9422, decls1)))))

and (encode_smt_patterns :
  FStar_Syntax_Syntax.arg Prims.list Prims.list ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term Prims.list Prims.list *
        FStar_SMTEncoding_Term.decl Prims.list))
  =
  fun pats_l  ->
    fun env  ->
      let env1 =
        let uu___369_9462 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___369_9462.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___369_9462.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___369_9462.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___369_9462.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___369_9462.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.cache =
            (uu___369_9462.FStar_SMTEncoding_Env.cache);
          FStar_SMTEncoding_Env.nolabels =
            (uu___369_9462.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___369_9462.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___369_9462.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___369_9462.FStar_SMTEncoding_Env.encoding_quantifier)
        }  in
      let encode_smt_pattern t =
        let uu____9478 = FStar_Syntax_Util.head_and_args t  in
        match uu____9478 with
        | (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____9541::(x,uu____9543)::(t1,uu____9545)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____9612 = encode_term x env1  in
                 (match uu____9612 with
                  | (x1,decls) ->
                      let uu____9623 = encode_term t1 env1  in
                      (match uu____9623 with
                       | (t2,decls') ->
                           let uu____9634 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                           (uu____9634, (FStar_List.append decls decls'))))
             | uu____9635 -> encode_term t env1)
         in
      FStar_List.fold_right
        (fun pats  ->
           fun uu____9678  ->
             match uu____9678 with
             | (pats_l1,decls) ->
                 let uu____9723 =
                   FStar_List.fold_right
                     (fun uu____9758  ->
                        fun uu____9759  ->
                          match (uu____9758, uu____9759) with
                          | ((p,uu____9801),(pats1,decls1)) ->
                              let uu____9836 = encode_smt_pattern p  in
                              (match uu____9836 with
                               | (t,d) ->
                                   let uu____9851 =
                                     FStar_SMTEncoding_Term.check_pattern_ok
                                       t
                                      in
                                   (match uu____9851 with
                                    | FStar_Pervasives_Native.None  ->
                                        ((t :: pats1),
                                          (FStar_List.append d decls1))
                                    | FStar_Pervasives_Native.Some
                                        illegal_subterm ->
                                        ((let uu____9868 =
                                            let uu____9874 =
                                              let uu____9876 =
                                                FStar_Syntax_Print.term_to_string
                                                  p
                                                 in
                                              let uu____9878 =
                                                FStar_SMTEncoding_Term.print_smt_term
                                                  illegal_subterm
                                                 in
                                              FStar_Util.format2
                                                "Pattern %s contains illegal sub-term (%s); dropping it"
                                                uu____9876 uu____9878
                                               in
                                            (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                                              uu____9874)
                                             in
                                          FStar_Errors.log_issue
                                            p.FStar_Syntax_Syntax.pos
                                            uu____9868);
                                         (pats1,
                                           (FStar_List.append d decls1))))))
                     pats ([], decls)
                    in
                 (match uu____9723 with
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
        let uu____9938 =
          FStar_All.pipe_left
            (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____9938
        then
          let uu____9943 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____9945 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____9943 uu____9945
        else ()  in
      let enc f r l =
        let uu____9987 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10019 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____10019 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____9987 with
        | (decls,args) ->
            let uu____10050 =
              let uu___370_10051 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___370_10051.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___370_10051.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10050, decls)
         in
      let const_op f r uu____10086 =
        let uu____10099 = f r  in (uu____10099, [])  in
      let un_op f l =
        let uu____10122 = FStar_List.hd l  in
        FStar_All.pipe_left f uu____10122  in
      let bin_op f uu___361_10142 =
        match uu___361_10142 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10153 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____10194 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____10219  ->
                 match uu____10219 with
                 | (t,uu____10235) ->
                     let uu____10240 = encode_formula t env  in
                     (match uu____10240 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____10194 with
        | (decls,phis) ->
            let uu____10269 =
              let uu___371_10270 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___371_10270.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___371_10270.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10269, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____10333  ->
               match uu____10333 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____10354) -> false
                    | uu____10357 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____10376 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____10376
        else
          (let uu____10393 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____10393 r rf)
         in
      let eq3_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____10465 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::t1::v0::v1::[] ->
                     let uu____10497 =
                       let uu____10502 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____10503 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____10502, uu____10503)  in
                     FStar_SMTEncoding_Util.mkAnd uu____10497
                 | uu____10504 -> failwith "Impossible")
             in
          uu____10465 r args
        else
          (let uu____10510 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____10510)
         in
      let h_equals_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____10582 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::v0::t1::v1::[] ->
                     let uu____10614 =
                       let uu____10619 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____10620 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____10619, uu____10620)  in
                     FStar_SMTEncoding_Util.mkAnd uu____10614
                 | uu____10621 -> failwith "Impossible")
             in
          uu____10582 r args
        else
          (let uu____10627 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____10627)
         in
      let mk_imp1 r uu___362_10662 =
        match uu___362_10662 with
        | (lhs,uu____10668)::(rhs,uu____10670)::[] ->
            let uu____10711 = encode_formula rhs env  in
            (match uu____10711 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____10726) ->
                      (l1, decls1)
                  | uu____10731 ->
                      let uu____10732 = encode_formula lhs env  in
                      (match uu____10732 with
                       | (l2,decls2) ->
                           let uu____10743 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____10743, (FStar_List.append decls1 decls2)))))
        | uu____10744 -> failwith "impossible"  in
      let mk_ite r uu___363_10772 =
        match uu___363_10772 with
        | (guard,uu____10778)::(_then,uu____10780)::(_else,uu____10782)::[]
            ->
            let uu____10839 = encode_formula guard env  in
            (match uu____10839 with
             | (g,decls1) ->
                 let uu____10850 = encode_formula _then env  in
                 (match uu____10850 with
                  | (t,decls2) ->
                      let uu____10861 = encode_formula _else env  in
                      (match uu____10861 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____10873 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____10903 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l
           in
        f uu____10903  in
      let connectives =
        let uu____10933 =
          let uu____10958 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____10958)  in
        let uu____11001 =
          let uu____11028 =
            let uu____11053 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____11053)  in
          let uu____11096 =
            let uu____11123 =
              let uu____11150 =
                let uu____11175 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____11175)  in
              let uu____11218 =
                let uu____11245 =
                  let uu____11272 =
                    let uu____11297 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____11297)  in
                  [uu____11272;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.c_eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq3_op);
                  (FStar_Parser_Const.c_eq3_lid, h_equals_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11245  in
              uu____11150 :: uu____11218  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11123  in
          uu____11028 :: uu____11096  in
        uu____10933 :: uu____11001  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____11842 = encode_formula phi' env  in
            (match uu____11842 with
             | (phi2,decls) ->
                 let uu____11853 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____11853, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____11855 ->
            let uu____11862 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____11862 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____11901 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____11901 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____11913;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____11915;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____11917;
                 FStar_Syntax_Syntax.lbpos = uu____11918;_}::[]),e2)
            ->
            let uu____11945 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____11945 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____11998::(x,uu____12000)::(t,uu____12002)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12069 = encode_term x env  in
                 (match uu____12069 with
                  | (x1,decls) ->
                      let uu____12080 = encode_term t env  in
                      (match uu____12080 with
                       | (t1,decls') ->
                           let uu____12091 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____12091, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12094)::(msg,uu____12096)::(phi2,uu____12098)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12165 =
                   let uu____12170 =
                     let uu____12171 = FStar_Syntax_Subst.compress r  in
                     uu____12171.FStar_Syntax_Syntax.n  in
                   let uu____12174 =
                     let uu____12175 = FStar_Syntax_Subst.compress msg  in
                     uu____12175.FStar_Syntax_Syntax.n  in
                   (uu____12170, uu____12174)  in
                 (match uu____12165 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12184))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____12195 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____12202)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____12237 when head_redex env head2 ->
                 let uu____12252 = whnf env phi1  in
                 encode_formula uu____12252 env
             | uu____12253 ->
                 let uu____12268 = encode_term phi1 env  in
                 (match uu____12268 with
                  | (tt,decls) ->
                      let tt1 =
                        let uu____12280 =
                          let uu____12282 =
                            FStar_Range.use_range
                              tt.FStar_SMTEncoding_Term.rng
                             in
                          let uu____12283 =
                            FStar_Range.use_range
                              phi1.FStar_Syntax_Syntax.pos
                             in
                          FStar_Range.rng_included uu____12282 uu____12283
                           in
                        if uu____12280
                        then tt
                        else
                          (let uu___372_12287 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___372_12287.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___372_12287.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      let uu____12288 = FStar_SMTEncoding_Term.mk_Valid tt1
                         in
                      (uu____12288, decls)))
        | uu____12289 ->
            let uu____12290 = encode_term phi1 env  in
            (match uu____12290 with
             | (tt,decls) ->
                 let tt1 =
                   let uu____12302 =
                     let uu____12304 =
                       FStar_Range.use_range tt.FStar_SMTEncoding_Term.rng
                        in
                     let uu____12305 =
                       FStar_Range.use_range phi1.FStar_Syntax_Syntax.pos  in
                     FStar_Range.rng_included uu____12304 uu____12305  in
                   if uu____12302
                   then tt
                   else
                     (let uu___373_12309 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___373_12309.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___373_12309.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 let uu____12310 = FStar_SMTEncoding_Term.mk_Valid tt1  in
                 (uu____12310, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____12354 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____12354 with
        | (vars,guards,env2,decls,uu____12393) ->
            let uu____12406 = encode_smt_patterns ps env2  in
            (match uu____12406 with
             | (pats,decls') ->
                 let uu____12449 = encode_formula body env2  in
                 (match uu____12449 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12481;
                             FStar_SMTEncoding_Term.rng = uu____12482;_}::[])::[]
                            when
                            let uu____12502 =
                              FStar_Ident.text_of_lid
                                FStar_Parser_Const.guard_free
                               in
                            uu____12502 = gf -> []
                        | uu____12505 -> guards  in
                      let uu____12510 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____12510, body1,
                        (FStar_List.append decls
                           (FStar_List.append decls' decls'')))))
         in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi  in
       let uu____12521 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____12521 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12530 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____12636  ->
                     match uu____12636 with
                     | (l,uu____12661) -> FStar_Ident.lid_equals op l))
              in
           (match uu____12530 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____12730,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____12822 = encode_q_body env vars pats body  in
             match uu____12822 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____12867 =
                     let uu____12878 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____12878)  in
                   FStar_SMTEncoding_Term.mkForall
                     phi1.FStar_Syntax_Syntax.pos uu____12867
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____12909 = encode_q_body env vars pats body  in
             match uu____12909 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____12953 =
                   let uu____12954 =
                     let uu____12965 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____12965)  in
                   FStar_SMTEncoding_Term.mkExists
                     phi1.FStar_Syntax_Syntax.pos uu____12954
                    in
                 (uu____12953, decls))))
