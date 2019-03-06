open Prims
let mkForall_fuel' :
  'Auu____67101 .
    Prims.string ->
      FStar_Range.range ->
        'Auu____67101 ->
          (FStar_SMTEncoding_Term.pat Prims.list Prims.list *
            FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term) ->
            FStar_SMTEncoding_Term.term
  =
  fun mname  ->
    fun r  ->
      fun n1  ->
        fun uu____67132  ->
          match uu____67132 with
          | (pats,vars,body) ->
              let fallback uu____67160 =
                FStar_SMTEncoding_Term.mkForall r (pats, vars, body)  in
              let uu____67165 = FStar_Options.unthrottle_inductives ()  in
              if uu____67165
              then fallback ()
              else
                (let uu____67170 =
                   FStar_SMTEncoding_Env.fresh_fvar mname "f"
                     FStar_SMTEncoding_Term.Fuel_sort
                    in
                 match uu____67170 with
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
                               | uu____67210 -> p))
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
                                 let uu____67231 = add_fuel1 guards  in
                                 FStar_SMTEncoding_Util.mk_and_l uu____67231
                             | uu____67234 ->
                                 let uu____67235 = add_fuel1 [guard]  in
                                 FStar_All.pipe_right uu____67235
                                   FStar_List.hd
                              in
                           FStar_SMTEncoding_Util.mkImp (guard1, body')
                       | uu____67240 -> body  in
                     let vars1 =
                       let uu____67252 =
                         FStar_SMTEncoding_Term.mk_fv
                           (fsym, FStar_SMTEncoding_Term.Fuel_sort)
                          in
                       uu____67252 :: vars  in
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
      | FStar_Syntax_Syntax.Tm_arrow uu____67316 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____67332 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____67340 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____67342 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____67356 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____67376 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____67379 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____67379 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____67398;
             FStar_Syntax_Syntax.vars = uu____67399;_},uu____67400)
          ->
          let uu____67425 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____67425 FStar_Option.isNone
      | uu____67443 -> false
  
let (head_redex :
  FStar_SMTEncoding_Env.env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____67457 =
        let uu____67458 = FStar_Syntax_Util.un_uinst t  in
        uu____67458.FStar_Syntax_Syntax.n  in
      match uu____67457 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____67462,uu____67463,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___630_67488  ->
                  match uu___630_67488 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____67491 -> false)
               rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____67494 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____67494 FStar_Option.isSome
      | uu____67512 -> false
  
let (whnf :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____67525 = head_normal env t  in
      if uu____67525
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
    let uu____67547 =
      let uu____67548 = FStar_Syntax_Syntax.null_binder t  in [uu____67548]
       in
    let uu____67567 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    FStar_Syntax_Util.abs uu____67547 uu____67567
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
                let uu____67589 = FStar_SMTEncoding_Term.fv_sort var  in
                match uu____67589 with
                | FStar_SMTEncoding_Term.Fuel_sort  ->
                    let uu____67590 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____67590
                | s ->
                    let uu____67593 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____67593) e)
  
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
          let uu____67649 =
            let uu____67655 =
              let uu____67657 = FStar_Util.string_of_int arity  in
              let uu____67659 = FStar_Util.string_of_int n_args  in
              FStar_Util.format3
                "Head symbol %s expects at least %s arguments; got only %s"
                head1 uu____67657 uu____67659
               in
            (FStar_Errors.Fatal_SMTEncodingArityMismatch, uu____67655)  in
          FStar_Errors.raise_error uu____67649 rng
  
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
                  (let uu____67708 = FStar_Util.first_N arity args  in
                   match uu____67708 with
                   | (args1,rest) ->
                       let head3 =
                         FStar_SMTEncoding_Util.mkApp' (head2, args1)  in
                       mk_Apply_args head3 rest)
                else
                  (let uu____67732 =
                     FStar_SMTEncoding_Term.op_to_string head2  in
                   raise_arity_mismatch uu____67732 arity n_args rng)
  
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
          let uu____67755 = FStar_SMTEncoding_Env.force_thunk fvb  in
          mk_Apply_args uu____67755 args
        else
          maybe_curry_app rng
            (FStar_Util.Inl
               (FStar_SMTEncoding_Term.Var (fvb.FStar_SMTEncoding_Env.smt_id)))
            fvb.FStar_SMTEncoding_Env.smt_arity args
  
let (is_app : FStar_SMTEncoding_Term.op -> Prims.bool) =
  fun uu___631_67764  ->
    match uu___631_67764 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____67770 -> false
  
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
                       FStar_SMTEncoding_Term.freevars = uu____67818;
                       FStar_SMTEncoding_Term.rng = uu____67819;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____67850) ->
              let uu____67860 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____67877 -> false) args (FStar_List.rev xs))
                 in
              if uu____67860
              then FStar_SMTEncoding_Env.tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____67884,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t  in
              let uu____67888 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____67896 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars
                           in
                        Prims.op_Negation uu____67896))
                 in
              if uu____67888
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____67903 -> FStar_Pervasives_Native.None  in
        check_partial_applications body (FStar_List.rev vars)
  
let check_pattern_vars :
  'Auu____67921 'Auu____67922 .
    FStar_SMTEncoding_Env.env_t ->
      (FStar_Syntax_Syntax.bv * 'Auu____67921) Prims.list ->
        (FStar_Syntax_Syntax.term * 'Auu____67922) Prims.list -> unit
  =
  fun env  ->
    fun vars  ->
      fun pats  ->
        let pats1 =
          FStar_All.pipe_right pats
            (FStar_List.map
               (fun uu____67980  ->
                  match uu____67980 with
                  | (x,uu____67986) ->
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
              let uu____67994 = FStar_Syntax_Free.names hd1  in
              FStar_List.fold_left
                (fun out  ->
                   fun x  ->
                     let uu____68006 = FStar_Syntax_Free.names x  in
                     FStar_Util.set_union out uu____68006) uu____67994 tl1
               in
            let uu____68009 =
              FStar_All.pipe_right vars
                (FStar_Util.find_opt
                   (fun uu____68036  ->
                      match uu____68036 with
                      | (b,uu____68043) ->
                          let uu____68044 = FStar_Util.set_mem b pat_vars  in
                          Prims.op_Negation uu____68044))
               in
            (match uu____68009 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some (x,uu____68051) ->
                 let pos =
                   FStar_List.fold_left
                     (fun out  ->
                        fun t  ->
                          FStar_Range.union_ranges out
                            t.FStar_Syntax_Syntax.pos)
                     hd1.FStar_Syntax_Syntax.pos tl1
                    in
                 let uu____68065 =
                   let uu____68071 =
                     let uu____68073 = FStar_Syntax_Print.bv_to_string x  in
                     FStar_Util.format1
                       "SMT pattern misses at least one bound variable: %s"
                       uu____68073
                      in
                   (FStar_Errors.Warning_SMTPatternIllFormed, uu____68071)
                    in
                 FStar_Errors.log_issue pos uu____68065)
  
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
        | FStar_Syntax_Syntax.Tm_arrow uu____68359 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____68374 ->
            let uu____68381 = FStar_Syntax_Util.unrefine t1  in
            aux true uu____68381
        | uu____68383 ->
            if norm1
            then let uu____68385 = whnf env t1  in aux false uu____68385
            else
              (let uu____68389 =
                 let uu____68391 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let uu____68393 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____68391 uu____68393
                  in
               failwith uu____68389)
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
    | FStar_Syntax_Syntax.Tm_refine (bv,uu____68435) ->
        let uu____68440 =
          curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort  in
        (match uu____68440 with
         | (args,res) ->
             (match args with
              | [] ->
                  let uu____68461 = FStar_Syntax_Syntax.mk_Total k1  in
                  ([], uu____68461)
              | uu____68468 -> (args, res)))
    | uu____68469 ->
        let uu____68470 = FStar_Syntax_Syntax.mk_Total k1  in
        ([], uu____68470)
  
let is_arithmetic_primitive :
  'Auu____68484 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____68484 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____68507::uu____68508::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____68512::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____68515 -> false
  
let (isInteger : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____68546 -> false
  
let (getInteger : FStar_Syntax_Syntax.term' -> Prims.int) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____68569 -> failwith "Expected an Integer term"
  
let is_BitVector_primitive :
  'Auu____68579 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____68579)
        Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____68621)::uu____68622::uu____68623::[]) ->
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
         fv,(sz_arg,uu____68674)::uu____68675::[]) ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____68712 -> false
  
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
          let uu____69036 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue  in
          (uu____69036, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____69038 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse  in
          (uu____69038, [])
      | FStar_Const.Const_char c1 ->
          let uu____69041 =
            let uu____69042 =
              let uu____69050 =
                let uu____69053 =
                  let uu____69054 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1)
                     in
                  FStar_SMTEncoding_Term.boxInt uu____69054  in
                [uu____69053]  in
              ("FStar.Char.__char_of_int", uu____69050)  in
            FStar_SMTEncoding_Util.mkApp uu____69042  in
          (uu____69041, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____69072 =
            let uu____69073 = FStar_SMTEncoding_Util.mkInteger i  in
            FStar_SMTEncoding_Term.boxInt uu____69073  in
          (uu____69072, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.FStar_SMTEncoding_Env.tcenv).FStar_TypeChecker_Env.dsenv
              repr sw FStar_Range.dummyRange
             in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____69094) ->
          let uu____69097 =
            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.string_const s
             in
          (uu____69097, [])
      | FStar_Const.Const_range uu____69098 ->
          let uu____69099 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          (uu____69099, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | FStar_Const.Const_real r ->
          let uu____69102 =
            let uu____69103 = FStar_SMTEncoding_Util.mkReal r  in
            FStar_SMTEncoding_Term.boxReal uu____69103  in
          (uu____69102, [])
      | c1 ->
          let uu____69105 =
            let uu____69107 = FStar_Syntax_Print.const_to_string c1  in
            FStar_Util.format1 "Unhandled constant: %s" uu____69107  in
          failwith uu____69105

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
        (let uu____69136 =
           FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
             FStar_Options.Medium
            in
         if uu____69136
         then
           let uu____69139 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____69139
         else ());
        (let uu____69145 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____69227  ->
                   fun b  ->
                     match uu____69227 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____69292 =
                           let x = FStar_Pervasives_Native.fst b  in
                           let uu____69308 =
                             FStar_SMTEncoding_Env.gen_term_var env1 x  in
                           match uu____69308 with
                           | (xxsym,xx,env') ->
                               let uu____69333 =
                                 let uu____69338 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____69338 env1
                                   xx
                                  in
                               (match uu____69333 with
                                | (guard_x_t,decls') ->
                                    let uu____69353 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xxsym,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    (uu____69353, guard_x_t, env', decls', x))
                            in
                         (match uu____69292 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____69145 with
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
          let uu____69453 = encode_term t env  in
          match uu____69453 with
          | (t1,decls) ->
              let uu____69464 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____69464, decls)

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
          let uu____69475 = encode_term t env  in
          match uu____69475 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____69490 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____69490, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____69492 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____69492, decls))

and (encode_arith_term :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____69498 = encode_args args_e env  in
        match uu____69498 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____69517 -> failwith "Impossible"  in
            let unary unbox arg_tms1 =
              let uu____69539 = FStar_List.hd arg_tms1  in unbox uu____69539
               in
            let binary unbox arg_tms1 =
              let uu____69564 =
                let uu____69565 = FStar_List.hd arg_tms1  in
                unbox uu____69565  in
              let uu____69566 =
                let uu____69567 =
                  let uu____69568 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____69568  in
                unbox uu____69567  in
              (uu____69564, uu____69566)  in
            let mk_default uu____69576 =
              let uu____69577 =
                FStar_SMTEncoding_Env.lookup_free_var_sym env
                  head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____69577 with
              | (fname,fuel_args,arity) ->
                  let args = FStar_List.append fuel_args arg_tms  in
                  maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity
                    args
               in
            let mk_l box op mk_args ts =
              let uu____69666 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____69666
              then
                let uu____69669 =
                  let uu____69670 = mk_args ts  in op uu____69670  in
                FStar_All.pipe_right uu____69669 box
              else mk_default ()  in
            let mk_nl box unbox nm op ts =
              let uu____69728 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____69728
              then
                let uu____69731 = binary unbox ts  in
                match uu____69731 with
                | (t1,t2) ->
                    let uu____69738 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____69738 box
              else
                (let uu____69744 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____69744
                 then
                   let uu____69747 =
                     let uu____69748 = binary unbox ts  in op uu____69748  in
                   FStar_All.pipe_right uu____69747 box
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
            let uu____70183 =
              let uu____70193 =
                FStar_List.tryFind
                  (fun uu____70217  ->
                     match uu____70217 with
                     | (l,uu____70228) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____70193 FStar_Util.must  in
            (match uu____70183 with
             | (uu____70272,op) ->
                 let uu____70284 = op arg_tms  in (uu____70284, decls))

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
        let uu____70300 = FStar_List.hd args_e  in
        match uu____70300 with
        | (tm_sz,uu____70316) ->
            let uu____70325 = uu____70300  in
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let t_decls1 = FStar_SMTEncoding_Term.mkBvConstructor sz  in
              FStar_SMTEncoding_Term.mk_decls "" sz_key t_decls1 []  in
            let uu____70336 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____70362::(sz_arg,uu____70364)::uu____70365::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____70432 =
                    let uu____70433 = FStar_List.tail args_e  in
                    FStar_List.tail uu____70433  in
                  let uu____70460 =
                    let uu____70464 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____70464  in
                  (uu____70432, uu____70460)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____70471::(sz_arg,uu____70473)::uu____70474::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____70541 =
                    let uu____70543 =
                      FStar_Syntax_Print.term_to_string sz_arg  in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____70543
                     in
                  failwith uu____70541
              | uu____70553 ->
                  let uu____70568 = FStar_List.tail args_e  in
                  (uu____70568, FStar_Pervasives_Native.None)
               in
            (match uu____70336 with
             | (arg_tms,ext_sz) ->
                 let uu____70595 = encode_args arg_tms env  in
                 (match uu____70595 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____70616 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____70628 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____70628  in
                      let unary_arith arg_tms2 =
                        let uu____70639 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____70639  in
                      let binary arg_tms2 =
                        let uu____70654 =
                          let uu____70655 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____70655
                           in
                        let uu____70656 =
                          let uu____70657 =
                            let uu____70658 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____70658  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____70657
                           in
                        (uu____70654, uu____70656)  in
                      let binary_arith arg_tms2 =
                        let uu____70675 =
                          let uu____70676 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____70676
                           in
                        let uu____70677 =
                          let uu____70678 =
                            let uu____70679 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____70679  in
                          FStar_SMTEncoding_Term.unboxInt uu____70678  in
                        (uu____70675, uu____70677)  in
                      let mk_bv op mk_args resBox ts =
                        let uu____70737 =
                          let uu____70738 = mk_args ts  in op uu____70738  in
                        FStar_All.pipe_right uu____70737 resBox  in
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
                        let uu____70870 =
                          let uu____70875 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____70875  in
                        let uu____70884 =
                          let uu____70889 =
                            let uu____70891 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____70891  in
                          FStar_SMTEncoding_Term.boxBitVec uu____70889  in
                        mk_bv uu____70870 unary uu____70884 arg_tms2  in
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
                      let uu____71131 =
                        let uu____71141 =
                          FStar_List.tryFind
                            (fun uu____71165  ->
                               match uu____71165 with
                               | (l,uu____71176) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____71141 FStar_Util.must  in
                      (match uu____71131 with
                       | (uu____71222,op) ->
                           let uu____71234 = op arg_tms1  in
                           (uu____71234, (FStar_List.append sz_decls decls)))))

and (encode_deeply_embedded_quantifier :
  FStar_Syntax_Syntax.term ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let env1 =
        let uu___1170_71244 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___1170_71244.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___1170_71244.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___1170_71244.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___1170_71244.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___1170_71244.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___1170_71244.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name =
            (uu___1170_71244.FStar_SMTEncoding_Env.use_zfuel_name);
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___1170_71244.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___1170_71244.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier = true;
          FStar_SMTEncoding_Env.global_cache =
            (uu___1170_71244.FStar_SMTEncoding_Env.global_cache)
        }  in
      let uu____71246 = encode_term t env1  in
      match uu____71246 with
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
               (uu____71272,{
                              FStar_SMTEncoding_Term.tm =
                                FStar_SMTEncoding_Term.FreeV uu____71273;
                              FStar_SMTEncoding_Term.freevars = uu____71274;
                              FStar_SMTEncoding_Term.rng = uu____71275;_}::
                {
                  FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV
                    uu____71276;
                  FStar_SMTEncoding_Term.freevars = uu____71277;
                  FStar_SMTEncoding_Term.rng = uu____71278;_}::[])
               ->
               (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                  (FStar_Errors.Warning_QuantifierWithoutPattern,
                    "Not encoding deeply embedded, unguarded quantifier to SMT");
                (tm, decls))
           | uu____71324 ->
               let uu____71325 = encode_formula t env1  in
               (match uu____71325 with
                | (phi,decls') ->
                    let interp =
                      match vars with
                      | [] ->
                          let uu____71345 =
                            let uu____71350 =
                              FStar_SMTEncoding_Term.mk_Valid tm  in
                            (uu____71350, phi)  in
                          FStar_SMTEncoding_Util.mkIff uu____71345
                      | uu____71351 ->
                          let uu____71352 =
                            let uu____71363 =
                              let uu____71364 =
                                let uu____71369 =
                                  FStar_SMTEncoding_Term.mk_Valid tm  in
                                (uu____71369, phi)  in
                              FStar_SMTEncoding_Util.mkIff uu____71364  in
                            ([[valid_tm]], vars, uu____71363)  in
                          FStar_SMTEncoding_Term.mkForall
                            t.FStar_Syntax_Syntax.pos uu____71352
                       in
                    let ax =
                      let uu____71379 =
                        let uu____71387 =
                          let uu____71389 =
                            FStar_Util.digest_of_string tkey_hash  in
                          Prims.op_Hat "l_quant_interp_" uu____71389  in
                        (interp,
                          (FStar_Pervasives_Native.Some
                             "Interpretation of deeply embedded quantifier"),
                          uu____71387)
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____71379  in
                    let uu____71395 =
                      let uu____71396 =
                        let uu____71399 =
                          FStar_SMTEncoding_Term.mk_decls "" tkey_hash 
                            [ax] (FStar_List.append decls decls')
                           in
                        FStar_List.append decls' uu____71399  in
                      FStar_List.append decls uu____71396  in
                    (tm, uu____71395)))

and (encode_term :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____71411 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____71411
       then
         let uu____71416 = FStar_Syntax_Print.tag_of_term t  in
         let uu____71418 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____71420 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____71416 uu____71418
           uu____71420
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____71429 ->
           let uu____71452 =
             let uu____71454 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____71457 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____71459 = FStar_Syntax_Print.term_to_string t0  in
             let uu____71461 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____71454
               uu____71457 uu____71459 uu____71461
              in
           failwith uu____71452
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____71468 =
             let uu____71470 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____71473 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____71475 = FStar_Syntax_Print.term_to_string t0  in
             let uu____71477 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____71470
               uu____71473 uu____71475 uu____71477
              in
           failwith uu____71468
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let e = FStar_Syntax_Util.unfold_lazy i  in
           ((let uu____71487 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____71487
             then
               let uu____71492 = FStar_Syntax_Print.term_to_string t0  in
               let uu____71494 = FStar_Syntax_Print.term_to_string e  in
               FStar_Util.print2 ">> Unfolded (%s) ~> (%s)\n" uu____71492
                 uu____71494
             else ());
            encode_term e env)
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____71500 =
             let uu____71502 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____71502
              in
           failwith uu____71500
       | FStar_Syntax_Syntax.Tm_ascribed (t1,(k,uu____71511),uu____71512) ->
           let uu____71561 =
             match k with
             | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
             | uu____71571 -> false  in
           if uu____71561
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t1 env
       | FStar_Syntax_Syntax.Tm_quoted (qt,uu____71589) ->
           let tv =
             let uu____71595 =
               let uu____71602 = FStar_Reflection_Basic.inspect_ln qt  in
               FStar_Syntax_Embeddings.embed
                 FStar_Reflection_Embeddings.e_term_view uu____71602
                in
             uu____71595 t.FStar_Syntax_Syntax.pos
               FStar_Pervasives_Native.None
               FStar_Syntax_Embeddings.id_norm_cb
              in
           ((let uu____71606 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____71606
             then
               let uu____71611 = FStar_Syntax_Print.term_to_string t0  in
               let uu____71613 = FStar_Syntax_Print.term_to_string tv  in
               FStar_Util.print2 ">> Inspected (%s) ~> (%s)\n" uu____71611
                 uu____71613
             else ());
            (let t1 =
               let uu____71621 =
                 let uu____71632 = FStar_Syntax_Syntax.as_arg tv  in
                 [uu____71632]  in
               FStar_Syntax_Util.mk_app
                 (FStar_Reflection_Data.refl_constant_term
                    FStar_Reflection_Data.fstar_refl_pack_ln) uu____71621
                in
             encode_term t1 env))
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_pattern uu____71658) ->
           encode_term t1
             (let uu___1242_71676 = env  in
              {
                FStar_SMTEncoding_Env.bvar_bindings =
                  (uu___1242_71676.FStar_SMTEncoding_Env.bvar_bindings);
                FStar_SMTEncoding_Env.fvar_bindings =
                  (uu___1242_71676.FStar_SMTEncoding_Env.fvar_bindings);
                FStar_SMTEncoding_Env.depth =
                  (uu___1242_71676.FStar_SMTEncoding_Env.depth);
                FStar_SMTEncoding_Env.tcenv =
                  (uu___1242_71676.FStar_SMTEncoding_Env.tcenv);
                FStar_SMTEncoding_Env.warn =
                  (uu___1242_71676.FStar_SMTEncoding_Env.warn);
                FStar_SMTEncoding_Env.nolabels =
                  (uu___1242_71676.FStar_SMTEncoding_Env.nolabels);
                FStar_SMTEncoding_Env.use_zfuel_name =
                  (uu___1242_71676.FStar_SMTEncoding_Env.use_zfuel_name);
                FStar_SMTEncoding_Env.encode_non_total_function_typ =
                  (uu___1242_71676.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                FStar_SMTEncoding_Env.current_module_name =
                  (uu___1242_71676.FStar_SMTEncoding_Env.current_module_name);
                FStar_SMTEncoding_Env.encoding_quantifier = false;
                FStar_SMTEncoding_Env.global_cache =
                  (uu___1242_71676.FStar_SMTEncoding_Env.global_cache)
              })
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____71679) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = FStar_SMTEncoding_Env.lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____71687 = head_redex env t  in
           if uu____71687
           then let uu____71694 = whnf env t  in encode_term uu____71694 env
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
              let uu____71701 =
                if
                  fvb.FStar_SMTEncoding_Env.smt_arity > (Prims.parse_int "0")
                then
                  match tok.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.FreeV uu____71725 ->
                      let sym_name =
                        let uu____71736 =
                          FStar_Util.digest_of_string tkey_hash  in
                        Prims.op_Hat "@kick_partial_app_" uu____71736  in
                      let uu____71739 =
                        let uu____71742 =
                          let uu____71743 =
                            let uu____71751 =
                              FStar_SMTEncoding_Term.kick_partial_app tok  in
                            (uu____71751,
                              (FStar_Pervasives_Native.Some
                                 "kick_partial_app"), sym_name)
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____71743  in
                        [uu____71742]  in
                      (uu____71739, sym_name)
                  | FStar_SMTEncoding_Term.App (uu____71758,[]) ->
                      let sym_name =
                        let uu____71763 =
                          FStar_Util.digest_of_string tkey_hash  in
                        Prims.op_Hat "@kick_partial_app_" uu____71763  in
                      let uu____71766 =
                        let uu____71769 =
                          let uu____71770 =
                            let uu____71778 =
                              FStar_SMTEncoding_Term.kick_partial_app tok  in
                            (uu____71778,
                              (FStar_Pervasives_Native.Some
                                 "kick_partial_app"), sym_name)
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____71770  in
                        [uu____71769]  in
                      (uu____71766, sym_name)
                  | uu____71785 -> ([], "")
                else ([], "")  in
              match uu____71701 with
              | (aux_decls,sym_name) ->
                  let uu____71808 =
                    if aux_decls = []
                    then
                      FStar_All.pipe_right []
                        FStar_SMTEncoding_Term.mk_decls_trivial
                    else
                      FStar_SMTEncoding_Term.mk_decls sym_name tkey_hash
                        aux_decls []
                     in
                  (tok, uu____71808))
       | FStar_Syntax_Syntax.Tm_type uu____71816 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____71818) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.FStar_SMTEncoding_Env.current_module_name
              in
           let uu____71848 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____71848 with
            | (binders1,res) ->
                let uu____71859 =
                  (env.FStar_SMTEncoding_Env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____71859
                then
                  let uu____71866 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____71866 with
                   | (vars,guards,env',decls,uu____71891) ->
                       let fsym =
                         let uu____71905 =
                           let uu____71911 =
                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                               module_name "f"
                              in
                           (uu____71911, FStar_SMTEncoding_Term.Term_sort)
                            in
                         FStar_SMTEncoding_Term.mk_fv uu____71905  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____71917 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___1296_71926 =
                              env.FStar_SMTEncoding_Env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___1296_71926.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___1296_71926.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___1296_71926.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___1296_71926.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___1296_71926.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___1296_71926.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___1296_71926.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___1296_71926.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___1296_71926.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___1296_71926.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___1296_71926.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___1296_71926.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___1296_71926.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___1296_71926.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___1296_71926.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___1296_71926.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___1296_71926.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___1296_71926.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___1296_71926.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___1296_71926.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___1296_71926.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___1296_71926.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___1296_71926.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___1296_71926.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___1296_71926.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___1296_71926.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___1296_71926.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___1296_71926.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___1296_71926.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___1296_71926.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___1296_71926.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___1296_71926.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___1296_71926.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___1296_71926.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___1296_71926.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___1296_71926.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___1296_71926.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___1296_71926.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___1296_71926.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___1296_71926.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___1296_71926.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___1296_71926.FStar_TypeChecker_Env.nbe)
                            }) res
                          in
                       (match uu____71917 with
                        | (pre_opt,res_t) ->
                            let uu____71938 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____71938 with
                             | (res_pred,decls') ->
                                 let uu____71949 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____71962 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____71962, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____71966 =
                                         encode_formula pre env'  in
                                       (match uu____71966 with
                                        | (guard,decls0) ->
                                            let uu____71979 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____71979, decls0))
                                    in
                                 (match uu____71949 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____71993 =
                                          let uu____72004 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____72004)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t.FStar_Syntax_Syntax.pos
                                          uu____71993
                                         in
                                      let cvars =
                                        let uu____72024 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____72024
                                          (FStar_List.filter
                                             (fun x  ->
                                                let uu____72043 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    x
                                                   in
                                                let uu____72045 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    fsym
                                                   in
                                                uu____72043 <> uu____72045))
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
                                        let uu____72067 =
                                          FStar_Util.digest_of_string
                                            tkey_hash
                                           in
                                        Prims.op_Hat "Tm_arrow_" uu____72067
                                         in
                                      let cvar_sorts =
                                        FStar_List.map
                                          FStar_SMTEncoding_Term.fv_sort
                                          cvars
                                         in
                                      let caption =
                                        let uu____72082 =
                                          FStar_Options.log_queries ()  in
                                        if uu____72082
                                        then
                                          let uu____72085 =
                                            let uu____72087 =
                                              FStar_TypeChecker_Normalize.term_to_string
                                                env.FStar_SMTEncoding_Env.tcenv
                                                t0
                                               in
                                            FStar_Util.replace_char
                                              uu____72087 10 32
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____72085
                                        else FStar_Pervasives_Native.None  in
                                      let tdecl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (tsym, cvar_sorts,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            caption)
                                         in
                                      let t1 =
                                        let uu____72100 =
                                          let uu____72108 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              cvars
                                             in
                                          (tsym, uu____72108)  in
                                        FStar_SMTEncoding_Util.mkApp
                                          uu____72100
                                         in
                                      let t_has_kind =
                                        FStar_SMTEncoding_Term.mk_HasType t1
                                          FStar_SMTEncoding_Term.mk_Term_type
                                         in
                                      let k_assumption =
                                        let a_name =
                                          Prims.op_Hat "kinding_" tsym  in
                                        let uu____72127 =
                                          let uu____72135 =
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              ([[t_has_kind]], cvars,
                                                t_has_kind)
                                             in
                                          (uu____72135,
                                            (FStar_Pervasives_Native.Some
                                               a_name), a_name)
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____72127
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
                                        let uu____72152 =
                                          let uu____72160 =
                                            let uu____72161 =
                                              let uu____72172 =
                                                let uu____72173 =
                                                  let uu____72178 =
                                                    let uu____72179 =
                                                      FStar_SMTEncoding_Term.mk_PreType
                                                        f
                                                       in
                                                    FStar_SMTEncoding_Term.mk_tester
                                                      "Tm_arrow" uu____72179
                                                     in
                                                  (f_has_t, uu____72178)  in
                                                FStar_SMTEncoding_Util.mkImp
                                                  uu____72173
                                                 in
                                              ([[f_has_t]], (fsym :: cvars),
                                                uu____72172)
                                               in
                                            let uu____72197 =
                                              mkForall_fuel module_name
                                                t0.FStar_Syntax_Syntax.pos
                                               in
                                            uu____72197 uu____72161  in
                                          (uu____72160,
                                            (FStar_Pervasives_Native.Some
                                               "pre-typing for functions"),
                                            (Prims.op_Hat module_name
                                               (Prims.op_Hat "_" a_name)))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____72152
                                         in
                                      let t_interp1 =
                                        let a_name =
                                          Prims.op_Hat "interpretation_" tsym
                                           in
                                        let uu____72220 =
                                          let uu____72228 =
                                            let uu____72229 =
                                              let uu____72240 =
                                                FStar_SMTEncoding_Util.mkIff
                                                  (f_has_t_z, t_interp)
                                                 in
                                              ([[f_has_t_z]], (fsym ::
                                                cvars), uu____72240)
                                               in
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              uu____72229
                                             in
                                          (uu____72228,
                                            (FStar_Pervasives_Native.Some
                                               a_name),
                                            (Prims.op_Hat module_name
                                               (Prims.op_Hat "_" a_name)))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____72220
                                         in
                                      let t_decls1 =
                                        [tdecl;
                                        k_assumption;
                                        pre_typing;
                                        t_interp1]  in
                                      let uu____72263 =
                                        let uu____72264 =
                                          let uu____72267 =
                                            let uu____72270 =
                                              FStar_SMTEncoding_Term.mk_decls
                                                tsym tkey_hash t_decls1
                                                (FStar_List.append decls
                                                   (FStar_List.append decls'
                                                      guard_decls))
                                               in
                                            FStar_List.append guard_decls
                                              uu____72270
                                             in
                                          FStar_List.append decls'
                                            uu____72267
                                           in
                                        FStar_List.append decls uu____72264
                                         in
                                      (t1, uu____72263)))))
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
                     let uu____72291 =
                       let uu____72299 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____72299,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"), a_name)
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____72291  in
                   let fsym =
                     FStar_SMTEncoding_Term.mk_fv
                       ("f", FStar_SMTEncoding_Term.Term_sort)
                      in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.op_Hat "pre_typing_" tsym  in
                     let uu____72312 =
                       let uu____72320 =
                         let uu____72321 =
                           let uu____72332 =
                             let uu____72333 =
                               let uu____72338 =
                                 let uu____72339 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____72339
                                  in
                               (f_has_t, uu____72338)  in
                             FStar_SMTEncoding_Util.mkImp uu____72333  in
                           ([[f_has_t]], [fsym], uu____72332)  in
                         let uu____72365 =
                           mkForall_fuel module_name
                             t0.FStar_Syntax_Syntax.pos
                            in
                         uu____72365 uu____72321  in
                       (uu____72320, (FStar_Pervasives_Native.Some a_name),
                         a_name)
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____72312  in
                   let uu____72382 =
                     FStar_All.pipe_right [tdecl; t_kinding; t_interp]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                      in
                   (t1, uu____72382)))
       | FStar_Syntax_Syntax.Tm_refine uu____72385 ->
           let uu____72392 =
             let uu____72397 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Env.Weak;
                 FStar_TypeChecker_Env.HNF;
                 FStar_TypeChecker_Env.EraseUniverses]
                 env.FStar_SMTEncoding_Env.tcenv t0
                in
             match uu____72397 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____72404;
                 FStar_Syntax_Syntax.vars = uu____72405;_} ->
                 let uu____72412 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____72412 with
                  | (b,f1) ->
                      let uu____72437 =
                        let uu____72438 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____72438  in
                      (uu____72437, f1))
             | uu____72453 -> failwith "impossible"  in
           (match uu____72392 with
            | (x,f) ->
                let uu____72465 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____72465 with
                 | (base_t,decls) ->
                     let uu____72476 =
                       FStar_SMTEncoding_Env.gen_term_var env x  in
                     (match uu____72476 with
                      | (x1,xtm,env') ->
                          let uu____72493 = encode_formula f env'  in
                          (match uu____72493 with
                           | (refinement,decls') ->
                               let uu____72504 =
                                 FStar_SMTEncoding_Env.fresh_fvar
                                   env.FStar_SMTEncoding_Env.current_module_name
                                   "f" FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____72504 with
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
                                      let uu____72532 =
                                        let uu____72543 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____72554 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____72543
                                          uu____72554
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____72532
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun y  ->
                                              (let uu____72608 =
                                                 FStar_SMTEncoding_Term.fv_name
                                                   y
                                                  in
                                               uu____72608 <> x1) &&
                                                (let uu____72612 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     y
                                                    in
                                                 uu____72612 <> fsym)))
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
                                      let uu____72648 =
                                        FStar_Util.digest_of_string tkey_hash
                                         in
                                      Prims.op_Hat "Tm_refine_" uu____72648
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
                                      let uu____72668 =
                                        let uu____72676 =
                                          FStar_List.map
                                            FStar_SMTEncoding_Util.mkFreeV
                                            cvars1
                                           in
                                        (tsym, uu____72676)  in
                                      FStar_SMTEncoding_Util.mkApp
                                        uu____72668
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
                                      let uu____72696 =
                                        let uu____72704 =
                                          let uu____72705 =
                                            let uu____72716 =
                                              FStar_SMTEncoding_Util.mkIff
                                                (t_haseq_ref, t_haseq_base)
                                               in
                                            ([[t_haseq_ref]], cvars1,
                                              uu____72716)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            t0.FStar_Syntax_Syntax.pos
                                            uu____72705
                                           in
                                        (uu____72704,
                                          (FStar_Pervasives_Native.Some
                                             (Prims.op_Hat "haseq for " tsym)),
                                          (Prims.op_Hat "haseq" tsym))
                                         in
                                      FStar_SMTEncoding_Util.mkAssume
                                        uu____72696
                                       in
                                    let t_kinding =
                                      let uu____72730 =
                                        let uu____72738 =
                                          FStar_SMTEncoding_Term.mkForall
                                            t0.FStar_Syntax_Syntax.pos
                                            ([[t_has_kind]], cvars1,
                                              t_has_kind)
                                           in
                                        (uu____72738,
                                          (FStar_Pervasives_Native.Some
                                             "refinement kinding"),
                                          (Prims.op_Hat "refinement_kinding_"
                                             tsym))
                                         in
                                      FStar_SMTEncoding_Util.mkAssume
                                        uu____72730
                                       in
                                    let t_interp =
                                      let uu____72752 =
                                        let uu____72760 =
                                          let uu____72761 =
                                            let uu____72772 =
                                              FStar_SMTEncoding_Util.mkIff
                                                (x_has_t, encoding)
                                               in
                                            ([[x_has_t]], (ffv :: xfv ::
                                              cvars1), uu____72772)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            t0.FStar_Syntax_Syntax.pos
                                            uu____72761
                                           in
                                        (uu____72760,
                                          (FStar_Pervasives_Native.Some
                                             "refinement_interpretation"),
                                          (Prims.op_Hat
                                             "refinement_interpretation_"
                                             tsym))
                                         in
                                      FStar_SMTEncoding_Util.mkAssume
                                        uu____72752
                                       in
                                    let t_decls1 =
                                      [tdecl; t_kinding; t_interp; t_haseq1]
                                       in
                                    let uu____72804 =
                                      let uu____72805 =
                                        let uu____72808 =
                                          FStar_SMTEncoding_Term.mk_decls
                                            tsym tkey_hash t_decls1
                                            (FStar_List.append decls decls')
                                           in
                                        FStar_List.append decls' uu____72808
                                         in
                                      FStar_List.append decls uu____72805  in
                                    (t1, uu____72804))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,uu____72812) ->
           let ttm =
             let uu____72830 =
               FStar_Syntax_Unionfind.uvar_id
                 uv.FStar_Syntax_Syntax.ctx_uvar_head
                in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____72830  in
           let uu____72832 =
             encode_term_pred FStar_Pervasives_Native.None
               uv.FStar_Syntax_Syntax.ctx_uvar_typ env ttm
              in
           (match uu____72832 with
            | (t_has_k,decls) ->
                let d =
                  let uu____72844 =
                    let uu____72852 =
                      let uu____72854 =
                        let uu____72856 =
                          let uu____72858 =
                            FStar_Syntax_Unionfind.uvar_id
                              uv.FStar_Syntax_Syntax.ctx_uvar_head
                             in
                          FStar_Util.string_of_int uu____72858  in
                        FStar_Util.format1 "uvar_typing_%s" uu____72856  in
                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                        uu____72854
                       in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____72852)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____72844  in
                let uu____72864 =
                  let uu____72865 =
                    FStar_All.pipe_right [d]
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append decls uu____72865  in
                (ttm, uu____72864))
       | FStar_Syntax_Syntax.Tm_app uu____72872 ->
           let uu____72889 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____72889 with
            | (head1,args_e) ->
                let uu____72936 =
                  let uu____72951 =
                    let uu____72952 = FStar_Syntax_Subst.compress head1  in
                    uu____72952.FStar_Syntax_Syntax.n  in
                  (uu____72951, args_e)  in
                (match uu____72936 with
                 | uu____72969 when head_redex env head1 ->
                     let uu____72984 = whnf env t  in
                     encode_term uu____72984 env
                 | uu____72985 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____73008 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_fvar fv,uu____73026) when
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
                       FStar_Syntax_Syntax.pos = uu____73048;
                       FStar_Syntax_Syntax.vars = uu____73049;_},uu____73050),uu____73051)
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
                       FStar_Syntax_Syntax.pos = uu____73077;
                       FStar_Syntax_Syntax.vars = uu____73078;_},uu____73079),
                    (v0,uu____73081)::(v1,uu____73083)::(v2,uu____73085)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____73156 = encode_term v0 env  in
                     (match uu____73156 with
                      | (v01,decls0) ->
                          let uu____73167 = encode_term v1 env  in
                          (match uu____73167 with
                           | (v11,decls1) ->
                               let uu____73178 = encode_term v2 env  in
                               (match uu____73178 with
                                | (v21,decls2) ->
                                    let uu____73189 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____73189,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(v0,uu____73192)::(v1,uu____73194)::(v2,uu____73196)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____73263 = encode_term v0 env  in
                     (match uu____73263 with
                      | (v01,decls0) ->
                          let uu____73274 = encode_term v1 env  in
                          (match uu____73274 with
                           | (v11,decls1) ->
                               let uu____73285 = encode_term v2 env  in
                               (match uu____73285 with
                                | (v21,decls2) ->
                                    let uu____73296 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____73296,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____73298)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____73334)::(rng,uu____73336)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____73387) ->
                     let e0 =
                       let uu____73409 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg
                         env.FStar_SMTEncoding_Env.tcenv head1 uu____73409
                        in
                     ((let uu____73419 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug
                              env.FStar_SMTEncoding_Env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____73419
                       then
                         let uu____73424 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____73424
                       else ());
                      (let e =
                         let uu____73432 =
                           let uu____73437 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____73438 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____73437
                             uu____73438
                            in
                         uu____73432 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____73447),(arg,uu____73449)::[]) ->
                     encode_term arg env
                 | uu____73484 ->
                     let uu____73499 = encode_args args_e env  in
                     (match uu____73499 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____73560 = encode_term head1 env  in
                            match uu____73560 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____73632 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____73632 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____73730  ->
                                                 fun uu____73731  ->
                                                   match (uu____73730,
                                                           uu____73731)
                                                   with
                                                   | ((bv,uu____73761),
                                                      (a,uu____73763)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____73793 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____73793
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____73794 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm
                                             in
                                          (match uu____73794 with
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
                                                 let uu____73811 =
                                                   let uu____73819 =
                                                     FStar_SMTEncoding_Term.mkForall
                                                       t0.FStar_Syntax_Syntax.pos
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____73828 =
                                                     let uu____73830 =
                                                       let uu____73832 =
                                                         FStar_SMTEncoding_Term.hash_of_term
                                                           app_tm
                                                          in
                                                       FStar_Util.digest_of_string
                                                         uu____73832
                                                        in
                                                     Prims.op_Hat
                                                       "partial_app_typing_"
                                                       uu____73830
                                                      in
                                                   (uu____73819,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____73828)
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____73811
                                                  in
                                               let uu____73838 =
                                                 let uu____73841 =
                                                   let uu____73844 =
                                                     let uu____73847 =
                                                       FStar_SMTEncoding_Term.mk_decls
                                                         "" tkey_hash
                                                         [e_typing]
                                                         (FStar_List.append
                                                            decls
                                                            (FStar_List.append
                                                               decls' decls''))
                                                        in
                                                     FStar_List.append
                                                       decls'' uu____73847
                                                      in
                                                   FStar_List.append decls'
                                                     uu____73844
                                                    in
                                                 FStar_List.append decls
                                                   uu____73841
                                                  in
                                               (app_tm, uu____73838))))
                             in
                          let encode_full_app fv =
                            let uu____73867 =
                              FStar_SMTEncoding_Env.lookup_free_var_sym env
                                fv
                               in
                            match uu____73867 with
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
                                   FStar_Syntax_Syntax.pos = uu____73910;
                                   FStar_Syntax_Syntax.vars = uu____73911;_},uu____73912)
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
                                   FStar_Syntax_Syntax.pos = uu____73919;
                                   FStar_Syntax_Syntax.vars = uu____73920;_},uu____73921)
                                ->
                                let uu____73926 =
                                  let uu____73927 =
                                    let uu____73932 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____73932
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____73927
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____73926
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____73962 =
                                  let uu____73963 =
                                    let uu____73968 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____73968
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____73963
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____73962
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____73997,(FStar_Util.Inl t1,uu____73999),uu____74000)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____74047,(FStar_Util.Inr c,uu____74049),uu____74050)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____74097 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____74118 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Env.Weak;
                                     FStar_TypeChecker_Env.HNF;
                                     FStar_TypeChecker_Env.EraseUniverses]
                                     env.FStar_SMTEncoding_Env.tcenv
                                     head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____74118
                                  in
                               let uu____74119 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____74119 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____74135;
                                            FStar_Syntax_Syntax.vars =
                                              uu____74136;_},uu____74137)
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
                                     | uu____74155 ->
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
           let uu____74234 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____74234 with
            | (bs1,body1,opening) ->
                let fallback uu____74257 =
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
                  let uu____74267 =
                    let uu____74268 =
                      FStar_SMTEncoding_Term.mk_fv
                        (f, FStar_SMTEncoding_Term.Term_sort)
                       in
                    FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV
                      uu____74268
                     in
                  let uu____74270 =
                    FStar_All.pipe_right [decl]
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  (uu____74267, uu____74270)  in
                let is_impure rc =
                  let uu____74280 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                      env.FStar_SMTEncoding_Env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____74280 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____74295 =
                          let uu____74308 =
                            FStar_TypeChecker_Env.get_range
                              env.FStar_SMTEncoding_Env.tcenv
                             in
                          FStar_TypeChecker_Util.new_implicit_var
                            "SMTEncoding codomain" uu____74308
                            env.FStar_SMTEncoding_Env.tcenv
                            FStar_Syntax_Util.ktype0
                           in
                        (match uu____74295 with
                         | (t1,uu____74311,uu____74312) -> t1)
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  let uu____74330 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                     in
                  if uu____74330
                  then
                    let uu____74335 = FStar_Syntax_Syntax.mk_Total res_typ
                       in
                    FStar_Pervasives_Native.Some uu____74335
                  else
                    (let uu____74338 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid
                        in
                     if uu____74338
                     then
                       let uu____74343 =
                         FStar_Syntax_Syntax.mk_GTotal res_typ  in
                       FStar_Pervasives_Native.Some uu____74343
                     else FStar_Pervasives_Native.None)
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____74351 =
                         let uu____74357 =
                           let uu____74359 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____74359
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____74357)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____74351);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____74364 =
                       (is_impure rc) &&
                         (let uu____74367 =
                            FStar_TypeChecker_Env.is_reifiable_rc
                              env.FStar_SMTEncoding_Env.tcenv rc
                             in
                          Prims.op_Negation uu____74367)
                        in
                     if uu____74364
                     then fallback ()
                     else
                       (let uu____74376 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____74376 with
                        | (vars,guards,envbody,decls,uu____74401) ->
                            let body2 =
                              let uu____74415 =
                                FStar_TypeChecker_Env.is_reifiable_rc
                                  env.FStar_SMTEncoding_Env.tcenv rc
                                 in
                              if uu____74415
                              then
                                FStar_TypeChecker_Util.reify_body
                                  env.FStar_SMTEncoding_Env.tcenv body1
                              else body1  in
                            let uu____74420 = encode_term body2 envbody  in
                            (match uu____74420 with
                             | (body3,decls') ->
                                 let uu____74431 =
                                   let uu____74440 = codomain_eff rc  in
                                   match uu____74440 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____74459 = encode_term tfun env
                                          in
                                       (match uu____74459 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____74431 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____74493 =
                                          let uu____74504 =
                                            let uu____74505 =
                                              let uu____74510 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____74510, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____74505
                                             in
                                          ([], vars, uu____74504)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t0.FStar_Syntax_Syntax.pos
                                          uu____74493
                                         in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body
                                         in
                                      let uu____74518 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            (cvars, key_body)
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____74534 =
                                              let uu____74537 =
                                                let uu____74548 =
                                                  FStar_SMTEncoding_Term.free_variables
                                                    t1
                                                   in
                                                FStar_List.append uu____74548
                                                  cvars
                                                 in
                                              FStar_Util.remove_dups
                                                FStar_SMTEncoding_Term.fv_eq
                                                uu____74537
                                               in
                                            let uu____74575 =
                                              FStar_SMTEncoding_Util.mkAnd
                                                (key_body, t1)
                                               in
                                            (uu____74534, uu____74575)
                                         in
                                      (match uu____74518 with
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
                                           let uu____74597 =
                                             is_an_eta_expansion env vars
                                               body3
                                              in
                                           (match uu____74597 with
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
                                                  let uu____74613 =
                                                    FStar_Util.digest_of_string
                                                      tkey_hash
                                                     in
                                                  Prims.op_Hat "Tm_abs_"
                                                    uu____74613
                                                   in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None)
                                                   in
                                                let f =
                                                  let uu____74622 =
                                                    let uu____74630 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    (fsym, uu____74630)  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____74622
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
                                                      let uu____74647 =
                                                        let uu____74648 =
                                                          let uu____74656 =
                                                            FStar_SMTEncoding_Term.mkForall
                                                              t0.FStar_Syntax_Syntax.pos
                                                              ([[f]], cvars1,
                                                                f_has_t)
                                                             in
                                                          (uu____74656,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name)
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____74648
                                                         in
                                                      [uu____74647]
                                                   in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.op_Hat
                                                      "interpretation_" fsym
                                                     in
                                                  let uu____74671 =
                                                    let uu____74679 =
                                                      let uu____74680 =
                                                        let uu____74691 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3)
                                                           in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____74691)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        t0.FStar_Syntax_Syntax.pos
                                                        uu____74680
                                                       in
                                                    (uu____74679,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____74671
                                                   in
                                                let f_decls =
                                                  FStar_List.append (fdecl ::
                                                    typing_f) [interp_f]
                                                   in
                                                let uu____74705 =
                                                  let uu____74706 =
                                                    let uu____74709 =
                                                      let uu____74712 =
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
                                                        decls'' uu____74712
                                                       in
                                                    FStar_List.append decls'
                                                      uu____74709
                                                     in
                                                  FStar_List.append decls
                                                    uu____74706
                                                   in
                                                (f, uu____74705))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____74715,{
                           FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                             uu____74716;
                           FStar_Syntax_Syntax.lbunivs = uu____74717;
                           FStar_Syntax_Syntax.lbtyp = uu____74718;
                           FStar_Syntax_Syntax.lbeff = uu____74719;
                           FStar_Syntax_Syntax.lbdef = uu____74720;
                           FStar_Syntax_Syntax.lbattrs = uu____74721;
                           FStar_Syntax_Syntax.lbpos = uu____74722;_}::uu____74723),uu____74724)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____74758;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____74760;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____74762;
                FStar_Syntax_Syntax.lbpos = uu____74763;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____74790 ->
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
              let uu____74862 =
                let uu____74867 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____74867 env  in
              match uu____74862 with
              | (ee1,decls1) ->
                  let uu____74892 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____74892 with
                   | (xs,e21) ->
                       let uu____74917 = FStar_List.hd xs  in
                       (match uu____74917 with
                        | (x1,uu____74935) ->
                            let env' =
                              FStar_SMTEncoding_Env.push_term_var env x1 ee1
                               in
                            let uu____74941 = encode_body e21 env'  in
                            (match uu____74941 with
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
            let uu____74971 =
              let uu____74979 =
                let uu____74980 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____74980  in
              FStar_SMTEncoding_Env.gen_term_var env uu____74979  in
            match uu____74971 with
            | (scrsym,scr',env1) ->
                let uu____74990 = encode_term e env1  in
                (match uu____74990 with
                 | (scr,decls) ->
                     let uu____75001 =
                       let encode_branch b uu____75030 =
                         match uu____75030 with
                         | (else_case,decls1) ->
                             let uu____75049 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____75049 with
                              | (p,w,br) ->
                                  let uu____75075 = encode_pat env1 p  in
                                  (match uu____75075 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____75112  ->
                                                   match uu____75112 with
                                                   | (x,t) ->
                                                       FStar_SMTEncoding_Env.push_term_var
                                                         env2 x t) env1)
                                          in
                                       let uu____75119 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____75141 =
                                               encode_term w1 env2  in
                                             (match uu____75141 with
                                              | (w2,decls2) ->
                                                  let uu____75154 =
                                                    let uu____75155 =
                                                      let uu____75160 =
                                                        let uu____75161 =
                                                          let uu____75166 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____75166)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____75161
                                                         in
                                                      (guard, uu____75160)
                                                       in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____75155
                                                     in
                                                  (uu____75154, decls2))
                                          in
                                       (match uu____75119 with
                                        | (guard1,decls2) ->
                                            let uu____75181 =
                                              encode_br br env2  in
                                            (match uu____75181 with
                                             | (br1,decls3) ->
                                                 let uu____75194 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____75194,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____75001 with
                      | (match_tm,decls1) ->
                          let uu____75215 =
                            let uu____75216 =
                              let uu____75227 =
                                let uu____75234 =
                                  let uu____75239 =
                                    FStar_SMTEncoding_Term.mk_fv
                                      (scrsym,
                                        FStar_SMTEncoding_Term.Term_sort)
                                     in
                                  (uu____75239, scr)  in
                                [uu____75234]  in
                              (uu____75227, match_tm)  in
                            FStar_SMTEncoding_Term.mkLet' uu____75216
                              FStar_Range.dummyRange
                             in
                          (uu____75215, decls1)))

and (encode_pat :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.pat -> (FStar_SMTEncoding_Env.env_t * pattern))
  =
  fun env  ->
    fun pat  ->
      (let uu____75262 =
         FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
           FStar_Options.Medium
          in
       if uu____75262
       then
         let uu____75265 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____75265
       else ());
      (let uu____75270 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____75270 with
       | (vars,pat_term) ->
           let uu____75287 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____75329  ->
                     fun v1  ->
                       match uu____75329 with
                       | (env1,vars1) ->
                           let uu____75365 =
                             FStar_SMTEncoding_Env.gen_term_var env1 v1  in
                           (match uu____75365 with
                            | (xx,uu____75384,env2) ->
                                let uu____75388 =
                                  let uu____75395 =
                                    let uu____75400 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xx,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    (v1, uu____75400)  in
                                  uu____75395 :: vars1  in
                                (env2, uu____75388))) (env, []))
              in
           (match uu____75287 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____75455 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____75456 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____75457 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____75465 = encode_const c env1  in
                      (match uu____75465 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____75473::uu____75474 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____75478 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon
                            env1.FStar_SMTEncoding_Env.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____75501 =
                          FStar_TypeChecker_Env.datacons_of_typ
                            env1.FStar_SMTEncoding_Env.tcenv tc_name
                           in
                        match uu____75501 with
                        | (uu____75509,uu____75510::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____75515 ->
                            FStar_SMTEncoding_Env.mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____75551  ->
                                  match uu____75551 with
                                  | (arg,uu____75561) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____75570 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____75570))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____75602) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____75633 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____75658 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____75704  ->
                                  match uu____75704 with
                                  | (arg,uu____75720) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____75729 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____75729))
                         in
                      FStar_All.pipe_right uu____75658 FStar_List.flatten
                   in
                let pat_term1 uu____75760 = encode_term pat_term env1  in
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
      let uu____75770 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____75818  ->
                fun uu____75819  ->
                  match (uu____75818, uu____75819) with
                  | ((tms,decls),(t,uu____75859)) ->
                      let uu____75886 = encode_term t env  in
                      (match uu____75886 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____75770 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____75943 = FStar_Syntax_Util.list_elements e  in
        match uu____75943 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____75974 =
          let uu____75991 = FStar_Syntax_Util.unmeta p  in
          FStar_All.pipe_right uu____75991 FStar_Syntax_Util.head_and_args
           in
        match uu____75974 with
        | (head1,args) ->
            let uu____76042 =
              let uu____76057 =
                let uu____76058 = FStar_Syntax_Util.un_uinst head1  in
                uu____76058.FStar_Syntax_Syntax.n  in
              (uu____76057, args)  in
            (match uu____76042 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____76080,uu____76081)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____76133 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or1 t1 =
          let uu____76188 =
            let uu____76205 = FStar_Syntax_Util.unmeta t1  in
            FStar_All.pipe_right uu____76205 FStar_Syntax_Util.head_and_args
             in
          match uu____76188 with
          | (head1,args) ->
              let uu____76252 =
                let uu____76267 =
                  let uu____76268 = FStar_Syntax_Util.un_uinst head1  in
                  uu____76268.FStar_Syntax_Syntax.n  in
                (uu____76267, args)  in
              (match uu____76252 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____76287)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____76324 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____76354 = smt_pat_or1 t1  in
            (match uu____76354 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____76376 = list_elements1 e  in
                 FStar_All.pipe_right uu____76376
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____76406 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____76406
                           (FStar_List.map one_pat)))
             | uu____76429 ->
                 let uu____76434 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____76434])
        | uu____76485 ->
            let uu____76488 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____76488]
         in
      let uu____76539 =
        let uu____76554 =
          let uu____76555 = FStar_Syntax_Subst.compress t  in
          uu____76555.FStar_Syntax_Syntax.n  in
        match uu____76554 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____76594 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____76594 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____76629;
                        FStar_Syntax_Syntax.effect_name = uu____76630;
                        FStar_Syntax_Syntax.result_typ = uu____76631;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____76633)::(post,uu____76635)::(pats,uu____76637)::[];
                        FStar_Syntax_Syntax.flags = uu____76638;_}
                      ->
                      let uu____76699 = lemma_pats pats  in
                      (binders1, pre, post, uu____76699)
                  | uu____76710 -> failwith "impos"))
        | uu____76726 -> failwith "Impos"  in
      match uu____76539 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___1940_76763 = env  in
            {
              FStar_SMTEncoding_Env.bvar_bindings =
                (uu___1940_76763.FStar_SMTEncoding_Env.bvar_bindings);
              FStar_SMTEncoding_Env.fvar_bindings =
                (uu___1940_76763.FStar_SMTEncoding_Env.fvar_bindings);
              FStar_SMTEncoding_Env.depth =
                (uu___1940_76763.FStar_SMTEncoding_Env.depth);
              FStar_SMTEncoding_Env.tcenv =
                (uu___1940_76763.FStar_SMTEncoding_Env.tcenv);
              FStar_SMTEncoding_Env.warn =
                (uu___1940_76763.FStar_SMTEncoding_Env.warn);
              FStar_SMTEncoding_Env.nolabels =
                (uu___1940_76763.FStar_SMTEncoding_Env.nolabels);
              FStar_SMTEncoding_Env.use_zfuel_name = true;
              FStar_SMTEncoding_Env.encode_non_total_function_typ =
                (uu___1940_76763.FStar_SMTEncoding_Env.encode_non_total_function_typ);
              FStar_SMTEncoding_Env.current_module_name =
                (uu___1940_76763.FStar_SMTEncoding_Env.current_module_name);
              FStar_SMTEncoding_Env.encoding_quantifier =
                (uu___1940_76763.FStar_SMTEncoding_Env.encoding_quantifier);
              FStar_SMTEncoding_Env.global_cache =
                (uu___1940_76763.FStar_SMTEncoding_Env.global_cache)
            }  in
          let uu____76765 =
            encode_binders FStar_Pervasives_Native.None binders env1  in
          (match uu____76765 with
           | (vars,guards,env2,decls,uu____76790) ->
               let uu____76803 = encode_smt_patterns patterns env2  in
               (match uu____76803 with
                | (pats,decls') ->
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
                    let env3 =
                      let uu___1953_76830 = env2  in
                      {
                        FStar_SMTEncoding_Env.bvar_bindings =
                          (uu___1953_76830.FStar_SMTEncoding_Env.bvar_bindings);
                        FStar_SMTEncoding_Env.fvar_bindings =
                          (uu___1953_76830.FStar_SMTEncoding_Env.fvar_bindings);
                        FStar_SMTEncoding_Env.depth =
                          (uu___1953_76830.FStar_SMTEncoding_Env.depth);
                        FStar_SMTEncoding_Env.tcenv =
                          (uu___1953_76830.FStar_SMTEncoding_Env.tcenv);
                        FStar_SMTEncoding_Env.warn =
                          (uu___1953_76830.FStar_SMTEncoding_Env.warn);
                        FStar_SMTEncoding_Env.nolabels = true;
                        FStar_SMTEncoding_Env.use_zfuel_name =
                          (uu___1953_76830.FStar_SMTEncoding_Env.use_zfuel_name);
                        FStar_SMTEncoding_Env.encode_non_total_function_typ =
                          (uu___1953_76830.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                        FStar_SMTEncoding_Env.current_module_name =
                          (uu___1953_76830.FStar_SMTEncoding_Env.current_module_name);
                        FStar_SMTEncoding_Env.encoding_quantifier =
                          (uu___1953_76830.FStar_SMTEncoding_Env.encoding_quantifier);
                        FStar_SMTEncoding_Env.global_cache =
                          (uu___1953_76830.FStar_SMTEncoding_Env.global_cache)
                      }  in
                    let uu____76832 =
                      let uu____76837 = FStar_Syntax_Util.unmeta pre  in
                      encode_formula uu____76837 env3  in
                    (match uu____76832 with
                     | (pre1,decls'') ->
                         let uu____76844 =
                           let uu____76849 = FStar_Syntax_Util.unmeta post1
                              in
                           encode_formula uu____76849 env3  in
                         (match uu____76844 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append decls'
                                     (FStar_List.append decls'' decls'''))
                                 in
                              let uu____76859 =
                                let uu____76860 =
                                  let uu____76871 =
                                    let uu____76872 =
                                      let uu____76877 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards)
                                         in
                                      (uu____76877, post2)  in
                                    FStar_SMTEncoding_Util.mkImp uu____76872
                                     in
                                  (pats, vars, uu____76871)  in
                                FStar_SMTEncoding_Term.mkForall
                                  t.FStar_Syntax_Syntax.pos uu____76860
                                 in
                              (uu____76859, decls1)))))

and (encode_smt_patterns :
  FStar_Syntax_Syntax.arg Prims.list Prims.list ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term Prims.list Prims.list *
        FStar_SMTEncoding_Term.decls_t))
  =
  fun pats_l  ->
    fun env  ->
      let env1 =
        let uu___1965_76897 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___1965_76897.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___1965_76897.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___1965_76897.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___1965_76897.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___1965_76897.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___1965_76897.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___1965_76897.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___1965_76897.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___1965_76897.FStar_SMTEncoding_Env.encoding_quantifier);
          FStar_SMTEncoding_Env.global_cache =
            (uu___1965_76897.FStar_SMTEncoding_Env.global_cache)
        }  in
      let encode_smt_pattern t =
        let uu____76913 = FStar_Syntax_Util.head_and_args t  in
        match uu____76913 with
        | (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____76976::(x,uu____76978)::(t1,uu____76980)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____77047 = encode_term x env1  in
                 (match uu____77047 with
                  | (x1,decls) ->
                      let uu____77058 = encode_term t1 env1  in
                      (match uu____77058 with
                       | (t2,decls') ->
                           let uu____77069 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                           (uu____77069, (FStar_List.append decls decls'))))
             | uu____77070 -> encode_term t env1)
         in
      FStar_List.fold_right
        (fun pats  ->
           fun uu____77113  ->
             match uu____77113 with
             | (pats_l1,decls) ->
                 let uu____77158 =
                   FStar_List.fold_right
                     (fun uu____77193  ->
                        fun uu____77194  ->
                          match (uu____77193, uu____77194) with
                          | ((p,uu____77236),(pats1,decls1)) ->
                              let uu____77271 = encode_smt_pattern p  in
                              (match uu____77271 with
                               | (t,d) ->
                                   let uu____77286 =
                                     FStar_SMTEncoding_Term.check_pattern_ok
                                       t
                                      in
                                   (match uu____77286 with
                                    | FStar_Pervasives_Native.None  ->
                                        ((t :: pats1),
                                          (FStar_List.append d decls1))
                                    | FStar_Pervasives_Native.Some
                                        illegal_subterm ->
                                        ((let uu____77303 =
                                            let uu____77309 =
                                              let uu____77311 =
                                                FStar_Syntax_Print.term_to_string
                                                  p
                                                 in
                                              let uu____77313 =
                                                FStar_SMTEncoding_Term.print_smt_term
                                                  illegal_subterm
                                                 in
                                              FStar_Util.format2
                                                "Pattern %s contains illegal sub-term (%s); dropping it"
                                                uu____77311 uu____77313
                                               in
                                            (FStar_Errors.Warning_SMTPatternIllFormed,
                                              uu____77309)
                                             in
                                          FStar_Errors.log_issue
                                            p.FStar_Syntax_Syntax.pos
                                            uu____77303);
                                         (pats1,
                                           (FStar_List.append d decls1))))))
                     pats ([], decls)
                    in
                 (match uu____77158 with
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
        let uu____77373 =
          FStar_All.pipe_left
            (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____77373
        then
          let uu____77378 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____77380 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____77378 uu____77380
        else ()  in
      let enc f r l =
        let uu____77422 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____77454 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____77454 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____77422 with
        | (decls,args) ->
            let uu____77485 =
              let uu___2029_77486 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___2029_77486.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___2029_77486.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____77485, decls)
         in
      let const_op f r uu____77521 =
        let uu____77534 = f r  in (uu____77534, [])  in
      let un_op f l =
        let uu____77557 = FStar_List.hd l  in
        FStar_All.pipe_left f uu____77557  in
      let bin_op f uu___632_77577 =
        match uu___632_77577 with
        | t1::t2::[] -> f (t1, t2)
        | uu____77588 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____77629 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____77654  ->
                 match uu____77654 with
                 | (t,uu____77670) ->
                     let uu____77675 = encode_formula t env  in
                     (match uu____77675 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____77629 with
        | (decls,phis) ->
            let uu____77704 =
              let uu___2059_77705 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___2059_77705.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___2059_77705.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____77704, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____77768  ->
               match uu____77768 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____77789) -> false
                    | uu____77792 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____77811 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____77811
        else
          (let uu____77828 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____77828 r rf)
         in
      let eq3_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____77896 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::t1::v0::v1::[] ->
                     let uu____77928 =
                       let uu____77933 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____77934 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____77933, uu____77934)  in
                     FStar_SMTEncoding_Util.mkAnd uu____77928
                 | uu____77935 -> failwith "Impossible")
             in
          uu____77896 r args
        else
          (let uu____77941 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____77941)
         in
      let h_equals_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____78003 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::v0::t1::v1::[] ->
                     let uu____78035 =
                       let uu____78040 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____78041 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____78040, uu____78041)  in
                     FStar_SMTEncoding_Util.mkAnd uu____78035
                 | uu____78042 -> failwith "Impossible")
             in
          uu____78003 r args
        else
          (let uu____78048 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____78048)
         in
      let mk_imp1 r uu___633_78077 =
        match uu___633_78077 with
        | (lhs,uu____78083)::(rhs,uu____78085)::[] ->
            let uu____78126 = encode_formula rhs env  in
            (match uu____78126 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____78141) ->
                      (l1, decls1)
                  | uu____78146 ->
                      let uu____78147 = encode_formula lhs env  in
                      (match uu____78147 with
                       | (l2,decls2) ->
                           let uu____78158 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____78158, (FStar_List.append decls1 decls2)))))
        | uu____78159 -> failwith "impossible"  in
      let mk_ite r uu___634_78187 =
        match uu___634_78187 with
        | (guard,uu____78193)::(_then,uu____78195)::(_else,uu____78197)::[]
            ->
            let uu____78254 = encode_formula guard env  in
            (match uu____78254 with
             | (g,decls1) ->
                 let uu____78265 = encode_formula _then env  in
                 (match uu____78265 with
                  | (t,decls2) ->
                      let uu____78276 = encode_formula _else env  in
                      (match uu____78276 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____78288 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____78318 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l
           in
        f uu____78318  in
      let connectives =
        let uu____78348 =
          let uu____78373 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____78373)  in
        let uu____78416 =
          let uu____78443 =
            let uu____78468 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____78468)  in
          let uu____78511 =
            let uu____78538 =
              let uu____78565 =
                let uu____78590 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____78590)  in
              let uu____78633 =
                let uu____78660 =
                  let uu____78687 =
                    let uu____78712 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____78712)  in
                  [uu____78687;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.c_eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq3_op);
                  (FStar_Parser_Const.c_eq3_lid, h_equals_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____78660  in
              uu____78565 :: uu____78633  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____78538  in
          uu____78443 :: uu____78511  in
        uu____78348 :: uu____78416  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____79257 = encode_formula phi' env  in
            (match uu____79257 with
             | (phi2,decls) ->
                 let uu____79268 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____79268, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____79270 ->
            let uu____79277 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____79277 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____79316 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____79316 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____79328;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____79330;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____79332;
                 FStar_Syntax_Syntax.lbpos = uu____79333;_}::[]),e2)
            ->
            let uu____79360 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____79360 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____79413::(x,uu____79415)::(t,uu____79417)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____79484 = encode_term x env  in
                 (match uu____79484 with
                  | (x1,decls) ->
                      let uu____79495 = encode_term t env  in
                      (match uu____79495 with
                       | (t1,decls') ->
                           let uu____79506 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____79506, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____79509)::(msg,uu____79511)::(phi2,uu____79513)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____79580 =
                   let uu____79585 =
                     let uu____79586 = FStar_Syntax_Subst.compress r  in
                     uu____79586.FStar_Syntax_Syntax.n  in
                   let uu____79589 =
                     let uu____79590 = FStar_Syntax_Subst.compress msg  in
                     uu____79590.FStar_Syntax_Syntax.n  in
                   (uu____79585, uu____79589)  in
                 (match uu____79580 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____79599))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____79610 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____79617)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____79652 when head_redex env head2 ->
                 let uu____79667 = whnf env phi1  in
                 encode_formula uu____79667 env
             | uu____79668 ->
                 let uu____79683 = encode_term phi1 env  in
                 (match uu____79683 with
                  | (tt,decls) ->
                      let tt1 =
                        let uu____79695 =
                          let uu____79697 =
                            FStar_Range.use_range
                              tt.FStar_SMTEncoding_Term.rng
                             in
                          let uu____79698 =
                            FStar_Range.use_range
                              phi1.FStar_Syntax_Syntax.pos
                             in
                          FStar_Range.rng_included uu____79697 uu____79698
                           in
                        if uu____79695
                        then tt
                        else
                          (let uu___2246_79702 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___2246_79702.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___2246_79702.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      let uu____79703 = FStar_SMTEncoding_Term.mk_Valid tt1
                         in
                      (uu____79703, decls)))
        | uu____79704 ->
            let uu____79705 = encode_term phi1 env  in
            (match uu____79705 with
             | (tt,decls) ->
                 let tt1 =
                   let uu____79717 =
                     let uu____79719 =
                       FStar_Range.use_range tt.FStar_SMTEncoding_Term.rng
                        in
                     let uu____79720 =
                       FStar_Range.use_range phi1.FStar_Syntax_Syntax.pos  in
                     FStar_Range.rng_included uu____79719 uu____79720  in
                   if uu____79717
                   then tt
                   else
                     (let uu___2254_79724 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___2254_79724.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___2254_79724.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 let uu____79725 = FStar_SMTEncoding_Term.mk_Valid tt1  in
                 (uu____79725, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____79769 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____79769 with
        | (vars,guards,env2,decls,uu____79808) ->
            let uu____79821 = encode_smt_patterns ps env2  in
            (match uu____79821 with
             | (pats,decls') ->
                 let uu____79858 = encode_formula body env2  in
                 (match uu____79858 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____79890;
                             FStar_SMTEncoding_Term.rng = uu____79891;_}::[])::[]
                            when
                            let uu____79911 =
                              FStar_Ident.text_of_lid
                                FStar_Parser_Const.guard_free
                               in
                            uu____79911 = gf -> []
                        | uu____79914 -> guards  in
                      let uu____79919 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____79919, body1,
                        (FStar_List.append decls
                           (FStar_List.append decls' decls'')))))
         in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi  in
       let uu____79930 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____79930 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____79939 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____80045  ->
                     match uu____80045 with
                     | (l,uu____80070) -> FStar_Ident.lid_equals op l))
              in
           (match uu____79939 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____80139,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____80231 = encode_q_body env vars pats body  in
             match uu____80231 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____80276 =
                     let uu____80287 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____80287)  in
                   FStar_SMTEncoding_Term.mkForall
                     phi1.FStar_Syntax_Syntax.pos uu____80276
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____80318 = encode_q_body env vars pats body  in
             match uu____80318 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____80362 =
                   let uu____80363 =
                     let uu____80374 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____80374)  in
                   FStar_SMTEncoding_Term.mkExists
                     phi1.FStar_Syntax_Syntax.pos uu____80363
                    in
                 (uu____80362, decls))))
