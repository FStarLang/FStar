open Prims
let mkForall_fuel' :
  'Auu____66274 .
    Prims.string ->
      FStar_Range.range ->
        'Auu____66274 ->
          (FStar_SMTEncoding_Term.pat Prims.list Prims.list *
            FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term) ->
            FStar_SMTEncoding_Term.term
  =
  fun mname  ->
    fun r  ->
      fun n1  ->
        fun uu____66305  ->
          match uu____66305 with
          | (pats,vars,body) ->
              let fallback uu____66333 =
                FStar_SMTEncoding_Term.mkForall r (pats, vars, body)  in
              let uu____66338 = FStar_Options.unthrottle_inductives ()  in
              if uu____66338
              then fallback ()
              else
                (let uu____66343 =
                   FStar_SMTEncoding_Env.fresh_fvar mname "f"
                     FStar_SMTEncoding_Term.Fuel_sort
                    in
                 match uu____66343 with
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
                               | uu____66383 -> p))
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
                                 let uu____66404 = add_fuel1 guards  in
                                 FStar_SMTEncoding_Util.mk_and_l uu____66404
                             | uu____66407 ->
                                 let uu____66408 = add_fuel1 [guard]  in
                                 FStar_All.pipe_right uu____66408
                                   FStar_List.hd
                              in
                           FStar_SMTEncoding_Util.mkImp (guard1, body')
                       | uu____66413 -> body  in
                     let vars1 =
                       let uu____66425 =
                         FStar_SMTEncoding_Term.mk_fv
                           (fsym, FStar_SMTEncoding_Term.Fuel_sort)
                          in
                       uu____66425 :: vars  in
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
      | FStar_Syntax_Syntax.Tm_arrow uu____66489 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____66505 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____66513 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____66515 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____66529 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____66549 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____66552 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____66552 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____66571;
             FStar_Syntax_Syntax.vars = uu____66572;_},uu____66573)
          ->
          let uu____66598 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____66598 FStar_Option.isNone
      | uu____66616 -> false
  
let (head_redex :
  FStar_SMTEncoding_Env.env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____66630 =
        let uu____66631 = FStar_Syntax_Util.un_uinst t  in
        uu____66631.FStar_Syntax_Syntax.n  in
      match uu____66630 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____66635,uu____66636,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___630_66661  ->
                  match uu___630_66661 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____66664 -> false)
               rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____66667 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____66667 FStar_Option.isSome
      | uu____66685 -> false
  
let (whnf :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____66698 = head_normal env t  in
      if uu____66698
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
    let uu____66720 =
      let uu____66721 = FStar_Syntax_Syntax.null_binder t  in [uu____66721]
       in
    let uu____66740 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    FStar_Syntax_Util.abs uu____66720 uu____66740
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
                let uu____66762 = FStar_SMTEncoding_Term.fv_sort var  in
                match uu____66762 with
                | FStar_SMTEncoding_Term.Fuel_sort  ->
                    let uu____66763 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____66763
                | s ->
                    let uu____66766 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____66766) e)
  
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
          let uu____66822 =
            let uu____66828 =
              let uu____66830 = FStar_Util.string_of_int arity  in
              let uu____66832 = FStar_Util.string_of_int n_args  in
              FStar_Util.format3
                "Head symbol %s expects at least %s arguments; got only %s"
                head1 uu____66830 uu____66832
               in
            (FStar_Errors.Fatal_SMTEncodingArityMismatch, uu____66828)  in
          FStar_Errors.raise_error uu____66822 rng
  
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
                  (let uu____66881 = FStar_Util.first_N arity args  in
                   match uu____66881 with
                   | (args1,rest) ->
                       let head3 =
                         FStar_SMTEncoding_Util.mkApp' (head2, args1)  in
                       mk_Apply_args head3 rest)
                else
                  (let uu____66905 =
                     FStar_SMTEncoding_Term.op_to_string head2  in
                   raise_arity_mismatch uu____66905 arity n_args rng)
  
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
          let uu____66928 = FStar_SMTEncoding_Env.force_thunk fvb  in
          mk_Apply_args uu____66928 args
        else
          maybe_curry_app rng
            (FStar_Util.Inl
               (FStar_SMTEncoding_Term.Var (fvb.FStar_SMTEncoding_Env.smt_id)))
            fvb.FStar_SMTEncoding_Env.smt_arity args
  
let (is_app : FStar_SMTEncoding_Term.op -> Prims.bool) =
  fun uu___631_66937  ->
    match uu___631_66937 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____66943 -> false
  
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
                       FStar_SMTEncoding_Term.freevars = uu____66991;
                       FStar_SMTEncoding_Term.rng = uu____66992;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____67023) ->
              let uu____67033 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____67050 -> false) args (FStar_List.rev xs))
                 in
              if uu____67033
              then FStar_SMTEncoding_Env.tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____67057,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t  in
              let uu____67061 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____67069 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars
                           in
                        Prims.op_Negation uu____67069))
                 in
              if uu____67061
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____67076 -> FStar_Pervasives_Native.None  in
        check_partial_applications body (FStar_List.rev vars)
  
let check_pattern_vars :
  'Auu____67094 'Auu____67095 .
    FStar_SMTEncoding_Env.env_t ->
      (FStar_Syntax_Syntax.bv * 'Auu____67094) Prims.list ->
        (FStar_Syntax_Syntax.term * 'Auu____67095) Prims.list -> unit
  =
  fun env  ->
    fun vars  ->
      fun pats  ->
        let pats1 =
          FStar_All.pipe_right pats
            (FStar_List.map
               (fun uu____67153  ->
                  match uu____67153 with
                  | (x,uu____67159) ->
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
              let uu____67167 = FStar_Syntax_Free.names hd1  in
              FStar_List.fold_left
                (fun out  ->
                   fun x  ->
                     let uu____67179 = FStar_Syntax_Free.names x  in
                     FStar_Util.set_union out uu____67179) uu____67167 tl1
               in
            let uu____67182 =
              FStar_All.pipe_right vars
                (FStar_Util.find_opt
                   (fun uu____67209  ->
                      match uu____67209 with
                      | (b,uu____67216) ->
                          let uu____67217 = FStar_Util.set_mem b pat_vars  in
                          Prims.op_Negation uu____67217))
               in
            (match uu____67182 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some (x,uu____67224) ->
                 let pos =
                   FStar_List.fold_left
                     (fun out  ->
                        fun t  ->
                          FStar_Range.union_ranges out
                            t.FStar_Syntax_Syntax.pos)
                     hd1.FStar_Syntax_Syntax.pos tl1
                    in
                 let uu____67238 =
                   let uu____67244 =
                     let uu____67246 = FStar_Syntax_Print.bv_to_string x  in
                     FStar_Util.format1
                       "SMT pattern misses at least one bound variable: %s"
                       uu____67246
                      in
                   (FStar_Errors.Warning_SMTPatternIllFormed, uu____67244)
                    in
                 FStar_Errors.log_issue pos uu____67238)
  
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
        | FStar_Syntax_Syntax.Tm_arrow uu____67532 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____67547 ->
            let uu____67554 = FStar_Syntax_Util.unrefine t1  in
            aux true uu____67554
        | uu____67556 ->
            if norm1
            then let uu____67558 = whnf env t1  in aux false uu____67558
            else
              (let uu____67562 =
                 let uu____67564 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let uu____67566 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____67564 uu____67566
                  in
               failwith uu____67562)
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
    | FStar_Syntax_Syntax.Tm_refine (bv,uu____67608) ->
        let uu____67613 =
          curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort  in
        (match uu____67613 with
         | (args,res) ->
             (match args with
              | [] ->
                  let uu____67634 = FStar_Syntax_Syntax.mk_Total k1  in
                  ([], uu____67634)
              | uu____67641 -> (args, res)))
    | uu____67642 ->
        let uu____67643 = FStar_Syntax_Syntax.mk_Total k1  in
        ([], uu____67643)
  
let is_arithmetic_primitive :
  'Auu____67657 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____67657 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____67680::uu____67681::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____67685::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____67688 -> false
  
let (isInteger : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____67719 -> false
  
let (getInteger : FStar_Syntax_Syntax.term' -> Prims.int) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____67742 -> failwith "Expected an Integer term"
  
let is_BitVector_primitive :
  'Auu____67752 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____67752)
        Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____67794)::uu____67795::uu____67796::[]) ->
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
         fv,(sz_arg,uu____67847)::uu____67848::[]) ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____67885 -> false
  
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
          let uu____68209 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue  in
          (uu____68209, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____68211 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse  in
          (uu____68211, [])
      | FStar_Const.Const_char c1 ->
          let uu____68214 =
            let uu____68215 =
              let uu____68223 =
                let uu____68226 =
                  let uu____68227 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1)
                     in
                  FStar_SMTEncoding_Term.boxInt uu____68227  in
                [uu____68226]  in
              ("FStar.Char.__char_of_int", uu____68223)  in
            FStar_SMTEncoding_Util.mkApp uu____68215  in
          (uu____68214, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____68245 =
            let uu____68246 = FStar_SMTEncoding_Util.mkInteger i  in
            FStar_SMTEncoding_Term.boxInt uu____68246  in
          (uu____68245, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.FStar_SMTEncoding_Env.tcenv).FStar_TypeChecker_Env.dsenv
              repr sw FStar_Range.dummyRange
             in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____68267) ->
          let uu____68270 =
            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.string_const s
             in
          (uu____68270, [])
      | FStar_Const.Const_range uu____68271 ->
          let uu____68272 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          (uu____68272, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | FStar_Const.Const_real r ->
          let uu____68275 =
            let uu____68276 = FStar_SMTEncoding_Util.mkReal r  in
            FStar_SMTEncoding_Term.boxReal uu____68276  in
          (uu____68275, [])
      | c1 ->
          let uu____68278 =
            let uu____68280 = FStar_Syntax_Print.const_to_string c1  in
            FStar_Util.format1 "Unhandled constant: %s" uu____68280  in
          failwith uu____68278

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
        (let uu____68309 =
           FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
             FStar_Options.Medium
            in
         if uu____68309
         then
           let uu____68312 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____68312
         else ());
        (let uu____68318 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____68400  ->
                   fun b  ->
                     match uu____68400 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____68465 =
                           let x = FStar_Pervasives_Native.fst b  in
                           let uu____68481 =
                             FStar_SMTEncoding_Env.gen_term_var env1 x  in
                           match uu____68481 with
                           | (xxsym,xx,env') ->
                               let uu____68506 =
                                 let uu____68511 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____68511 env1
                                   xx
                                  in
                               (match uu____68506 with
                                | (guard_x_t,decls') ->
                                    let uu____68526 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xxsym,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    (uu____68526, guard_x_t, env', decls', x))
                            in
                         (match uu____68465 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____68318 with
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
          let uu____68626 = encode_term t env  in
          match uu____68626 with
          | (t1,decls) ->
              let uu____68637 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____68637, decls)

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
          let uu____68648 = encode_term t env  in
          match uu____68648 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____68663 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____68663, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____68665 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____68665, decls))

and (encode_arith_term :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____68671 = encode_args args_e env  in
        match uu____68671 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____68690 -> failwith "Impossible"  in
            let unary unbox arg_tms1 =
              let uu____68712 = FStar_List.hd arg_tms1  in unbox uu____68712
               in
            let binary unbox arg_tms1 =
              let uu____68737 =
                let uu____68738 = FStar_List.hd arg_tms1  in
                unbox uu____68738  in
              let uu____68739 =
                let uu____68740 =
                  let uu____68741 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____68741  in
                unbox uu____68740  in
              (uu____68737, uu____68739)  in
            let mk_default uu____68749 =
              let uu____68750 =
                FStar_SMTEncoding_Env.lookup_free_var_sym env
                  head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____68750 with
              | (fname,fuel_args,arity) ->
                  let args = FStar_List.append fuel_args arg_tms  in
                  maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity
                    args
               in
            let mk_l box op mk_args ts =
              let uu____68839 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____68839
              then
                let uu____68842 =
                  let uu____68843 = mk_args ts  in op uu____68843  in
                FStar_All.pipe_right uu____68842 box
              else mk_default ()  in
            let mk_nl box unbox nm op ts =
              let uu____68901 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____68901
              then
                let uu____68904 = binary unbox ts  in
                match uu____68904 with
                | (t1,t2) ->
                    let uu____68911 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____68911 box
              else
                (let uu____68917 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____68917
                 then
                   let uu____68920 =
                     let uu____68921 = binary unbox ts  in op uu____68921  in
                   FStar_All.pipe_right uu____68920 box
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
            let uu____69356 =
              let uu____69366 =
                FStar_List.tryFind
                  (fun uu____69390  ->
                     match uu____69390 with
                     | (l,uu____69401) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____69366 FStar_Util.must  in
            (match uu____69356 with
             | (uu____69445,op) ->
                 let uu____69457 = op arg_tms  in (uu____69457, decls))

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
        let uu____69473 = FStar_List.hd args_e  in
        match uu____69473 with
        | (tm_sz,uu____69489) ->
            let uu____69498 = uu____69473  in
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let t_decls1 = FStar_SMTEncoding_Term.mkBvConstructor sz  in
              FStar_SMTEncoding_Term.mk_decls "" sz_key t_decls1 []  in
            let uu____69509 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____69535::(sz_arg,uu____69537)::uu____69538::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____69605 =
                    let uu____69606 = FStar_List.tail args_e  in
                    FStar_List.tail uu____69606  in
                  let uu____69633 =
                    let uu____69637 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____69637  in
                  (uu____69605, uu____69633)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____69644::(sz_arg,uu____69646)::uu____69647::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____69714 =
                    let uu____69716 =
                      FStar_Syntax_Print.term_to_string sz_arg  in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____69716
                     in
                  failwith uu____69714
              | uu____69726 ->
                  let uu____69741 = FStar_List.tail args_e  in
                  (uu____69741, FStar_Pervasives_Native.None)
               in
            (match uu____69509 with
             | (arg_tms,ext_sz) ->
                 let uu____69768 = encode_args arg_tms env  in
                 (match uu____69768 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____69789 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____69801 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____69801  in
                      let unary_arith arg_tms2 =
                        let uu____69812 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____69812  in
                      let binary arg_tms2 =
                        let uu____69827 =
                          let uu____69828 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____69828
                           in
                        let uu____69829 =
                          let uu____69830 =
                            let uu____69831 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____69831  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____69830
                           in
                        (uu____69827, uu____69829)  in
                      let binary_arith arg_tms2 =
                        let uu____69848 =
                          let uu____69849 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____69849
                           in
                        let uu____69850 =
                          let uu____69851 =
                            let uu____69852 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____69852  in
                          FStar_SMTEncoding_Term.unboxInt uu____69851  in
                        (uu____69848, uu____69850)  in
                      let mk_bv op mk_args resBox ts =
                        let uu____69910 =
                          let uu____69911 = mk_args ts  in op uu____69911  in
                        FStar_All.pipe_right uu____69910 resBox  in
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
                        let uu____70043 =
                          let uu____70048 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____70048  in
                        let uu____70057 =
                          let uu____70062 =
                            let uu____70064 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____70064  in
                          FStar_SMTEncoding_Term.boxBitVec uu____70062  in
                        mk_bv uu____70043 unary uu____70057 arg_tms2  in
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
                      let uu____70304 =
                        let uu____70314 =
                          FStar_List.tryFind
                            (fun uu____70338  ->
                               match uu____70338 with
                               | (l,uu____70349) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____70314 FStar_Util.must  in
                      (match uu____70304 with
                       | (uu____70395,op) ->
                           let uu____70407 = op arg_tms1  in
                           (uu____70407, (FStar_List.append sz_decls decls)))))

and (encode_deeply_embedded_quantifier :
  FStar_Syntax_Syntax.term ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let env1 =
        let uu___1170_70417 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___1170_70417.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___1170_70417.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___1170_70417.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___1170_70417.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___1170_70417.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___1170_70417.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name =
            (uu___1170_70417.FStar_SMTEncoding_Env.use_zfuel_name);
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___1170_70417.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___1170_70417.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier = true;
          FStar_SMTEncoding_Env.global_cache =
            (uu___1170_70417.FStar_SMTEncoding_Env.global_cache)
        }  in
      let uu____70419 = encode_term t env1  in
      match uu____70419 with
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
               (uu____70445,{
                              FStar_SMTEncoding_Term.tm =
                                FStar_SMTEncoding_Term.FreeV uu____70446;
                              FStar_SMTEncoding_Term.freevars = uu____70447;
                              FStar_SMTEncoding_Term.rng = uu____70448;_}::
                {
                  FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV
                    uu____70449;
                  FStar_SMTEncoding_Term.freevars = uu____70450;
                  FStar_SMTEncoding_Term.rng = uu____70451;_}::[])
               ->
               (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                  (FStar_Errors.Warning_QuantifierWithoutPattern,
                    "Not encoding deeply embedded, unguarded quantifier to SMT");
                (tm, decls))
           | uu____70497 ->
               let uu____70498 = encode_formula t env1  in
               (match uu____70498 with
                | (phi,decls') ->
                    let interp =
                      match vars with
                      | [] ->
                          let uu____70518 =
                            let uu____70523 =
                              FStar_SMTEncoding_Term.mk_Valid tm  in
                            (uu____70523, phi)  in
                          FStar_SMTEncoding_Util.mkIff uu____70518
                      | uu____70524 ->
                          let uu____70525 =
                            let uu____70536 =
                              let uu____70537 =
                                let uu____70542 =
                                  FStar_SMTEncoding_Term.mk_Valid tm  in
                                (uu____70542, phi)  in
                              FStar_SMTEncoding_Util.mkIff uu____70537  in
                            ([[valid_tm]], vars, uu____70536)  in
                          FStar_SMTEncoding_Term.mkForall
                            t.FStar_Syntax_Syntax.pos uu____70525
                       in
                    let ax =
                      let uu____70552 =
                        let uu____70560 =
                          let uu____70562 =
                            FStar_Util.digest_of_string tkey_hash  in
                          Prims.op_Hat "l_quant_interp_" uu____70562  in
                        (interp,
                          (FStar_Pervasives_Native.Some
                             "Interpretation of deeply embedded quantifier"),
                          uu____70560)
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____70552  in
                    let uu____70568 =
                      let uu____70569 =
                        let uu____70572 =
                          FStar_SMTEncoding_Term.mk_decls "" tkey_hash 
                            [ax] (FStar_List.append decls decls')
                           in
                        FStar_List.append decls' uu____70572  in
                      FStar_List.append decls uu____70569  in
                    (tm, uu____70568)))

and (encode_term :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____70584 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____70584
       then
         let uu____70589 = FStar_Syntax_Print.tag_of_term t  in
         let uu____70591 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____70593 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____70589 uu____70591
           uu____70593
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____70602 ->
           let uu____70625 =
             let uu____70627 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____70630 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____70632 = FStar_Syntax_Print.term_to_string t0  in
             let uu____70634 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____70627
               uu____70630 uu____70632 uu____70634
              in
           failwith uu____70625
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____70641 =
             let uu____70643 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____70646 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____70648 = FStar_Syntax_Print.term_to_string t0  in
             let uu____70650 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____70643
               uu____70646 uu____70648 uu____70650
              in
           failwith uu____70641
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let e = FStar_Syntax_Util.unfold_lazy i  in
           ((let uu____70660 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____70660
             then
               let uu____70665 = FStar_Syntax_Print.term_to_string t0  in
               let uu____70667 = FStar_Syntax_Print.term_to_string e  in
               FStar_Util.print2 ">> Unfolded (%s) ~> (%s)\n" uu____70665
                 uu____70667
             else ());
            encode_term e env)
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____70673 =
             let uu____70675 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____70675
              in
           failwith uu____70673
       | FStar_Syntax_Syntax.Tm_ascribed (t1,(k,uu____70684),uu____70685) ->
           let uu____70734 =
             match k with
             | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
             | uu____70744 -> false  in
           if uu____70734
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t1 env
       | FStar_Syntax_Syntax.Tm_quoted (qt,uu____70762) ->
           let tv =
             let uu____70768 =
               let uu____70775 = FStar_Reflection_Basic.inspect_ln qt  in
               FStar_Syntax_Embeddings.embed
                 FStar_Reflection_Embeddings.e_term_view uu____70775
                in
             uu____70768 t.FStar_Syntax_Syntax.pos
               FStar_Pervasives_Native.None
               FStar_Syntax_Embeddings.id_norm_cb
              in
           ((let uu____70779 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____70779
             then
               let uu____70784 = FStar_Syntax_Print.term_to_string t0  in
               let uu____70786 = FStar_Syntax_Print.term_to_string tv  in
               FStar_Util.print2 ">> Inspected (%s) ~> (%s)\n" uu____70784
                 uu____70786
             else ());
            (let t1 =
               let uu____70794 =
                 let uu____70805 = FStar_Syntax_Syntax.as_arg tv  in
                 [uu____70805]  in
               FStar_Syntax_Util.mk_app
                 (FStar_Reflection_Data.refl_constant_term
                    FStar_Reflection_Data.fstar_refl_pack_ln) uu____70794
                in
             encode_term t1 env))
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_pattern uu____70831) ->
           encode_term t1
             (let uu___1242_70849 = env  in
              {
                FStar_SMTEncoding_Env.bvar_bindings =
                  (uu___1242_70849.FStar_SMTEncoding_Env.bvar_bindings);
                FStar_SMTEncoding_Env.fvar_bindings =
                  (uu___1242_70849.FStar_SMTEncoding_Env.fvar_bindings);
                FStar_SMTEncoding_Env.depth =
                  (uu___1242_70849.FStar_SMTEncoding_Env.depth);
                FStar_SMTEncoding_Env.tcenv =
                  (uu___1242_70849.FStar_SMTEncoding_Env.tcenv);
                FStar_SMTEncoding_Env.warn =
                  (uu___1242_70849.FStar_SMTEncoding_Env.warn);
                FStar_SMTEncoding_Env.nolabels =
                  (uu___1242_70849.FStar_SMTEncoding_Env.nolabels);
                FStar_SMTEncoding_Env.use_zfuel_name =
                  (uu___1242_70849.FStar_SMTEncoding_Env.use_zfuel_name);
                FStar_SMTEncoding_Env.encode_non_total_function_typ =
                  (uu___1242_70849.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                FStar_SMTEncoding_Env.current_module_name =
                  (uu___1242_70849.FStar_SMTEncoding_Env.current_module_name);
                FStar_SMTEncoding_Env.encoding_quantifier = false;
                FStar_SMTEncoding_Env.global_cache =
                  (uu___1242_70849.FStar_SMTEncoding_Env.global_cache)
              })
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____70852) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = FStar_SMTEncoding_Env.lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____70860 = head_redex env t  in
           if uu____70860
           then let uu____70867 = whnf env t  in encode_term uu____70867 env
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
              let uu____70874 =
                if
                  fvb.FStar_SMTEncoding_Env.smt_arity > (Prims.parse_int "0")
                then
                  match tok.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.FreeV uu____70898 ->
                      let sym_name =
                        let uu____70909 =
                          FStar_Util.digest_of_string tkey_hash  in
                        Prims.op_Hat "@kick_partial_app_" uu____70909  in
                      let uu____70912 =
                        let uu____70915 =
                          let uu____70916 =
                            let uu____70924 =
                              FStar_SMTEncoding_Term.kick_partial_app tok  in
                            (uu____70924,
                              (FStar_Pervasives_Native.Some
                                 "kick_partial_app"), sym_name)
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____70916  in
                        [uu____70915]  in
                      (uu____70912, sym_name)
                  | FStar_SMTEncoding_Term.App (uu____70931,[]) ->
                      let sym_name =
                        let uu____70936 =
                          FStar_Util.digest_of_string tkey_hash  in
                        Prims.op_Hat "@kick_partial_app_" uu____70936  in
                      let uu____70939 =
                        let uu____70942 =
                          let uu____70943 =
                            let uu____70951 =
                              FStar_SMTEncoding_Term.kick_partial_app tok  in
                            (uu____70951,
                              (FStar_Pervasives_Native.Some
                                 "kick_partial_app"), sym_name)
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____70943  in
                        [uu____70942]  in
                      (uu____70939, sym_name)
                  | uu____70958 -> ([], "")
                else ([], "")  in
              match uu____70874 with
              | (aux_decls,sym_name) ->
                  let uu____70981 =
                    if aux_decls = []
                    then
                      FStar_All.pipe_right []
                        FStar_SMTEncoding_Term.mk_decls_trivial
                    else
                      FStar_SMTEncoding_Term.mk_decls sym_name tkey_hash
                        aux_decls []
                     in
                  (tok, uu____70981))
       | FStar_Syntax_Syntax.Tm_type uu____70989 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____70991) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.FStar_SMTEncoding_Env.current_module_name
              in
           let uu____71021 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____71021 with
            | (binders1,res) ->
                let uu____71032 =
                  (env.FStar_SMTEncoding_Env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____71032
                then
                  let uu____71039 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____71039 with
                   | (vars,guards,env',decls,uu____71064) ->
                       let fsym =
                         let uu____71078 =
                           let uu____71084 =
                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                               module_name "f"
                              in
                           (uu____71084, FStar_SMTEncoding_Term.Term_sort)
                            in
                         FStar_SMTEncoding_Term.mk_fv uu____71078  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____71090 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___1296_71099 =
                              env.FStar_SMTEncoding_Env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___1296_71099.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___1296_71099.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___1296_71099.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___1296_71099.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___1296_71099.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___1296_71099.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___1296_71099.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___1296_71099.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___1296_71099.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___1296_71099.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___1296_71099.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___1296_71099.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___1296_71099.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___1296_71099.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___1296_71099.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___1296_71099.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___1296_71099.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___1296_71099.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___1296_71099.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___1296_71099.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___1296_71099.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___1296_71099.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___1296_71099.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___1296_71099.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___1296_71099.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___1296_71099.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___1296_71099.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___1296_71099.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___1296_71099.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___1296_71099.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___1296_71099.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___1296_71099.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___1296_71099.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___1296_71099.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___1296_71099.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___1296_71099.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___1296_71099.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___1296_71099.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___1296_71099.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___1296_71099.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___1296_71099.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___1296_71099.FStar_TypeChecker_Env.nbe)
                            }) res
                          in
                       (match uu____71090 with
                        | (pre_opt,res_t) ->
                            let uu____71111 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____71111 with
                             | (res_pred,decls') ->
                                 let uu____71122 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____71135 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____71135, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____71139 =
                                         encode_formula pre env'  in
                                       (match uu____71139 with
                                        | (guard,decls0) ->
                                            let uu____71152 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____71152, decls0))
                                    in
                                 (match uu____71122 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____71166 =
                                          let uu____71177 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____71177)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t.FStar_Syntax_Syntax.pos
                                          uu____71166
                                         in
                                      let cvars =
                                        let uu____71197 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____71197
                                          (FStar_List.filter
                                             (fun x  ->
                                                let uu____71216 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    x
                                                   in
                                                let uu____71218 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    fsym
                                                   in
                                                uu____71216 <> uu____71218))
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
                                        let uu____71240 =
                                          FStar_Util.digest_of_string
                                            tkey_hash
                                           in
                                        Prims.op_Hat "Tm_arrow_" uu____71240
                                         in
                                      let cvar_sorts =
                                        FStar_List.map
                                          FStar_SMTEncoding_Term.fv_sort
                                          cvars
                                         in
                                      let caption =
                                        let uu____71255 =
                                          FStar_Options.log_queries ()  in
                                        if uu____71255
                                        then
                                          let uu____71258 =
                                            let uu____71260 =
                                              FStar_TypeChecker_Normalize.term_to_string
                                                env.FStar_SMTEncoding_Env.tcenv
                                                t0
                                               in
                                            FStar_Util.replace_char
                                              uu____71260 10 32
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____71258
                                        else FStar_Pervasives_Native.None  in
                                      let tdecl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (tsym, cvar_sorts,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            caption)
                                         in
                                      let t1 =
                                        let uu____71273 =
                                          let uu____71281 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              cvars
                                             in
                                          (tsym, uu____71281)  in
                                        FStar_SMTEncoding_Util.mkApp
                                          uu____71273
                                         in
                                      let t_has_kind =
                                        FStar_SMTEncoding_Term.mk_HasType t1
                                          FStar_SMTEncoding_Term.mk_Term_type
                                         in
                                      let k_assumption =
                                        let a_name =
                                          Prims.op_Hat "kinding_" tsym  in
                                        let uu____71300 =
                                          let uu____71308 =
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              ([[t_has_kind]], cvars,
                                                t_has_kind)
                                             in
                                          (uu____71308,
                                            (FStar_Pervasives_Native.Some
                                               a_name), a_name)
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____71300
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
                                        let uu____71325 =
                                          let uu____71333 =
                                            let uu____71334 =
                                              let uu____71345 =
                                                let uu____71346 =
                                                  let uu____71351 =
                                                    let uu____71352 =
                                                      FStar_SMTEncoding_Term.mk_PreType
                                                        f
                                                       in
                                                    FStar_SMTEncoding_Term.mk_tester
                                                      "Tm_arrow" uu____71352
                                                     in
                                                  (f_has_t, uu____71351)  in
                                                FStar_SMTEncoding_Util.mkImp
                                                  uu____71346
                                                 in
                                              ([[f_has_t]], (fsym :: cvars),
                                                uu____71345)
                                               in
                                            let uu____71370 =
                                              mkForall_fuel module_name
                                                t0.FStar_Syntax_Syntax.pos
                                               in
                                            uu____71370 uu____71334  in
                                          (uu____71333,
                                            (FStar_Pervasives_Native.Some
                                               "pre-typing for functions"),
                                            (Prims.op_Hat module_name
                                               (Prims.op_Hat "_" a_name)))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____71325
                                         in
                                      let t_interp1 =
                                        let a_name =
                                          Prims.op_Hat "interpretation_" tsym
                                           in
                                        let uu____71393 =
                                          let uu____71401 =
                                            let uu____71402 =
                                              let uu____71413 =
                                                FStar_SMTEncoding_Util.mkIff
                                                  (f_has_t_z, t_interp)
                                                 in
                                              ([[f_has_t_z]], (fsym ::
                                                cvars), uu____71413)
                                               in
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              uu____71402
                                             in
                                          (uu____71401,
                                            (FStar_Pervasives_Native.Some
                                               a_name),
                                            (Prims.op_Hat module_name
                                               (Prims.op_Hat "_" a_name)))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____71393
                                         in
                                      let t_decls1 =
                                        [tdecl;
                                        k_assumption;
                                        pre_typing;
                                        t_interp1]  in
                                      let uu____71436 =
                                        let uu____71437 =
                                          let uu____71440 =
                                            let uu____71443 =
                                              FStar_SMTEncoding_Term.mk_decls
                                                tsym tkey_hash t_decls1
                                                (FStar_List.append decls
                                                   (FStar_List.append decls'
                                                      guard_decls))
                                               in
                                            FStar_List.append guard_decls
                                              uu____71443
                                             in
                                          FStar_List.append decls'
                                            uu____71440
                                           in
                                        FStar_List.append decls uu____71437
                                         in
                                      (t1, uu____71436)))))
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
                     let uu____71464 =
                       let uu____71472 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____71472,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"), a_name)
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____71464  in
                   let fsym =
                     FStar_SMTEncoding_Term.mk_fv
                       ("f", FStar_SMTEncoding_Term.Term_sort)
                      in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.op_Hat "pre_typing_" tsym  in
                     let uu____71485 =
                       let uu____71493 =
                         let uu____71494 =
                           let uu____71505 =
                             let uu____71506 =
                               let uu____71511 =
                                 let uu____71512 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____71512
                                  in
                               (f_has_t, uu____71511)  in
                             FStar_SMTEncoding_Util.mkImp uu____71506  in
                           ([[f_has_t]], [fsym], uu____71505)  in
                         let uu____71538 =
                           mkForall_fuel module_name
                             t0.FStar_Syntax_Syntax.pos
                            in
                         uu____71538 uu____71494  in
                       (uu____71493, (FStar_Pervasives_Native.Some a_name),
                         a_name)
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____71485  in
                   let uu____71555 =
                     FStar_All.pipe_right [tdecl; t_kinding; t_interp]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                      in
                   (t1, uu____71555)))
       | FStar_Syntax_Syntax.Tm_refine uu____71558 ->
           let uu____71565 =
             let uu____71570 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Env.Weak;
                 FStar_TypeChecker_Env.HNF;
                 FStar_TypeChecker_Env.EraseUniverses]
                 env.FStar_SMTEncoding_Env.tcenv t0
                in
             match uu____71570 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____71577;
                 FStar_Syntax_Syntax.vars = uu____71578;_} ->
                 let uu____71585 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____71585 with
                  | (b,f1) ->
                      let uu____71610 =
                        let uu____71611 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____71611  in
                      (uu____71610, f1))
             | uu____71626 -> failwith "impossible"  in
           (match uu____71565 with
            | (x,f) ->
                let uu____71638 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____71638 with
                 | (base_t,decls) ->
                     let uu____71649 =
                       FStar_SMTEncoding_Env.gen_term_var env x  in
                     (match uu____71649 with
                      | (x1,xtm,env') ->
                          let uu____71666 = encode_formula f env'  in
                          (match uu____71666 with
                           | (refinement,decls') ->
                               let uu____71677 =
                                 FStar_SMTEncoding_Env.fresh_fvar
                                   env.FStar_SMTEncoding_Env.current_module_name
                                   "f" FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____71677 with
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
                                      let uu____71705 =
                                        let uu____71716 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____71727 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____71716
                                          uu____71727
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____71705
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun y  ->
                                              (let uu____71781 =
                                                 FStar_SMTEncoding_Term.fv_name
                                                   y
                                                  in
                                               uu____71781 <> x1) &&
                                                (let uu____71785 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     y
                                                    in
                                                 uu____71785 <> fsym)))
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
                                      let uu____71821 =
                                        FStar_Util.digest_of_string tkey_hash
                                         in
                                      Prims.op_Hat "Tm_refine_" uu____71821
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
                                      let uu____71841 =
                                        let uu____71849 =
                                          FStar_List.map
                                            FStar_SMTEncoding_Util.mkFreeV
                                            cvars1
                                           in
                                        (tsym, uu____71849)  in
                                      FStar_SMTEncoding_Util.mkApp
                                        uu____71841
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
                                      let uu____71869 =
                                        let uu____71877 =
                                          let uu____71878 =
                                            let uu____71889 =
                                              FStar_SMTEncoding_Util.mkIff
                                                (t_haseq_ref, t_haseq_base)
                                               in
                                            ([[t_haseq_ref]], cvars1,
                                              uu____71889)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            t0.FStar_Syntax_Syntax.pos
                                            uu____71878
                                           in
                                        (uu____71877,
                                          (FStar_Pervasives_Native.Some
                                             (Prims.op_Hat "haseq for " tsym)),
                                          (Prims.op_Hat "haseq" tsym))
                                         in
                                      FStar_SMTEncoding_Util.mkAssume
                                        uu____71869
                                       in
                                    let t_kinding =
                                      let uu____71903 =
                                        let uu____71911 =
                                          FStar_SMTEncoding_Term.mkForall
                                            t0.FStar_Syntax_Syntax.pos
                                            ([[t_has_kind]], cvars1,
                                              t_has_kind)
                                           in
                                        (uu____71911,
                                          (FStar_Pervasives_Native.Some
                                             "refinement kinding"),
                                          (Prims.op_Hat "refinement_kinding_"
                                             tsym))
                                         in
                                      FStar_SMTEncoding_Util.mkAssume
                                        uu____71903
                                       in
                                    let t_interp =
                                      let uu____71925 =
                                        let uu____71933 =
                                          let uu____71934 =
                                            let uu____71945 =
                                              FStar_SMTEncoding_Util.mkIff
                                                (x_has_t, encoding)
                                               in
                                            ([[x_has_t]], (ffv :: xfv ::
                                              cvars1), uu____71945)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            t0.FStar_Syntax_Syntax.pos
                                            uu____71934
                                           in
                                        (uu____71933,
                                          (FStar_Pervasives_Native.Some
                                             "refinement_interpretation"),
                                          (Prims.op_Hat
                                             "refinement_interpretation_"
                                             tsym))
                                         in
                                      FStar_SMTEncoding_Util.mkAssume
                                        uu____71925
                                       in
                                    let t_decls1 =
                                      [tdecl; t_kinding; t_interp; t_haseq1]
                                       in
                                    let uu____71977 =
                                      let uu____71978 =
                                        let uu____71981 =
                                          FStar_SMTEncoding_Term.mk_decls
                                            tsym tkey_hash t_decls1
                                            (FStar_List.append decls decls')
                                           in
                                        FStar_List.append decls' uu____71981
                                         in
                                      FStar_List.append decls uu____71978  in
                                    (t1, uu____71977))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,uu____71985) ->
           let ttm =
             let uu____72003 =
               FStar_Syntax_Unionfind.uvar_id
                 uv.FStar_Syntax_Syntax.ctx_uvar_head
                in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____72003  in
           let uu____72005 =
             encode_term_pred FStar_Pervasives_Native.None
               uv.FStar_Syntax_Syntax.ctx_uvar_typ env ttm
              in
           (match uu____72005 with
            | (t_has_k,decls) ->
                let d =
                  let uu____72017 =
                    let uu____72025 =
                      let uu____72027 =
                        let uu____72029 =
                          let uu____72031 =
                            FStar_Syntax_Unionfind.uvar_id
                              uv.FStar_Syntax_Syntax.ctx_uvar_head
                             in
                          FStar_Util.string_of_int uu____72031  in
                        FStar_Util.format1 "uvar_typing_%s" uu____72029  in
                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                        uu____72027
                       in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____72025)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____72017  in
                let uu____72037 =
                  let uu____72038 =
                    FStar_All.pipe_right [d]
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append decls uu____72038  in
                (ttm, uu____72037))
       | FStar_Syntax_Syntax.Tm_app uu____72045 ->
           let uu____72062 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____72062 with
            | (head1,args_e) ->
                let uu____72109 =
                  let uu____72124 =
                    let uu____72125 = FStar_Syntax_Subst.compress head1  in
                    uu____72125.FStar_Syntax_Syntax.n  in
                  (uu____72124, args_e)  in
                (match uu____72109 with
                 | uu____72142 when head_redex env head1 ->
                     let uu____72157 = whnf env t  in
                     encode_term uu____72157 env
                 | uu____72158 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____72181 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_fvar fv,uu____72199) when
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
                       FStar_Syntax_Syntax.pos = uu____72221;
                       FStar_Syntax_Syntax.vars = uu____72222;_},uu____72223),uu____72224)
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
                       FStar_Syntax_Syntax.pos = uu____72250;
                       FStar_Syntax_Syntax.vars = uu____72251;_},uu____72252),
                    (v0,uu____72254)::(v1,uu____72256)::(v2,uu____72258)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____72329 = encode_term v0 env  in
                     (match uu____72329 with
                      | (v01,decls0) ->
                          let uu____72340 = encode_term v1 env  in
                          (match uu____72340 with
                           | (v11,decls1) ->
                               let uu____72351 = encode_term v2 env  in
                               (match uu____72351 with
                                | (v21,decls2) ->
                                    let uu____72362 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____72362,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(v0,uu____72365)::(v1,uu____72367)::(v2,uu____72369)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____72436 = encode_term v0 env  in
                     (match uu____72436 with
                      | (v01,decls0) ->
                          let uu____72447 = encode_term v1 env  in
                          (match uu____72447 with
                           | (v11,decls1) ->
                               let uu____72458 = encode_term v2 env  in
                               (match uu____72458 with
                                | (v21,decls2) ->
                                    let uu____72469 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____72469,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____72471)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____72507)::(rng,uu____72509)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____72560) ->
                     let e0 =
                       let uu____72582 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg
                         env.FStar_SMTEncoding_Env.tcenv head1 uu____72582
                        in
                     ((let uu____72592 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug
                              env.FStar_SMTEncoding_Env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____72592
                       then
                         let uu____72597 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____72597
                       else ());
                      (let e =
                         let uu____72605 =
                           let uu____72610 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____72611 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____72610
                             uu____72611
                            in
                         uu____72605 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____72620),(arg,uu____72622)::[]) ->
                     encode_term arg env
                 | uu____72657 ->
                     let uu____72672 = encode_args args_e env  in
                     (match uu____72672 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____72733 = encode_term head1 env  in
                            match uu____72733 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____72805 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____72805 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____72903  ->
                                                 fun uu____72904  ->
                                                   match (uu____72903,
                                                           uu____72904)
                                                   with
                                                   | ((bv,uu____72934),
                                                      (a,uu____72936)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____72966 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____72966
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____72967 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm
                                             in
                                          (match uu____72967 with
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
                                                 let uu____72984 =
                                                   let uu____72992 =
                                                     FStar_SMTEncoding_Term.mkForall
                                                       t0.FStar_Syntax_Syntax.pos
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____73001 =
                                                     let uu____73003 =
                                                       let uu____73005 =
                                                         FStar_SMTEncoding_Term.hash_of_term
                                                           app_tm
                                                          in
                                                       FStar_Util.digest_of_string
                                                         uu____73005
                                                        in
                                                     Prims.op_Hat
                                                       "partial_app_typing_"
                                                       uu____73003
                                                      in
                                                   (uu____72992,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____73001)
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____72984
                                                  in
                                               let uu____73011 =
                                                 let uu____73014 =
                                                   let uu____73017 =
                                                     let uu____73020 =
                                                       FStar_SMTEncoding_Term.mk_decls
                                                         "" tkey_hash
                                                         [e_typing]
                                                         (FStar_List.append
                                                            decls
                                                            (FStar_List.append
                                                               decls' decls''))
                                                        in
                                                     FStar_List.append
                                                       decls'' uu____73020
                                                      in
                                                   FStar_List.append decls'
                                                     uu____73017
                                                    in
                                                 FStar_List.append decls
                                                   uu____73014
                                                  in
                                               (app_tm, uu____73011))))
                             in
                          let encode_full_app fv =
                            let uu____73040 =
                              FStar_SMTEncoding_Env.lookup_free_var_sym env
                                fv
                               in
                            match uu____73040 with
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
                                   FStar_Syntax_Syntax.pos = uu____73083;
                                   FStar_Syntax_Syntax.vars = uu____73084;_},uu____73085)
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
                                   FStar_Syntax_Syntax.pos = uu____73092;
                                   FStar_Syntax_Syntax.vars = uu____73093;_},uu____73094)
                                ->
                                let uu____73099 =
                                  let uu____73100 =
                                    let uu____73105 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____73105
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____73100
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____73099
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____73135 =
                                  let uu____73136 =
                                    let uu____73141 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____73141
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____73136
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____73135
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____73170,(FStar_Util.Inl t1,uu____73172),uu____73173)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____73220,(FStar_Util.Inr c,uu____73222),uu____73223)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____73270 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____73291 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Env.Weak;
                                     FStar_TypeChecker_Env.HNF;
                                     FStar_TypeChecker_Env.EraseUniverses]
                                     env.FStar_SMTEncoding_Env.tcenv
                                     head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____73291
                                  in
                               let uu____73292 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____73292 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____73308;
                                            FStar_Syntax_Syntax.vars =
                                              uu____73309;_},uu____73310)
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
                                     | uu____73328 ->
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
           let uu____73407 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____73407 with
            | (bs1,body1,opening) ->
                let fallback uu____73430 =
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
                  let uu____73440 =
                    let uu____73441 =
                      FStar_SMTEncoding_Term.mk_fv
                        (f, FStar_SMTEncoding_Term.Term_sort)
                       in
                    FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV
                      uu____73441
                     in
                  let uu____73443 =
                    FStar_All.pipe_right [decl]
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  (uu____73440, uu____73443)  in
                let is_impure rc =
                  let uu____73453 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                      env.FStar_SMTEncoding_Env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____73453 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____73468 =
                          let uu____73481 =
                            FStar_TypeChecker_Env.get_range
                              env.FStar_SMTEncoding_Env.tcenv
                             in
                          FStar_TypeChecker_Util.new_implicit_var
                            "SMTEncoding codomain" uu____73481
                            env.FStar_SMTEncoding_Env.tcenv
                            FStar_Syntax_Util.ktype0
                           in
                        (match uu____73468 with
                         | (t1,uu____73484,uu____73485) -> t1)
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  let uu____73503 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                     in
                  if uu____73503
                  then
                    let uu____73508 = FStar_Syntax_Syntax.mk_Total res_typ
                       in
                    FStar_Pervasives_Native.Some uu____73508
                  else
                    (let uu____73511 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid
                        in
                     if uu____73511
                     then
                       let uu____73516 =
                         FStar_Syntax_Syntax.mk_GTotal res_typ  in
                       FStar_Pervasives_Native.Some uu____73516
                     else FStar_Pervasives_Native.None)
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____73524 =
                         let uu____73530 =
                           let uu____73532 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____73532
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____73530)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____73524);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____73537 =
                       (is_impure rc) &&
                         (let uu____73540 =
                            FStar_TypeChecker_Env.is_reifiable_rc
                              env.FStar_SMTEncoding_Env.tcenv rc
                             in
                          Prims.op_Negation uu____73540)
                        in
                     if uu____73537
                     then fallback ()
                     else
                       (let uu____73549 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____73549 with
                        | (vars,guards,envbody,decls,uu____73574) ->
                            let body2 =
                              let uu____73588 =
                                FStar_TypeChecker_Env.is_reifiable_rc
                                  env.FStar_SMTEncoding_Env.tcenv rc
                                 in
                              if uu____73588
                              then
                                FStar_TypeChecker_Util.reify_body
                                  env.FStar_SMTEncoding_Env.tcenv body1
                              else body1  in
                            let uu____73593 = encode_term body2 envbody  in
                            (match uu____73593 with
                             | (body3,decls') ->
                                 let uu____73604 =
                                   let uu____73613 = codomain_eff rc  in
                                   match uu____73613 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____73632 = encode_term tfun env
                                          in
                                       (match uu____73632 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____73604 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____73666 =
                                          let uu____73677 =
                                            let uu____73678 =
                                              let uu____73683 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____73683, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____73678
                                             in
                                          ([], vars, uu____73677)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t0.FStar_Syntax_Syntax.pos
                                          uu____73666
                                         in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body
                                         in
                                      let uu____73691 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            (cvars, key_body)
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____73707 =
                                              let uu____73710 =
                                                let uu____73721 =
                                                  FStar_SMTEncoding_Term.free_variables
                                                    t1
                                                   in
                                                FStar_List.append uu____73721
                                                  cvars
                                                 in
                                              FStar_Util.remove_dups
                                                FStar_SMTEncoding_Term.fv_eq
                                                uu____73710
                                               in
                                            let uu____73748 =
                                              FStar_SMTEncoding_Util.mkAnd
                                                (key_body, t1)
                                               in
                                            (uu____73707, uu____73748)
                                         in
                                      (match uu____73691 with
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
                                           let uu____73770 =
                                             is_an_eta_expansion env vars
                                               body3
                                              in
                                           (match uu____73770 with
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
                                                  let uu____73786 =
                                                    FStar_Util.digest_of_string
                                                      tkey_hash
                                                     in
                                                  Prims.op_Hat "Tm_abs_"
                                                    uu____73786
                                                   in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None)
                                                   in
                                                let f =
                                                  let uu____73795 =
                                                    let uu____73803 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    (fsym, uu____73803)  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____73795
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
                                                      let uu____73820 =
                                                        let uu____73821 =
                                                          let uu____73829 =
                                                            FStar_SMTEncoding_Term.mkForall
                                                              t0.FStar_Syntax_Syntax.pos
                                                              ([[f]], cvars1,
                                                                f_has_t)
                                                             in
                                                          (uu____73829,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name)
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____73821
                                                         in
                                                      [uu____73820]
                                                   in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.op_Hat
                                                      "interpretation_" fsym
                                                     in
                                                  let uu____73844 =
                                                    let uu____73852 =
                                                      let uu____73853 =
                                                        let uu____73864 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3)
                                                           in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____73864)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        t0.FStar_Syntax_Syntax.pos
                                                        uu____73853
                                                       in
                                                    (uu____73852,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____73844
                                                   in
                                                let f_decls =
                                                  FStar_List.append (fdecl ::
                                                    typing_f) [interp_f]
                                                   in
                                                let uu____73878 =
                                                  let uu____73879 =
                                                    let uu____73882 =
                                                      let uu____73885 =
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
                                                        decls'' uu____73885
                                                       in
                                                    FStar_List.append decls'
                                                      uu____73882
                                                     in
                                                  FStar_List.append decls
                                                    uu____73879
                                                   in
                                                (f, uu____73878))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____73888,{
                           FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                             uu____73889;
                           FStar_Syntax_Syntax.lbunivs = uu____73890;
                           FStar_Syntax_Syntax.lbtyp = uu____73891;
                           FStar_Syntax_Syntax.lbeff = uu____73892;
                           FStar_Syntax_Syntax.lbdef = uu____73893;
                           FStar_Syntax_Syntax.lbattrs = uu____73894;
                           FStar_Syntax_Syntax.lbpos = uu____73895;_}::uu____73896),uu____73897)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____73931;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____73933;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____73935;
                FStar_Syntax_Syntax.lbpos = uu____73936;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____73963 ->
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
              let uu____74035 =
                let uu____74040 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____74040 env  in
              match uu____74035 with
              | (ee1,decls1) ->
                  let uu____74065 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____74065 with
                   | (xs,e21) ->
                       let uu____74090 = FStar_List.hd xs  in
                       (match uu____74090 with
                        | (x1,uu____74108) ->
                            let env' =
                              FStar_SMTEncoding_Env.push_term_var env x1 ee1
                               in
                            let uu____74114 = encode_body e21 env'  in
                            (match uu____74114 with
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
            let uu____74144 =
              let uu____74152 =
                let uu____74153 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____74153  in
              FStar_SMTEncoding_Env.gen_term_var env uu____74152  in
            match uu____74144 with
            | (scrsym,scr',env1) ->
                let uu____74163 = encode_term e env1  in
                (match uu____74163 with
                 | (scr,decls) ->
                     let uu____74174 =
                       let encode_branch b uu____74203 =
                         match uu____74203 with
                         | (else_case,decls1) ->
                             let uu____74222 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____74222 with
                              | (p,w,br) ->
                                  let uu____74248 = encode_pat env1 p  in
                                  (match uu____74248 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____74285  ->
                                                   match uu____74285 with
                                                   | (x,t) ->
                                                       FStar_SMTEncoding_Env.push_term_var
                                                         env2 x t) env1)
                                          in
                                       let uu____74292 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____74314 =
                                               encode_term w1 env2  in
                                             (match uu____74314 with
                                              | (w2,decls2) ->
                                                  let uu____74327 =
                                                    let uu____74328 =
                                                      let uu____74333 =
                                                        let uu____74334 =
                                                          let uu____74339 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____74339)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____74334
                                                         in
                                                      (guard, uu____74333)
                                                       in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____74328
                                                     in
                                                  (uu____74327, decls2))
                                          in
                                       (match uu____74292 with
                                        | (guard1,decls2) ->
                                            let uu____74354 =
                                              encode_br br env2  in
                                            (match uu____74354 with
                                             | (br1,decls3) ->
                                                 let uu____74367 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____74367,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____74174 with
                      | (match_tm,decls1) ->
                          let uu____74388 =
                            let uu____74389 =
                              let uu____74400 =
                                let uu____74407 =
                                  let uu____74412 =
                                    FStar_SMTEncoding_Term.mk_fv
                                      (scrsym,
                                        FStar_SMTEncoding_Term.Term_sort)
                                     in
                                  (uu____74412, scr)  in
                                [uu____74407]  in
                              (uu____74400, match_tm)  in
                            FStar_SMTEncoding_Term.mkLet' uu____74389
                              FStar_Range.dummyRange
                             in
                          (uu____74388, decls1)))

and (encode_pat :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.pat -> (FStar_SMTEncoding_Env.env_t * pattern))
  =
  fun env  ->
    fun pat  ->
      (let uu____74435 =
         FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
           FStar_Options.Medium
          in
       if uu____74435
       then
         let uu____74438 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____74438
       else ());
      (let uu____74443 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____74443 with
       | (vars,pat_term) ->
           let uu____74460 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____74502  ->
                     fun v1  ->
                       match uu____74502 with
                       | (env1,vars1) ->
                           let uu____74538 =
                             FStar_SMTEncoding_Env.gen_term_var env1 v1  in
                           (match uu____74538 with
                            | (xx,uu____74557,env2) ->
                                let uu____74561 =
                                  let uu____74568 =
                                    let uu____74573 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xx,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    (v1, uu____74573)  in
                                  uu____74568 :: vars1  in
                                (env2, uu____74561))) (env, []))
              in
           (match uu____74460 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____74628 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____74629 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____74630 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____74638 = encode_const c env1  in
                      (match uu____74638 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____74646::uu____74647 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____74651 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon
                            env1.FStar_SMTEncoding_Env.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____74674 =
                          FStar_TypeChecker_Env.datacons_of_typ
                            env1.FStar_SMTEncoding_Env.tcenv tc_name
                           in
                        match uu____74674 with
                        | (uu____74682,uu____74683::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____74688 ->
                            FStar_SMTEncoding_Env.mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____74724  ->
                                  match uu____74724 with
                                  | (arg,uu____74734) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____74743 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____74743))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____74775) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____74806 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____74831 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____74877  ->
                                  match uu____74877 with
                                  | (arg,uu____74893) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____74902 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____74902))
                         in
                      FStar_All.pipe_right uu____74831 FStar_List.flatten
                   in
                let pat_term1 uu____74933 = encode_term pat_term env1  in
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
      let uu____74943 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____74991  ->
                fun uu____74992  ->
                  match (uu____74991, uu____74992) with
                  | ((tms,decls),(t,uu____75032)) ->
                      let uu____75059 = encode_term t env  in
                      (match uu____75059 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____74943 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____75116 = FStar_Syntax_Util.list_elements e  in
        match uu____75116 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____75147 =
          let uu____75164 = FStar_Syntax_Util.unmeta p  in
          FStar_All.pipe_right uu____75164 FStar_Syntax_Util.head_and_args
           in
        match uu____75147 with
        | (head1,args) ->
            let uu____75215 =
              let uu____75230 =
                let uu____75231 = FStar_Syntax_Util.un_uinst head1  in
                uu____75231.FStar_Syntax_Syntax.n  in
              (uu____75230, args)  in
            (match uu____75215 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____75253,uu____75254)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____75306 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or1 t1 =
          let uu____75361 =
            let uu____75378 = FStar_Syntax_Util.unmeta t1  in
            FStar_All.pipe_right uu____75378 FStar_Syntax_Util.head_and_args
             in
          match uu____75361 with
          | (head1,args) ->
              let uu____75425 =
                let uu____75440 =
                  let uu____75441 = FStar_Syntax_Util.un_uinst head1  in
                  uu____75441.FStar_Syntax_Syntax.n  in
                (uu____75440, args)  in
              (match uu____75425 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____75460)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____75497 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____75527 = smt_pat_or1 t1  in
            (match uu____75527 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____75549 = list_elements1 e  in
                 FStar_All.pipe_right uu____75549
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____75579 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____75579
                           (FStar_List.map one_pat)))
             | uu____75602 ->
                 let uu____75607 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____75607])
        | uu____75658 ->
            let uu____75661 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____75661]
         in
      let uu____75712 =
        let uu____75727 =
          let uu____75728 = FStar_Syntax_Subst.compress t  in
          uu____75728.FStar_Syntax_Syntax.n  in
        match uu____75727 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____75767 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____75767 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____75802;
                        FStar_Syntax_Syntax.effect_name = uu____75803;
                        FStar_Syntax_Syntax.result_typ = uu____75804;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____75806)::(post,uu____75808)::(pats,uu____75810)::[];
                        FStar_Syntax_Syntax.flags = uu____75811;_}
                      ->
                      let uu____75872 = lemma_pats pats  in
                      (binders1, pre, post, uu____75872)
                  | uu____75883 -> failwith "impos"))
        | uu____75899 -> failwith "Impos"  in
      match uu____75712 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___1940_75936 = env  in
            {
              FStar_SMTEncoding_Env.bvar_bindings =
                (uu___1940_75936.FStar_SMTEncoding_Env.bvar_bindings);
              FStar_SMTEncoding_Env.fvar_bindings =
                (uu___1940_75936.FStar_SMTEncoding_Env.fvar_bindings);
              FStar_SMTEncoding_Env.depth =
                (uu___1940_75936.FStar_SMTEncoding_Env.depth);
              FStar_SMTEncoding_Env.tcenv =
                (uu___1940_75936.FStar_SMTEncoding_Env.tcenv);
              FStar_SMTEncoding_Env.warn =
                (uu___1940_75936.FStar_SMTEncoding_Env.warn);
              FStar_SMTEncoding_Env.nolabels =
                (uu___1940_75936.FStar_SMTEncoding_Env.nolabels);
              FStar_SMTEncoding_Env.use_zfuel_name = true;
              FStar_SMTEncoding_Env.encode_non_total_function_typ =
                (uu___1940_75936.FStar_SMTEncoding_Env.encode_non_total_function_typ);
              FStar_SMTEncoding_Env.current_module_name =
                (uu___1940_75936.FStar_SMTEncoding_Env.current_module_name);
              FStar_SMTEncoding_Env.encoding_quantifier =
                (uu___1940_75936.FStar_SMTEncoding_Env.encoding_quantifier);
              FStar_SMTEncoding_Env.global_cache =
                (uu___1940_75936.FStar_SMTEncoding_Env.global_cache)
            }  in
          let uu____75938 =
            encode_binders FStar_Pervasives_Native.None binders env1  in
          (match uu____75938 with
           | (vars,guards,env2,decls,uu____75963) ->
               let uu____75976 = encode_smt_patterns patterns env2  in
               (match uu____75976 with
                | (pats,decls') ->
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
                    let env3 =
                      let uu___1953_76003 = env2  in
                      {
                        FStar_SMTEncoding_Env.bvar_bindings =
                          (uu___1953_76003.FStar_SMTEncoding_Env.bvar_bindings);
                        FStar_SMTEncoding_Env.fvar_bindings =
                          (uu___1953_76003.FStar_SMTEncoding_Env.fvar_bindings);
                        FStar_SMTEncoding_Env.depth =
                          (uu___1953_76003.FStar_SMTEncoding_Env.depth);
                        FStar_SMTEncoding_Env.tcenv =
                          (uu___1953_76003.FStar_SMTEncoding_Env.tcenv);
                        FStar_SMTEncoding_Env.warn =
                          (uu___1953_76003.FStar_SMTEncoding_Env.warn);
                        FStar_SMTEncoding_Env.nolabels = true;
                        FStar_SMTEncoding_Env.use_zfuel_name =
                          (uu___1953_76003.FStar_SMTEncoding_Env.use_zfuel_name);
                        FStar_SMTEncoding_Env.encode_non_total_function_typ =
                          (uu___1953_76003.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                        FStar_SMTEncoding_Env.current_module_name =
                          (uu___1953_76003.FStar_SMTEncoding_Env.current_module_name);
                        FStar_SMTEncoding_Env.encoding_quantifier =
                          (uu___1953_76003.FStar_SMTEncoding_Env.encoding_quantifier);
                        FStar_SMTEncoding_Env.global_cache =
                          (uu___1953_76003.FStar_SMTEncoding_Env.global_cache)
                      }  in
                    let uu____76005 =
                      let uu____76010 = FStar_Syntax_Util.unmeta pre  in
                      encode_formula uu____76010 env3  in
                    (match uu____76005 with
                     | (pre1,decls'') ->
                         let uu____76017 =
                           let uu____76022 = FStar_Syntax_Util.unmeta post1
                              in
                           encode_formula uu____76022 env3  in
                         (match uu____76017 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append decls'
                                     (FStar_List.append decls'' decls'''))
                                 in
                              let uu____76032 =
                                let uu____76033 =
                                  let uu____76044 =
                                    let uu____76045 =
                                      let uu____76050 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards)
                                         in
                                      (uu____76050, post2)  in
                                    FStar_SMTEncoding_Util.mkImp uu____76045
                                     in
                                  (pats, vars, uu____76044)  in
                                FStar_SMTEncoding_Term.mkForall
                                  t.FStar_Syntax_Syntax.pos uu____76033
                                 in
                              (uu____76032, decls1)))))

and (encode_smt_patterns :
  FStar_Syntax_Syntax.arg Prims.list Prims.list ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term Prims.list Prims.list *
        FStar_SMTEncoding_Term.decls_t))
  =
  fun pats_l  ->
    fun env  ->
      let env1 =
        let uu___1965_76070 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___1965_76070.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___1965_76070.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___1965_76070.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___1965_76070.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___1965_76070.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___1965_76070.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___1965_76070.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___1965_76070.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___1965_76070.FStar_SMTEncoding_Env.encoding_quantifier);
          FStar_SMTEncoding_Env.global_cache =
            (uu___1965_76070.FStar_SMTEncoding_Env.global_cache)
        }  in
      let encode_smt_pattern t =
        let uu____76086 = FStar_Syntax_Util.head_and_args t  in
        match uu____76086 with
        | (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____76149::(x,uu____76151)::(t1,uu____76153)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____76220 = encode_term x env1  in
                 (match uu____76220 with
                  | (x1,decls) ->
                      let uu____76231 = encode_term t1 env1  in
                      (match uu____76231 with
                       | (t2,decls') ->
                           let uu____76242 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                           (uu____76242, (FStar_List.append decls decls'))))
             | uu____76243 -> encode_term t env1)
         in
      FStar_List.fold_right
        (fun pats  ->
           fun uu____76286  ->
             match uu____76286 with
             | (pats_l1,decls) ->
                 let uu____76331 =
                   FStar_List.fold_right
                     (fun uu____76366  ->
                        fun uu____76367  ->
                          match (uu____76366, uu____76367) with
                          | ((p,uu____76409),(pats1,decls1)) ->
                              let uu____76444 = encode_smt_pattern p  in
                              (match uu____76444 with
                               | (t,d) ->
                                   let uu____76459 =
                                     FStar_SMTEncoding_Term.check_pattern_ok
                                       t
                                      in
                                   (match uu____76459 with
                                    | FStar_Pervasives_Native.None  ->
                                        ((t :: pats1),
                                          (FStar_List.append d decls1))
                                    | FStar_Pervasives_Native.Some
                                        illegal_subterm ->
                                        ((let uu____76476 =
                                            let uu____76482 =
                                              let uu____76484 =
                                                FStar_Syntax_Print.term_to_string
                                                  p
                                                 in
                                              let uu____76486 =
                                                FStar_SMTEncoding_Term.print_smt_term
                                                  illegal_subterm
                                                 in
                                              FStar_Util.format2
                                                "Pattern %s contains illegal sub-term (%s); dropping it"
                                                uu____76484 uu____76486
                                               in
                                            (FStar_Errors.Warning_SMTPatternIllFormed,
                                              uu____76482)
                                             in
                                          FStar_Errors.log_issue
                                            p.FStar_Syntax_Syntax.pos
                                            uu____76476);
                                         (pats1,
                                           (FStar_List.append d decls1))))))
                     pats ([], decls)
                    in
                 (match uu____76331 with
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
        let uu____76546 =
          FStar_All.pipe_left
            (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____76546
        then
          let uu____76551 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____76553 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____76551 uu____76553
        else ()  in
      let enc f r l =
        let uu____76595 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____76627 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____76627 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____76595 with
        | (decls,args) ->
            let uu____76658 =
              let uu___2029_76659 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___2029_76659.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___2029_76659.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____76658, decls)
         in
      let const_op f r uu____76694 =
        let uu____76707 = f r  in (uu____76707, [])  in
      let un_op f l =
        let uu____76730 = FStar_List.hd l  in
        FStar_All.pipe_left f uu____76730  in
      let bin_op f uu___632_76750 =
        match uu___632_76750 with
        | t1::t2::[] -> f (t1, t2)
        | uu____76761 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____76802 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____76827  ->
                 match uu____76827 with
                 | (t,uu____76843) ->
                     let uu____76848 = encode_formula t env  in
                     (match uu____76848 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____76802 with
        | (decls,phis) ->
            let uu____76877 =
              let uu___2059_76878 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___2059_76878.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___2059_76878.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____76877, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____76941  ->
               match uu____76941 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____76962) -> false
                    | uu____76965 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____76984 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____76984
        else
          (let uu____77001 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____77001 r rf)
         in
      let eq3_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____77069 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::t1::v0::v1::[] ->
                     let uu____77101 =
                       let uu____77106 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____77107 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____77106, uu____77107)  in
                     FStar_SMTEncoding_Util.mkAnd uu____77101
                 | uu____77108 -> failwith "Impossible")
             in
          uu____77069 r args
        else
          (let uu____77114 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____77114)
         in
      let h_equals_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____77176 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::v0::t1::v1::[] ->
                     let uu____77208 =
                       let uu____77213 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____77214 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____77213, uu____77214)  in
                     FStar_SMTEncoding_Util.mkAnd uu____77208
                 | uu____77215 -> failwith "Impossible")
             in
          uu____77176 r args
        else
          (let uu____77221 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____77221)
         in
      let mk_imp1 r uu___633_77250 =
        match uu___633_77250 with
        | (lhs,uu____77256)::(rhs,uu____77258)::[] ->
            let uu____77299 = encode_formula rhs env  in
            (match uu____77299 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____77314) ->
                      (l1, decls1)
                  | uu____77319 ->
                      let uu____77320 = encode_formula lhs env  in
                      (match uu____77320 with
                       | (l2,decls2) ->
                           let uu____77331 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____77331, (FStar_List.append decls1 decls2)))))
        | uu____77332 -> failwith "impossible"  in
      let mk_ite r uu___634_77360 =
        match uu___634_77360 with
        | (guard,uu____77366)::(_then,uu____77368)::(_else,uu____77370)::[]
            ->
            let uu____77427 = encode_formula guard env  in
            (match uu____77427 with
             | (g,decls1) ->
                 let uu____77438 = encode_formula _then env  in
                 (match uu____77438 with
                  | (t,decls2) ->
                      let uu____77449 = encode_formula _else env  in
                      (match uu____77449 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____77461 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____77491 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l
           in
        f uu____77491  in
      let connectives =
        let uu____77521 =
          let uu____77546 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____77546)  in
        let uu____77589 =
          let uu____77616 =
            let uu____77641 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____77641)  in
          let uu____77684 =
            let uu____77711 =
              let uu____77738 =
                let uu____77763 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____77763)  in
              let uu____77806 =
                let uu____77833 =
                  let uu____77860 =
                    let uu____77885 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____77885)  in
                  [uu____77860;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.c_eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq3_op);
                  (FStar_Parser_Const.c_eq3_lid, h_equals_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____77833  in
              uu____77738 :: uu____77806  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____77711  in
          uu____77616 :: uu____77684  in
        uu____77521 :: uu____77589  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____78430 = encode_formula phi' env  in
            (match uu____78430 with
             | (phi2,decls) ->
                 let uu____78441 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____78441, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____78443 ->
            let uu____78450 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____78450 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____78489 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____78489 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____78501;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____78503;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____78505;
                 FStar_Syntax_Syntax.lbpos = uu____78506;_}::[]),e2)
            ->
            let uu____78533 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____78533 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____78586::(x,uu____78588)::(t,uu____78590)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____78657 = encode_term x env  in
                 (match uu____78657 with
                  | (x1,decls) ->
                      let uu____78668 = encode_term t env  in
                      (match uu____78668 with
                       | (t1,decls') ->
                           let uu____78679 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____78679, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____78682)::(msg,uu____78684)::(phi2,uu____78686)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____78753 =
                   let uu____78758 =
                     let uu____78759 = FStar_Syntax_Subst.compress r  in
                     uu____78759.FStar_Syntax_Syntax.n  in
                   let uu____78762 =
                     let uu____78763 = FStar_Syntax_Subst.compress msg  in
                     uu____78763.FStar_Syntax_Syntax.n  in
                   (uu____78758, uu____78762)  in
                 (match uu____78753 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____78772))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____78783 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____78790)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____78825 when head_redex env head2 ->
                 let uu____78840 = whnf env phi1  in
                 encode_formula uu____78840 env
             | uu____78841 ->
                 let uu____78856 = encode_term phi1 env  in
                 (match uu____78856 with
                  | (tt,decls) ->
                      let tt1 =
                        let uu____78868 =
                          let uu____78870 =
                            FStar_Range.use_range
                              tt.FStar_SMTEncoding_Term.rng
                             in
                          let uu____78871 =
                            FStar_Range.use_range
                              phi1.FStar_Syntax_Syntax.pos
                             in
                          FStar_Range.rng_included uu____78870 uu____78871
                           in
                        if uu____78868
                        then tt
                        else
                          (let uu___2246_78875 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___2246_78875.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___2246_78875.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      let uu____78876 = FStar_SMTEncoding_Term.mk_Valid tt1
                         in
                      (uu____78876, decls)))
        | uu____78877 ->
            let uu____78878 = encode_term phi1 env  in
            (match uu____78878 with
             | (tt,decls) ->
                 let tt1 =
                   let uu____78890 =
                     let uu____78892 =
                       FStar_Range.use_range tt.FStar_SMTEncoding_Term.rng
                        in
                     let uu____78893 =
                       FStar_Range.use_range phi1.FStar_Syntax_Syntax.pos  in
                     FStar_Range.rng_included uu____78892 uu____78893  in
                   if uu____78890
                   then tt
                   else
                     (let uu___2254_78897 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___2254_78897.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___2254_78897.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 let uu____78898 = FStar_SMTEncoding_Term.mk_Valid tt1  in
                 (uu____78898, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____78942 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____78942 with
        | (vars,guards,env2,decls,uu____78981) ->
            let uu____78994 = encode_smt_patterns ps env2  in
            (match uu____78994 with
             | (pats,decls') ->
                 let uu____79031 = encode_formula body env2  in
                 (match uu____79031 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____79063;
                             FStar_SMTEncoding_Term.rng = uu____79064;_}::[])::[]
                            when
                            let uu____79084 =
                              FStar_Ident.text_of_lid
                                FStar_Parser_Const.guard_free
                               in
                            uu____79084 = gf -> []
                        | uu____79087 -> guards  in
                      let uu____79092 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____79092, body1,
                        (FStar_List.append decls
                           (FStar_List.append decls' decls'')))))
         in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi  in
       let uu____79103 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____79103 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____79112 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____79218  ->
                     match uu____79218 with
                     | (l,uu____79243) -> FStar_Ident.lid_equals op l))
              in
           (match uu____79112 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____79312,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____79404 = encode_q_body env vars pats body  in
             match uu____79404 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____79449 =
                     let uu____79460 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____79460)  in
                   FStar_SMTEncoding_Term.mkForall
                     phi1.FStar_Syntax_Syntax.pos uu____79449
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____79491 = encode_q_body env vars pats body  in
             match uu____79491 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____79535 =
                   let uu____79536 =
                     let uu____79547 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____79547)  in
                   FStar_SMTEncoding_Term.mkExists
                     phi1.FStar_Syntax_Syntax.pos uu____79536
                    in
                 (uu____79535, decls))))
