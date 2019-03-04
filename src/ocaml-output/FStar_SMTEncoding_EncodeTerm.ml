open Prims
let mkForall_fuel' :
  'Auu____71273 .
    Prims.string ->
      FStar_Range.range ->
        'Auu____71273 ->
          (FStar_SMTEncoding_Term.pat Prims.list Prims.list *
            FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term) ->
            FStar_SMTEncoding_Term.term
  =
  fun mname  ->
    fun r  ->
      fun n1  ->
        fun uu____71304  ->
          match uu____71304 with
          | (pats,vars,body) ->
              let fallback uu____71332 =
                FStar_SMTEncoding_Term.mkForall r (pats, vars, body)  in
              let uu____71337 = FStar_Options.unthrottle_inductives ()  in
              if uu____71337
              then fallback ()
              else
                (let uu____71342 =
                   FStar_SMTEncoding_Env.fresh_fvar mname "f"
                     FStar_SMTEncoding_Term.Fuel_sort
                    in
                 match uu____71342 with
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
                               | uu____71382 -> p))
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
                                 let uu____71403 = add_fuel1 guards  in
                                 FStar_SMTEncoding_Util.mk_and_l uu____71403
                             | uu____71406 ->
                                 let uu____71407 = add_fuel1 [guard]  in
                                 FStar_All.pipe_right uu____71407
                                   FStar_List.hd
                              in
                           FStar_SMTEncoding_Util.mkImp (guard1, body')
                       | uu____71412 -> body  in
                     let vars1 =
                       let uu____71424 =
                         FStar_SMTEncoding_Term.mk_fv
                           (fsym, FStar_SMTEncoding_Term.Fuel_sort)
                          in
                       uu____71424 :: vars  in
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
      | FStar_Syntax_Syntax.Tm_arrow uu____71488 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____71504 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____71512 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____71514 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____71528 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____71548 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____71551 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____71551 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____71570;
             FStar_Syntax_Syntax.vars = uu____71571;_},uu____71572)
          ->
          let uu____71597 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____71597 FStar_Option.isNone
      | uu____71615 -> false
  
let (head_redex :
  FStar_SMTEncoding_Env.env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____71629 =
        let uu____71630 = FStar_Syntax_Util.un_uinst t  in
        uu____71630.FStar_Syntax_Syntax.n  in
      match uu____71629 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____71634,uu____71635,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___630_71660  ->
                  match uu___630_71660 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____71663 -> false)
               rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____71666 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____71666 FStar_Option.isSome
      | uu____71684 -> false
  
let (whnf :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____71697 = head_normal env t  in
      if uu____71697
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
    let uu____71719 =
      let uu____71720 = FStar_Syntax_Syntax.null_binder t  in [uu____71720]
       in
    let uu____71739 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    FStar_Syntax_Util.abs uu____71719 uu____71739
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
                let uu____71761 = FStar_SMTEncoding_Term.fv_sort var  in
                match uu____71761 with
                | FStar_SMTEncoding_Term.Fuel_sort  ->
                    let uu____71762 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____71762
                | s ->
                    let uu____71765 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____71765) e)
  
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
          let uu____71821 =
            let uu____71827 =
              let uu____71829 = FStar_Util.string_of_int arity  in
              let uu____71831 = FStar_Util.string_of_int n_args  in
              FStar_Util.format3
                "Head symbol %s expects at least %s arguments; got only %s"
                head1 uu____71829 uu____71831
               in
            (FStar_Errors.Fatal_SMTEncodingArityMismatch, uu____71827)  in
          FStar_Errors.raise_error uu____71821 rng
  
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
                  (let uu____71890 = FStar_Util.first_N arity args  in
                   match uu____71890 with
                   | (args1,rest) ->
                       let head3 =
                         FStar_SMTEncoding_Util.mkApp' (head2, args1)  in
                       mk_Apply_args head3 rest)
                else
                  (let uu____71914 =
                     FStar_SMTEncoding_Term.op_to_string head2  in
                   raise_arity_mismatch uu____71914 arity n_args rng)
  
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
          let uu____71941 = FStar_SMTEncoding_Env.force_thunk fvb  in
          mk_Apply_args uu____71941 args
        else
          maybe_curry_app rng
            (FStar_Util.Inl
               (FStar_SMTEncoding_Term.Var (fvb.FStar_SMTEncoding_Env.smt_id)))
            fvb.FStar_SMTEncoding_Env.smt_arity args
  
let (is_app : FStar_SMTEncoding_Term.op -> Prims.bool) =
  fun uu___631_71950  ->
    match uu___631_71950 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____71956 -> false
  
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
                       FStar_SMTEncoding_Term.freevars = uu____72004;
                       FStar_SMTEncoding_Term.rng = uu____72005;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____72036) ->
              let uu____72046 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____72063 -> false) args (FStar_List.rev xs))
                 in
              if uu____72046
              then FStar_SMTEncoding_Env.tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____72070,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t  in
              let uu____72074 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____72082 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars
                           in
                        Prims.op_Negation uu____72082))
                 in
              if uu____72074
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____72089 -> FStar_Pervasives_Native.None  in
        check_partial_applications body (FStar_List.rev vars)
  
let check_pattern_vars :
  'Auu____72107 'Auu____72108 .
    FStar_SMTEncoding_Env.env_t ->
      (FStar_Syntax_Syntax.bv * 'Auu____72107) Prims.list ->
        (FStar_Syntax_Syntax.term * 'Auu____72108) Prims.list -> unit
  =
  fun env  ->
    fun vars  ->
      fun pats  ->
        let pats1 =
          FStar_All.pipe_right pats
            (FStar_List.map
               (fun uu____72166  ->
                  match uu____72166 with
                  | (x,uu____72172) ->
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
              let uu____72180 = FStar_Syntax_Free.names hd1  in
              FStar_List.fold_left
                (fun out  ->
                   fun x  ->
                     let uu____72192 = FStar_Syntax_Free.names x  in
                     FStar_Util.set_union out uu____72192) uu____72180 tl1
               in
            let uu____72195 =
              FStar_All.pipe_right vars
                (FStar_Util.find_opt
                   (fun uu____72222  ->
                      match uu____72222 with
                      | (b,uu____72229) ->
                          let uu____72230 = FStar_Util.set_mem b pat_vars  in
                          Prims.op_Negation uu____72230))
               in
            (match uu____72195 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some (x,uu____72237) ->
                 let pos =
                   FStar_List.fold_left
                     (fun out  ->
                        fun t  ->
                          FStar_Range.union_ranges out
                            t.FStar_Syntax_Syntax.pos)
                     hd1.FStar_Syntax_Syntax.pos tl1
                    in
                 let uu____72251 =
                   let uu____72257 =
                     let uu____72259 = FStar_Syntax_Print.bv_to_string x  in
                     FStar_Util.format1
                       "SMT pattern misses at least one bound variable: %s"
                       uu____72259
                      in
                   (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                     uu____72257)
                    in
                 FStar_Errors.log_issue pos uu____72251)
  
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
        | FStar_Syntax_Syntax.Tm_arrow uu____72545 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____72560 ->
            let uu____72567 = FStar_Syntax_Util.unrefine t1  in
            aux true uu____72567
        | uu____72569 ->
            if norm1
            then let uu____72571 = whnf env t1  in aux false uu____72571
            else
              (let uu____72575 =
                 let uu____72577 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let uu____72579 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____72577 uu____72579
                  in
               failwith uu____72575)
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
    | FStar_Syntax_Syntax.Tm_refine (bv,uu____72621) ->
        let uu____72626 =
          curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort  in
        (match uu____72626 with
         | (args,res) ->
             (match args with
              | [] ->
                  let uu____72647 = FStar_Syntax_Syntax.mk_Total k1  in
                  ([], uu____72647)
              | uu____72654 -> (args, res)))
    | uu____72655 ->
        let uu____72656 = FStar_Syntax_Syntax.mk_Total k1  in
        ([], uu____72656)
  
let is_arithmetic_primitive :
  'Auu____72670 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____72670 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____72693::uu____72694::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____72698::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____72701 -> false
  
let (isInteger : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____72732 -> false
  
let (getInteger : FStar_Syntax_Syntax.term' -> Prims.int) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____72755 -> failwith "Expected an Integer term"
  
let is_BitVector_primitive :
  'Auu____72765 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____72765)
        Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____72807)::uu____72808::uu____72809::[]) ->
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
         fv,(sz_arg,uu____72860)::uu____72861::[]) ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____72898 -> false
  
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
          let uu____73222 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue  in
          (uu____73222, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____73224 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse  in
          (uu____73224, [])
      | FStar_Const.Const_char c1 ->
          let uu____73227 =
            let uu____73228 =
              let uu____73236 =
                let uu____73239 =
                  let uu____73240 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1)
                     in
                  FStar_SMTEncoding_Term.boxInt uu____73240  in
                [uu____73239]  in
              ("FStar.Char.__char_of_int", uu____73236)  in
            FStar_SMTEncoding_Util.mkApp uu____73228  in
          (uu____73227, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____73258 =
            let uu____73259 = FStar_SMTEncoding_Util.mkInteger i  in
            FStar_SMTEncoding_Term.boxInt uu____73259  in
          (uu____73258, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.FStar_SMTEncoding_Env.tcenv).FStar_TypeChecker_Env.dsenv
              repr sw FStar_Range.dummyRange
             in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____73280) ->
          let uu____73283 =
            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.string_const s
             in
          (uu____73283, [])
      | FStar_Const.Const_range uu____73284 ->
          let uu____73285 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          (uu____73285, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | FStar_Const.Const_real r ->
          let uu____73288 =
            let uu____73289 = FStar_SMTEncoding_Util.mkReal r  in
            FStar_SMTEncoding_Term.boxReal uu____73289  in
          (uu____73288, [])
      | c1 ->
          let uu____73291 =
            let uu____73293 = FStar_Syntax_Print.const_to_string c1  in
            FStar_Util.format1 "Unhandled constant: %s" uu____73293  in
          failwith uu____73291

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
        (let uu____73322 =
           FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
             FStar_Options.Medium
            in
         if uu____73322
         then
           let uu____73325 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____73325
         else ());
        (let uu____73331 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____73413  ->
                   fun b  ->
                     match uu____73413 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____73478 =
                           let x = FStar_Pervasives_Native.fst b  in
                           let uu____73494 =
                             FStar_SMTEncoding_Env.gen_term_var env1 x  in
                           match uu____73494 with
                           | (xxsym,xx,env') ->
                               let uu____73519 =
                                 let uu____73524 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____73524 env1
                                   xx
                                  in
                               (match uu____73519 with
                                | (guard_x_t,decls') ->
                                    let uu____73539 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xxsym,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    (uu____73539, guard_x_t, env', decls', x))
                            in
                         (match uu____73478 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____73331 with
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
          let uu____73639 = encode_term t env  in
          match uu____73639 with
          | (t1,decls) ->
              let uu____73650 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____73650, decls)

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
          let uu____73661 = encode_term t env  in
          match uu____73661 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____73676 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____73676, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____73678 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____73678, decls))

and (encode_arith_term :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____73684 = encode_args args_e env  in
        match uu____73684 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____73703 -> failwith "Impossible"  in
            let unary unbox arg_tms1 =
              let uu____73725 = FStar_List.hd arg_tms1  in unbox uu____73725
               in
            let binary unbox arg_tms1 =
              let uu____73750 =
                let uu____73751 = FStar_List.hd arg_tms1  in
                unbox uu____73751  in
              let uu____73752 =
                let uu____73753 =
                  let uu____73754 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____73754  in
                unbox uu____73753  in
              (uu____73750, uu____73752)  in
            let mk_default uu____73762 =
              let uu____73763 =
                FStar_SMTEncoding_Env.lookup_free_var_sym env
                  head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____73763 with
              | (fname,fuel_args,arity) ->
                  let args = FStar_List.append fuel_args arg_tms  in
                  maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity
                    args
               in
            let mk_l box op mk_args ts =
              let uu____73852 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____73852
              then
                let uu____73855 =
                  let uu____73856 = mk_args ts  in op uu____73856  in
                FStar_All.pipe_right uu____73855 box
              else mk_default ()  in
            let mk_nl box unbox nm op ts =
              let uu____73914 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____73914
              then
                let uu____73917 = binary unbox ts  in
                match uu____73917 with
                | (t1,t2) ->
                    let uu____73924 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____73924 box
              else
                (let uu____73930 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____73930
                 then
                   let uu____73933 =
                     let uu____73934 = binary unbox ts  in op uu____73934  in
                   FStar_All.pipe_right uu____73933 box
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
            let uu____74369 =
              let uu____74379 =
                FStar_List.tryFind
                  (fun uu____74403  ->
                     match uu____74403 with
                     | (l,uu____74414) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____74379 FStar_Util.must  in
            (match uu____74369 with
             | (uu____74458,op) ->
                 let uu____74470 = op arg_tms  in (uu____74470, decls))

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
        let uu____74486 = FStar_List.hd args_e  in
        match uu____74486 with
        | (tm_sz,uu____74502) ->
            let uu____74511 = uu____74486  in
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let t_decls1 = FStar_SMTEncoding_Term.mkBvConstructor sz  in
              FStar_SMTEncoding_Term.mk_decls "" sz_key t_decls1 []  in
            let uu____74522 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____74548::(sz_arg,uu____74550)::uu____74551::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____74618 =
                    let uu____74619 = FStar_List.tail args_e  in
                    FStar_List.tail uu____74619  in
                  let uu____74646 =
                    let uu____74650 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____74650  in
                  (uu____74618, uu____74646)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____74657::(sz_arg,uu____74659)::uu____74660::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____74727 =
                    let uu____74729 =
                      FStar_Syntax_Print.term_to_string sz_arg  in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____74729
                     in
                  failwith uu____74727
              | uu____74739 ->
                  let uu____74754 = FStar_List.tail args_e  in
                  (uu____74754, FStar_Pervasives_Native.None)
               in
            (match uu____74522 with
             | (arg_tms,ext_sz) ->
                 let uu____74781 = encode_args arg_tms env  in
                 (match uu____74781 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____74802 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____74814 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____74814  in
                      let unary_arith arg_tms2 =
                        let uu____74825 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____74825  in
                      let binary arg_tms2 =
                        let uu____74840 =
                          let uu____74841 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____74841
                           in
                        let uu____74842 =
                          let uu____74843 =
                            let uu____74844 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____74844  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____74843
                           in
                        (uu____74840, uu____74842)  in
                      let binary_arith arg_tms2 =
                        let uu____74861 =
                          let uu____74862 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____74862
                           in
                        let uu____74863 =
                          let uu____74864 =
                            let uu____74865 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____74865  in
                          FStar_SMTEncoding_Term.unboxInt uu____74864  in
                        (uu____74861, uu____74863)  in
                      let mk_bv op mk_args resBox ts =
                        let uu____74923 =
                          let uu____74924 = mk_args ts  in op uu____74924  in
                        FStar_All.pipe_right uu____74923 resBox  in
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
                        let uu____75056 =
                          let uu____75061 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____75061  in
                        let uu____75070 =
                          let uu____75075 =
                            let uu____75077 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____75077  in
                          FStar_SMTEncoding_Term.boxBitVec uu____75075  in
                        mk_bv uu____75056 unary uu____75070 arg_tms2  in
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
                      let uu____75317 =
                        let uu____75327 =
                          FStar_List.tryFind
                            (fun uu____75351  ->
                               match uu____75351 with
                               | (l,uu____75362) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____75327 FStar_Util.must  in
                      (match uu____75317 with
                       | (uu____75408,op) ->
                           let uu____75420 = op arg_tms1  in
                           (uu____75420, (FStar_List.append sz_decls decls)))))

and (encode_deeply_embedded_quantifier :
  FStar_Syntax_Syntax.term ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let env1 =
        let uu___1170_75430 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___1170_75430.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___1170_75430.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___1170_75430.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___1170_75430.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___1170_75430.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___1170_75430.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name =
            (uu___1170_75430.FStar_SMTEncoding_Env.use_zfuel_name);
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___1170_75430.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___1170_75430.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier = true;
          FStar_SMTEncoding_Env.global_cache =
            (uu___1170_75430.FStar_SMTEncoding_Env.global_cache)
        }  in
      let uu____75432 = encode_term t env1  in
      match uu____75432 with
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
               (uu____75458,{
                              FStar_SMTEncoding_Term.tm =
                                FStar_SMTEncoding_Term.FreeV uu____75459;
                              FStar_SMTEncoding_Term.freevars = uu____75460;
                              FStar_SMTEncoding_Term.rng = uu____75461;_}::
                {
                  FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV
                    uu____75462;
                  FStar_SMTEncoding_Term.freevars = uu____75463;
                  FStar_SMTEncoding_Term.rng = uu____75464;_}::[])
               ->
               (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                  (FStar_Errors.Warning_QuantifierWithoutPattern,
                    "Not encoding deeply embedded, unguarded quantifier to SMT");
                (tm, decls))
           | uu____75510 ->
               let uu____75511 = encode_formula t env1  in
               (match uu____75511 with
                | (phi,decls') ->
                    let interp =
                      match vars with
                      | [] ->
                          let uu____75531 =
                            let uu____75536 =
                              FStar_SMTEncoding_Term.mk_Valid tm  in
                            (uu____75536, phi)  in
                          FStar_SMTEncoding_Util.mkIff uu____75531
                      | uu____75537 ->
                          let uu____75538 =
                            let uu____75549 =
                              let uu____75550 =
                                let uu____75555 =
                                  FStar_SMTEncoding_Term.mk_Valid tm  in
                                (uu____75555, phi)  in
                              FStar_SMTEncoding_Util.mkIff uu____75550  in
                            ([[valid_tm]], vars, uu____75549)  in
                          FStar_SMTEncoding_Term.mkForall
                            t.FStar_Syntax_Syntax.pos uu____75538
                       in
                    let ax =
                      let uu____75565 =
                        let uu____75573 =
                          let uu____75575 =
                            FStar_Util.digest_of_string tkey_hash  in
                          Prims.op_Hat "l_quant_interp_" uu____75575  in
                        (interp,
                          (FStar_Pervasives_Native.Some
                             "Interpretation of deeply embedded quantifier"),
                          uu____75573)
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____75565  in
                    let uu____75581 =
                      let uu____75582 =
                        let uu____75585 =
                          FStar_SMTEncoding_Term.mk_decls "" tkey_hash 
                            [ax] (FStar_List.append decls decls')
                           in
                        FStar_List.append decls' uu____75585  in
                      FStar_List.append decls uu____75582  in
                    (tm, uu____75581)))

and (encode_term :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____75597 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____75597
       then
         let uu____75602 = FStar_Syntax_Print.tag_of_term t  in
         let uu____75604 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____75606 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____75602 uu____75604
           uu____75606
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____75615 ->
           let uu____75638 =
             let uu____75640 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____75643 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____75645 = FStar_Syntax_Print.term_to_string t0  in
             let uu____75647 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____75640
               uu____75643 uu____75645 uu____75647
              in
           failwith uu____75638
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____75654 =
             let uu____75656 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____75659 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____75661 = FStar_Syntax_Print.term_to_string t0  in
             let uu____75663 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____75656
               uu____75659 uu____75661 uu____75663
              in
           failwith uu____75654
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let e = FStar_Syntax_Util.unfold_lazy i  in
           ((let uu____75673 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____75673
             then
               let uu____75678 = FStar_Syntax_Print.term_to_string t0  in
               let uu____75680 = FStar_Syntax_Print.term_to_string e  in
               FStar_Util.print2 ">> Unfolded (%s) ~> (%s)\n" uu____75678
                 uu____75680
             else ());
            encode_term e env)
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____75686 =
             let uu____75688 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____75688
              in
           failwith uu____75686
       | FStar_Syntax_Syntax.Tm_ascribed (t1,(k,uu____75697),uu____75698) ->
           let uu____75747 =
             match k with
             | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
             | uu____75757 -> false  in
           if uu____75747
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t1 env
       | FStar_Syntax_Syntax.Tm_quoted (qt,uu____75775) ->
           let tv =
             let uu____75781 =
               let uu____75788 = FStar_Reflection_Basic.inspect_ln qt  in
               FStar_Syntax_Embeddings.embed
                 FStar_Reflection_Embeddings.e_term_view uu____75788
                in
             uu____75781 t.FStar_Syntax_Syntax.pos
               FStar_Pervasives_Native.None
               FStar_Syntax_Embeddings.id_norm_cb
              in
           ((let uu____75815 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____75815
             then
               let uu____75820 = FStar_Syntax_Print.term_to_string t0  in
               let uu____75822 = FStar_Syntax_Print.term_to_string tv  in
               FStar_Util.print2 ">> Inspected (%s) ~> (%s)\n" uu____75820
                 uu____75822
             else ());
            (let t1 =
               let uu____75830 =
                 let uu____75841 = FStar_Syntax_Syntax.as_arg tv  in
                 [uu____75841]  in
               FStar_Syntax_Util.mk_app
                 (FStar_Reflection_Data.refl_constant_term
                    FStar_Reflection_Data.fstar_refl_pack_ln) uu____75830
                in
             encode_term t1 env))
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_pattern uu____75867) ->
           encode_term t1
             (let uu___1242_75885 = env  in
              {
                FStar_SMTEncoding_Env.bvar_bindings =
                  (uu___1242_75885.FStar_SMTEncoding_Env.bvar_bindings);
                FStar_SMTEncoding_Env.fvar_bindings =
                  (uu___1242_75885.FStar_SMTEncoding_Env.fvar_bindings);
                FStar_SMTEncoding_Env.depth =
                  (uu___1242_75885.FStar_SMTEncoding_Env.depth);
                FStar_SMTEncoding_Env.tcenv =
                  (uu___1242_75885.FStar_SMTEncoding_Env.tcenv);
                FStar_SMTEncoding_Env.warn =
                  (uu___1242_75885.FStar_SMTEncoding_Env.warn);
                FStar_SMTEncoding_Env.nolabels =
                  (uu___1242_75885.FStar_SMTEncoding_Env.nolabels);
                FStar_SMTEncoding_Env.use_zfuel_name =
                  (uu___1242_75885.FStar_SMTEncoding_Env.use_zfuel_name);
                FStar_SMTEncoding_Env.encode_non_total_function_typ =
                  (uu___1242_75885.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                FStar_SMTEncoding_Env.current_module_name =
                  (uu___1242_75885.FStar_SMTEncoding_Env.current_module_name);
                FStar_SMTEncoding_Env.encoding_quantifier = false;
                FStar_SMTEncoding_Env.global_cache =
                  (uu___1242_75885.FStar_SMTEncoding_Env.global_cache)
              })
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____75888) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = FStar_SMTEncoding_Env.lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____75896 = head_redex env t  in
           if uu____75896
           then let uu____75903 = whnf env t  in encode_term uu____75903 env
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
              let uu____75910 =
                if
                  fvb.FStar_SMTEncoding_Env.smt_arity > (Prims.parse_int "0")
                then
                  match tok.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.FreeV uu____75934 ->
                      let sym_name =
                        let uu____75945 =
                          FStar_Util.digest_of_string tkey_hash  in
                        Prims.op_Hat "@kick_partial_app_" uu____75945  in
                      let uu____75948 =
                        let uu____75951 =
                          let uu____75952 =
                            let uu____75960 =
                              FStar_SMTEncoding_Term.kick_partial_app tok  in
                            (uu____75960,
                              (FStar_Pervasives_Native.Some
                                 "kick_partial_app"), sym_name)
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____75952  in
                        [uu____75951]  in
                      (uu____75948, sym_name)
                  | FStar_SMTEncoding_Term.App (uu____75967,[]) ->
                      let sym_name =
                        let uu____75972 =
                          FStar_Util.digest_of_string tkey_hash  in
                        Prims.op_Hat "@kick_partial_app_" uu____75972  in
                      let uu____75975 =
                        let uu____75978 =
                          let uu____75979 =
                            let uu____75987 =
                              FStar_SMTEncoding_Term.kick_partial_app tok  in
                            (uu____75987,
                              (FStar_Pervasives_Native.Some
                                 "kick_partial_app"), sym_name)
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____75979  in
                        [uu____75978]  in
                      (uu____75975, sym_name)
                  | uu____75994 -> ([], "")
                else ([], "")  in
              match uu____75910 with
              | (aux_decls,sym_name) ->
                  let uu____76017 =
                    if aux_decls = []
                    then
                      FStar_All.pipe_right []
                        FStar_SMTEncoding_Term.mk_decls_trivial
                    else
                      FStar_SMTEncoding_Term.mk_decls sym_name tkey_hash
                        aux_decls []
                     in
                  (tok, uu____76017))
       | FStar_Syntax_Syntax.Tm_type uu____76025 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____76027) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.FStar_SMTEncoding_Env.current_module_name
              in
           let uu____76057 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____76057 with
            | (binders1,res) ->
                let uu____76068 =
                  (env.FStar_SMTEncoding_Env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____76068
                then
                  let uu____76075 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____76075 with
                   | (vars,guards,env',decls,uu____76100) ->
                       let fsym =
                         let uu____76114 =
                           let uu____76120 =
                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                               module_name "f"
                              in
                           (uu____76120, FStar_SMTEncoding_Term.Term_sort)
                            in
                         FStar_SMTEncoding_Term.mk_fv uu____76114  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____76126 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___1296_76135 =
                              env.FStar_SMTEncoding_Env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___1296_76135.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___1296_76135.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___1296_76135.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___1296_76135.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___1296_76135.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___1296_76135.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___1296_76135.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___1296_76135.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___1296_76135.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___1296_76135.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___1296_76135.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___1296_76135.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___1296_76135.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___1296_76135.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___1296_76135.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___1296_76135.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___1296_76135.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___1296_76135.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___1296_76135.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___1296_76135.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___1296_76135.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___1296_76135.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___1296_76135.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___1296_76135.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___1296_76135.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___1296_76135.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___1296_76135.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___1296_76135.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___1296_76135.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___1296_76135.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___1296_76135.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___1296_76135.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___1296_76135.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___1296_76135.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___1296_76135.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___1296_76135.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___1296_76135.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___1296_76135.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___1296_76135.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___1296_76135.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___1296_76135.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___1296_76135.FStar_TypeChecker_Env.nbe)
                            }) res
                          in
                       (match uu____76126 with
                        | (pre_opt,res_t) ->
                            let uu____76147 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____76147 with
                             | (res_pred,decls') ->
                                 let uu____76158 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____76171 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____76171, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____76175 =
                                         encode_formula pre env'  in
                                       (match uu____76175 with
                                        | (guard,decls0) ->
                                            let uu____76188 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____76188, decls0))
                                    in
                                 (match uu____76158 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____76202 =
                                          let uu____76213 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____76213)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t.FStar_Syntax_Syntax.pos
                                          uu____76202
                                         in
                                      let cvars =
                                        let uu____76233 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____76233
                                          (FStar_List.filter
                                             (fun x  ->
                                                let uu____76252 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    x
                                                   in
                                                let uu____76254 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    fsym
                                                   in
                                                uu____76252 <> uu____76254))
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
                                        let uu____76276 =
                                          FStar_Util.digest_of_string
                                            tkey_hash
                                           in
                                        Prims.op_Hat "Tm_arrow_" uu____76276
                                         in
                                      let cvar_sorts =
                                        FStar_List.map
                                          FStar_SMTEncoding_Term.fv_sort
                                          cvars
                                         in
                                      let caption =
                                        let uu____76291 =
                                          FStar_Options.log_queries ()  in
                                        if uu____76291
                                        then
                                          let uu____76294 =
                                            let uu____76296 =
                                              FStar_TypeChecker_Normalize.term_to_string
                                                env.FStar_SMTEncoding_Env.tcenv
                                                t0
                                               in
                                            FStar_Util.replace_char
                                              uu____76296 10 32
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____76294
                                        else FStar_Pervasives_Native.None  in
                                      let tdecl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (tsym, cvar_sorts,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            caption)
                                         in
                                      let t1 =
                                        let uu____76309 =
                                          let uu____76317 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              cvars
                                             in
                                          (tsym, uu____76317)  in
                                        FStar_SMTEncoding_Util.mkApp
                                          uu____76309
                                         in
                                      let t_has_kind =
                                        FStar_SMTEncoding_Term.mk_HasType t1
                                          FStar_SMTEncoding_Term.mk_Term_type
                                         in
                                      let k_assumption =
                                        let a_name =
                                          Prims.op_Hat "kinding_" tsym  in
                                        let uu____76336 =
                                          let uu____76344 =
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              ([[t_has_kind]], cvars,
                                                t_has_kind)
                                             in
                                          (uu____76344,
                                            (FStar_Pervasives_Native.Some
                                               a_name), a_name)
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____76336
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
                                        let uu____76361 =
                                          let uu____76369 =
                                            let uu____76370 =
                                              let uu____76381 =
                                                let uu____76382 =
                                                  let uu____76387 =
                                                    let uu____76388 =
                                                      FStar_SMTEncoding_Term.mk_PreType
                                                        f
                                                       in
                                                    FStar_SMTEncoding_Term.mk_tester
                                                      "Tm_arrow" uu____76388
                                                     in
                                                  (f_has_t, uu____76387)  in
                                                FStar_SMTEncoding_Util.mkImp
                                                  uu____76382
                                                 in
                                              ([[f_has_t]], (fsym :: cvars),
                                                uu____76381)
                                               in
                                            let uu____76406 =
                                              mkForall_fuel module_name
                                                t0.FStar_Syntax_Syntax.pos
                                               in
                                            uu____76406 uu____76370  in
                                          (uu____76369,
                                            (FStar_Pervasives_Native.Some
                                               "pre-typing for functions"),
                                            (Prims.op_Hat module_name
                                               (Prims.op_Hat "_" a_name)))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____76361
                                         in
                                      let t_interp1 =
                                        let a_name =
                                          Prims.op_Hat "interpretation_" tsym
                                           in
                                        let uu____76429 =
                                          let uu____76437 =
                                            let uu____76438 =
                                              let uu____76449 =
                                                FStar_SMTEncoding_Util.mkIff
                                                  (f_has_t_z, t_interp)
                                                 in
                                              ([[f_has_t_z]], (fsym ::
                                                cvars), uu____76449)
                                               in
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              uu____76438
                                             in
                                          (uu____76437,
                                            (FStar_Pervasives_Native.Some
                                               a_name),
                                            (Prims.op_Hat module_name
                                               (Prims.op_Hat "_" a_name)))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____76429
                                         in
                                      let t_decls1 =
                                        [tdecl;
                                        k_assumption;
                                        pre_typing;
                                        t_interp1]  in
                                      let uu____76472 =
                                        let uu____76473 =
                                          let uu____76476 =
                                            let uu____76479 =
                                              FStar_SMTEncoding_Term.mk_decls
                                                tsym tkey_hash t_decls1
                                                (FStar_List.append decls
                                                   (FStar_List.append decls'
                                                      guard_decls))
                                               in
                                            FStar_List.append guard_decls
                                              uu____76479
                                             in
                                          FStar_List.append decls'
                                            uu____76476
                                           in
                                        FStar_List.append decls uu____76473
                                         in
                                      (t1, uu____76472)))))
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
                     let uu____76500 =
                       let uu____76508 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____76508,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"), a_name)
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____76500  in
                   let fsym =
                     FStar_SMTEncoding_Term.mk_fv
                       ("f", FStar_SMTEncoding_Term.Term_sort)
                      in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.op_Hat "pre_typing_" tsym  in
                     let uu____76521 =
                       let uu____76529 =
                         let uu____76530 =
                           let uu____76541 =
                             let uu____76542 =
                               let uu____76547 =
                                 let uu____76548 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____76548
                                  in
                               (f_has_t, uu____76547)  in
                             FStar_SMTEncoding_Util.mkImp uu____76542  in
                           ([[f_has_t]], [fsym], uu____76541)  in
                         let uu____76574 =
                           mkForall_fuel module_name
                             t0.FStar_Syntax_Syntax.pos
                            in
                         uu____76574 uu____76530  in
                       (uu____76529, (FStar_Pervasives_Native.Some a_name),
                         a_name)
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____76521  in
                   let uu____76591 =
                     FStar_All.pipe_right [tdecl; t_kinding; t_interp]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                      in
                   (t1, uu____76591)))
       | FStar_Syntax_Syntax.Tm_refine uu____76594 ->
           let uu____76601 =
             let uu____76606 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Env.Weak;
                 FStar_TypeChecker_Env.HNF;
                 FStar_TypeChecker_Env.EraseUniverses]
                 env.FStar_SMTEncoding_Env.tcenv t0
                in
             match uu____76606 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____76613;
                 FStar_Syntax_Syntax.vars = uu____76614;_} ->
                 let uu____76621 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____76621 with
                  | (b,f1) ->
                      let uu____76646 =
                        let uu____76647 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____76647  in
                      (uu____76646, f1))
             | uu____76662 -> failwith "impossible"  in
           (match uu____76601 with
            | (x,f) ->
                let uu____76674 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____76674 with
                 | (base_t,decls) ->
                     let uu____76685 =
                       FStar_SMTEncoding_Env.gen_term_var env x  in
                     (match uu____76685 with
                      | (x1,xtm,env') ->
                          let uu____76702 = encode_formula f env'  in
                          (match uu____76702 with
                           | (refinement,decls') ->
                               let uu____76713 =
                                 FStar_SMTEncoding_Env.fresh_fvar
                                   env.FStar_SMTEncoding_Env.current_module_name
                                   "f" FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____76713 with
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
                                      let uu____76741 =
                                        let uu____76752 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____76763 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____76752
                                          uu____76763
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____76741
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun y  ->
                                              (let uu____76817 =
                                                 FStar_SMTEncoding_Term.fv_name
                                                   y
                                                  in
                                               uu____76817 <> x1) &&
                                                (let uu____76821 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     y
                                                    in
                                                 uu____76821 <> fsym)))
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
                                      let uu____76857 =
                                        FStar_Util.digest_of_string tkey_hash
                                         in
                                      Prims.op_Hat "Tm_refine_" uu____76857
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
                                      let uu____76877 =
                                        let uu____76885 =
                                          FStar_List.map
                                            FStar_SMTEncoding_Util.mkFreeV
                                            cvars1
                                           in
                                        (tsym, uu____76885)  in
                                      FStar_SMTEncoding_Util.mkApp
                                        uu____76877
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
                                      let uu____76905 =
                                        let uu____76913 =
                                          let uu____76914 =
                                            let uu____76925 =
                                              FStar_SMTEncoding_Util.mkIff
                                                (t_haseq_ref, t_haseq_base)
                                               in
                                            ([[t_haseq_ref]], cvars1,
                                              uu____76925)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            t0.FStar_Syntax_Syntax.pos
                                            uu____76914
                                           in
                                        (uu____76913,
                                          (FStar_Pervasives_Native.Some
                                             (Prims.op_Hat "haseq for " tsym)),
                                          (Prims.op_Hat "haseq" tsym))
                                         in
                                      FStar_SMTEncoding_Util.mkAssume
                                        uu____76905
                                       in
                                    let t_kinding =
                                      let uu____76939 =
                                        let uu____76947 =
                                          FStar_SMTEncoding_Term.mkForall
                                            t0.FStar_Syntax_Syntax.pos
                                            ([[t_has_kind]], cvars1,
                                              t_has_kind)
                                           in
                                        (uu____76947,
                                          (FStar_Pervasives_Native.Some
                                             "refinement kinding"),
                                          (Prims.op_Hat "refinement_kinding_"
                                             tsym))
                                         in
                                      FStar_SMTEncoding_Util.mkAssume
                                        uu____76939
                                       in
                                    let t_interp =
                                      let uu____76961 =
                                        let uu____76969 =
                                          let uu____76970 =
                                            let uu____76981 =
                                              FStar_SMTEncoding_Util.mkIff
                                                (x_has_t, encoding)
                                               in
                                            ([[x_has_t]], (ffv :: xfv ::
                                              cvars1), uu____76981)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            t0.FStar_Syntax_Syntax.pos
                                            uu____76970
                                           in
                                        (uu____76969,
                                          (FStar_Pervasives_Native.Some
                                             "refinement_interpretation"),
                                          (Prims.op_Hat
                                             "refinement_interpretation_"
                                             tsym))
                                         in
                                      FStar_SMTEncoding_Util.mkAssume
                                        uu____76961
                                       in
                                    let t_decls1 =
                                      [tdecl; t_kinding; t_interp; t_haseq1]
                                       in
                                    let uu____77013 =
                                      let uu____77014 =
                                        let uu____77017 =
                                          FStar_SMTEncoding_Term.mk_decls
                                            tsym tkey_hash t_decls1
                                            (FStar_List.append decls decls')
                                           in
                                        FStar_List.append decls' uu____77017
                                         in
                                      FStar_List.append decls uu____77014  in
                                    (t1, uu____77013))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,uu____77021) ->
           let ttm =
             let uu____77039 =
               FStar_Syntax_Unionfind.uvar_id
                 uv.FStar_Syntax_Syntax.ctx_uvar_head
                in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____77039  in
           let uu____77041 =
             encode_term_pred FStar_Pervasives_Native.None
               uv.FStar_Syntax_Syntax.ctx_uvar_typ env ttm
              in
           (match uu____77041 with
            | (t_has_k,decls) ->
                let d =
                  let uu____77053 =
                    let uu____77061 =
                      let uu____77063 =
                        let uu____77065 =
                          let uu____77067 =
                            FStar_Syntax_Unionfind.uvar_id
                              uv.FStar_Syntax_Syntax.ctx_uvar_head
                             in
                          FStar_Util.string_of_int uu____77067  in
                        FStar_Util.format1 "uvar_typing_%s" uu____77065  in
                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                        uu____77063
                       in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____77061)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____77053  in
                let uu____77073 =
                  let uu____77074 =
                    FStar_All.pipe_right [d]
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append decls uu____77074  in
                (ttm, uu____77073))
       | FStar_Syntax_Syntax.Tm_app uu____77081 ->
           let uu____77098 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____77098 with
            | (head1,args_e) ->
                let uu____77145 =
                  let uu____77160 =
                    let uu____77161 = FStar_Syntax_Subst.compress head1  in
                    uu____77161.FStar_Syntax_Syntax.n  in
                  (uu____77160, args_e)  in
                (match uu____77145 with
                 | uu____77178 when head_redex env head1 ->
                     let uu____77193 = whnf env t  in
                     encode_term uu____77193 env
                 | uu____77194 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____77217 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_fvar fv,uu____77235) when
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
                       FStar_Syntax_Syntax.pos = uu____77257;
                       FStar_Syntax_Syntax.vars = uu____77258;_},uu____77259),uu____77260)
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
                       FStar_Syntax_Syntax.pos = uu____77286;
                       FStar_Syntax_Syntax.vars = uu____77287;_},uu____77288),
                    (v0,uu____77290)::(v1,uu____77292)::(v2,uu____77294)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____77365 = encode_term v0 env  in
                     (match uu____77365 with
                      | (v01,decls0) ->
                          let uu____77376 = encode_term v1 env  in
                          (match uu____77376 with
                           | (v11,decls1) ->
                               let uu____77387 = encode_term v2 env  in
                               (match uu____77387 with
                                | (v21,decls2) ->
                                    let uu____77398 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____77398,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(v0,uu____77401)::(v1,uu____77403)::(v2,uu____77405)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____77472 = encode_term v0 env  in
                     (match uu____77472 with
                      | (v01,decls0) ->
                          let uu____77483 = encode_term v1 env  in
                          (match uu____77483 with
                           | (v11,decls1) ->
                               let uu____77494 = encode_term v2 env  in
                               (match uu____77494 with
                                | (v21,decls2) ->
                                    let uu____77505 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____77505,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____77507)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____77543)::(rng,uu____77545)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____77596) ->
                     let e0 =
                       let uu____77618 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg
                         env.FStar_SMTEncoding_Env.tcenv head1 uu____77618
                        in
                     ((let uu____77628 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug
                              env.FStar_SMTEncoding_Env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____77628
                       then
                         let uu____77633 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____77633
                       else ());
                      (let e =
                         let uu____77641 =
                           let uu____77646 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____77647 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____77646
                             uu____77647
                            in
                         uu____77641 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____77658),(arg,uu____77660)::[]) ->
                     encode_term arg env
                 | uu____77695 ->
                     let uu____77710 = encode_args args_e env  in
                     (match uu____77710 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____77771 = encode_term head1 env  in
                            match uu____77771 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____77843 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____77843 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____77941  ->
                                                 fun uu____77942  ->
                                                   match (uu____77941,
                                                           uu____77942)
                                                   with
                                                   | ((bv,uu____77972),
                                                      (a,uu____77974)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____78004 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____78004
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____78005 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm
                                             in
                                          (match uu____78005 with
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
                                                 let uu____78022 =
                                                   let uu____78030 =
                                                     FStar_SMTEncoding_Term.mkForall
                                                       t0.FStar_Syntax_Syntax.pos
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____78039 =
                                                     let uu____78041 =
                                                       let uu____78043 =
                                                         FStar_SMTEncoding_Term.hash_of_term
                                                           app_tm
                                                          in
                                                       FStar_Util.digest_of_string
                                                         uu____78043
                                                        in
                                                     Prims.op_Hat
                                                       "partial_app_typing_"
                                                       uu____78041
                                                      in
                                                   (uu____78030,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____78039)
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____78022
                                                  in
                                               let uu____78049 =
                                                 let uu____78052 =
                                                   let uu____78055 =
                                                     let uu____78058 =
                                                       FStar_SMTEncoding_Term.mk_decls
                                                         "" tkey_hash
                                                         [e_typing]
                                                         (FStar_List.append
                                                            decls
                                                            (FStar_List.append
                                                               decls' decls''))
                                                        in
                                                     FStar_List.append
                                                       decls'' uu____78058
                                                      in
                                                   FStar_List.append decls'
                                                     uu____78055
                                                    in
                                                 FStar_List.append decls
                                                   uu____78052
                                                  in
                                               (app_tm, uu____78049))))
                             in
                          let encode_full_app fv =
                            let uu____78078 =
                              FStar_SMTEncoding_Env.lookup_free_var_sym env
                                fv
                               in
                            match uu____78078 with
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
                                   FStar_Syntax_Syntax.pos = uu____78121;
                                   FStar_Syntax_Syntax.vars = uu____78122;_},uu____78123)
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
                                   FStar_Syntax_Syntax.pos = uu____78130;
                                   FStar_Syntax_Syntax.vars = uu____78131;_},uu____78132)
                                ->
                                let uu____78137 =
                                  let uu____78138 =
                                    let uu____78143 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____78143
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____78138
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____78137
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____78173 =
                                  let uu____78174 =
                                    let uu____78179 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____78179
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____78174
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____78173
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____78208,(FStar_Util.Inl t1,uu____78210),uu____78211)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____78258,(FStar_Util.Inr c,uu____78260),uu____78261)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____78308 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____78329 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Env.Weak;
                                     FStar_TypeChecker_Env.HNF;
                                     FStar_TypeChecker_Env.EraseUniverses]
                                     env.FStar_SMTEncoding_Env.tcenv
                                     head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____78329
                                  in
                               let uu____78330 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____78330 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____78346;
                                            FStar_Syntax_Syntax.vars =
                                              uu____78347;_},uu____78348)
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
                                     | uu____78366 ->
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
           let uu____78445 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____78445 with
            | (bs1,body1,opening) ->
                let fallback uu____78468 =
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
                  let uu____78478 =
                    let uu____78479 =
                      FStar_SMTEncoding_Term.mk_fv
                        (f, FStar_SMTEncoding_Term.Term_sort)
                       in
                    FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV
                      uu____78479
                     in
                  let uu____78481 =
                    FStar_All.pipe_right [decl]
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  (uu____78478, uu____78481)  in
                let is_impure rc =
                  let uu____78491 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                      env.FStar_SMTEncoding_Env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____78491 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____78506 =
                          let uu____78519 =
                            FStar_TypeChecker_Env.get_range
                              env.FStar_SMTEncoding_Env.tcenv
                             in
                          FStar_TypeChecker_Util.new_implicit_var
                            "SMTEncoding codomain" uu____78519
                            env.FStar_SMTEncoding_Env.tcenv
                            FStar_Syntax_Util.ktype0
                           in
                        (match uu____78506 with
                         | (t1,uu____78522,uu____78523) -> t1)
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  let uu____78541 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                     in
                  if uu____78541
                  then
                    let uu____78546 = FStar_Syntax_Syntax.mk_Total res_typ
                       in
                    FStar_Pervasives_Native.Some uu____78546
                  else
                    (let uu____78549 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid
                        in
                     if uu____78549
                     then
                       let uu____78554 =
                         FStar_Syntax_Syntax.mk_GTotal res_typ  in
                       FStar_Pervasives_Native.Some uu____78554
                     else FStar_Pervasives_Native.None)
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____78562 =
                         let uu____78568 =
                           let uu____78570 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____78570
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____78568)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____78562);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____78575 =
                       (is_impure rc) &&
                         (let uu____78578 =
                            FStar_TypeChecker_Env.is_reifiable_rc
                              env.FStar_SMTEncoding_Env.tcenv rc
                             in
                          Prims.op_Negation uu____78578)
                        in
                     if uu____78575
                     then fallback ()
                     else
                       (let uu____78587 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____78587 with
                        | (vars,guards,envbody,decls,uu____78612) ->
                            let body2 =
                              let uu____78626 =
                                FStar_TypeChecker_Env.is_reifiable_rc
                                  env.FStar_SMTEncoding_Env.tcenv rc
                                 in
                              if uu____78626
                              then
                                FStar_TypeChecker_Util.reify_body
                                  env.FStar_SMTEncoding_Env.tcenv body1
                              else body1  in
                            let uu____78631 = encode_term body2 envbody  in
                            (match uu____78631 with
                             | (body3,decls') ->
                                 let uu____78642 =
                                   let uu____78651 = codomain_eff rc  in
                                   match uu____78651 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____78670 = encode_term tfun env
                                          in
                                       (match uu____78670 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____78642 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____78704 =
                                          let uu____78715 =
                                            let uu____78716 =
                                              let uu____78721 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____78721, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____78716
                                             in
                                          ([], vars, uu____78715)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t0.FStar_Syntax_Syntax.pos
                                          uu____78704
                                         in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body
                                         in
                                      let uu____78729 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            (cvars, key_body)
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____78745 =
                                              let uu____78748 =
                                                let uu____78759 =
                                                  FStar_SMTEncoding_Term.free_variables
                                                    t1
                                                   in
                                                FStar_List.append uu____78759
                                                  cvars
                                                 in
                                              FStar_Util.remove_dups
                                                FStar_SMTEncoding_Term.fv_eq
                                                uu____78748
                                               in
                                            let uu____78786 =
                                              FStar_SMTEncoding_Util.mkAnd
                                                (key_body, t1)
                                               in
                                            (uu____78745, uu____78786)
                                         in
                                      (match uu____78729 with
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
                                           let uu____78808 =
                                             is_an_eta_expansion env vars
                                               body3
                                              in
                                           (match uu____78808 with
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
                                                  let uu____78824 =
                                                    FStar_Util.digest_of_string
                                                      tkey_hash
                                                     in
                                                  Prims.op_Hat "Tm_abs_"
                                                    uu____78824
                                                   in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None)
                                                   in
                                                let f =
                                                  let uu____78833 =
                                                    let uu____78841 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    (fsym, uu____78841)  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____78833
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
                                                      let uu____78858 =
                                                        let uu____78859 =
                                                          let uu____78867 =
                                                            FStar_SMTEncoding_Term.mkForall
                                                              t0.FStar_Syntax_Syntax.pos
                                                              ([[f]], cvars1,
                                                                f_has_t)
                                                             in
                                                          (uu____78867,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name)
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____78859
                                                         in
                                                      [uu____78858]
                                                   in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.op_Hat
                                                      "interpretation_" fsym
                                                     in
                                                  let uu____78882 =
                                                    let uu____78890 =
                                                      let uu____78891 =
                                                        let uu____78902 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3)
                                                           in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____78902)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        t0.FStar_Syntax_Syntax.pos
                                                        uu____78891
                                                       in
                                                    (uu____78890,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____78882
                                                   in
                                                let f_decls =
                                                  FStar_List.append (fdecl ::
                                                    typing_f) [interp_f]
                                                   in
                                                let uu____78916 =
                                                  let uu____78917 =
                                                    let uu____78920 =
                                                      let uu____78923 =
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
                                                        decls'' uu____78923
                                                       in
                                                    FStar_List.append decls'
                                                      uu____78920
                                                     in
                                                  FStar_List.append decls
                                                    uu____78917
                                                   in
                                                (f, uu____78916))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____78926,{
                           FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                             uu____78927;
                           FStar_Syntax_Syntax.lbunivs = uu____78928;
                           FStar_Syntax_Syntax.lbtyp = uu____78929;
                           FStar_Syntax_Syntax.lbeff = uu____78930;
                           FStar_Syntax_Syntax.lbdef = uu____78931;
                           FStar_Syntax_Syntax.lbattrs = uu____78932;
                           FStar_Syntax_Syntax.lbpos = uu____78933;_}::uu____78934),uu____78935)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____78969;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____78971;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____78973;
                FStar_Syntax_Syntax.lbpos = uu____78974;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____79001 ->
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
              let uu____79073 =
                let uu____79078 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____79078 env  in
              match uu____79073 with
              | (ee1,decls1) ->
                  let uu____79103 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____79103 with
                   | (xs,e21) ->
                       let uu____79128 = FStar_List.hd xs  in
                       (match uu____79128 with
                        | (x1,uu____79146) ->
                            let env' =
                              FStar_SMTEncoding_Env.push_term_var env x1 ee1
                               in
                            let uu____79152 = encode_body e21 env'  in
                            (match uu____79152 with
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
            let uu____79182 =
              let uu____79190 =
                let uu____79191 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____79191  in
              FStar_SMTEncoding_Env.gen_term_var env uu____79190  in
            match uu____79182 with
            | (scrsym,scr',env1) ->
                let uu____79201 = encode_term e env1  in
                (match uu____79201 with
                 | (scr,decls) ->
                     let uu____79212 =
                       let encode_branch b uu____79241 =
                         match uu____79241 with
                         | (else_case,decls1) ->
                             let uu____79260 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____79260 with
                              | (p,w,br) ->
                                  let uu____79286 = encode_pat env1 p  in
                                  (match uu____79286 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____79323  ->
                                                   match uu____79323 with
                                                   | (x,t) ->
                                                       FStar_SMTEncoding_Env.push_term_var
                                                         env2 x t) env1)
                                          in
                                       let uu____79330 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____79352 =
                                               encode_term w1 env2  in
                                             (match uu____79352 with
                                              | (w2,decls2) ->
                                                  let uu____79365 =
                                                    let uu____79366 =
                                                      let uu____79371 =
                                                        let uu____79372 =
                                                          let uu____79377 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____79377)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____79372
                                                         in
                                                      (guard, uu____79371)
                                                       in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____79366
                                                     in
                                                  (uu____79365, decls2))
                                          in
                                       (match uu____79330 with
                                        | (guard1,decls2) ->
                                            let uu____79392 =
                                              encode_br br env2  in
                                            (match uu____79392 with
                                             | (br1,decls3) ->
                                                 let uu____79405 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____79405,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____79212 with
                      | (match_tm,decls1) ->
                          let uu____79426 =
                            let uu____79427 =
                              let uu____79438 =
                                let uu____79445 =
                                  let uu____79450 =
                                    FStar_SMTEncoding_Term.mk_fv
                                      (scrsym,
                                        FStar_SMTEncoding_Term.Term_sort)
                                     in
                                  (uu____79450, scr)  in
                                [uu____79445]  in
                              (uu____79438, match_tm)  in
                            FStar_SMTEncoding_Term.mkLet' uu____79427
                              FStar_Range.dummyRange
                             in
                          (uu____79426, decls1)))

and (encode_pat :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.pat -> (FStar_SMTEncoding_Env.env_t * pattern))
  =
  fun env  ->
    fun pat  ->
      (let uu____79473 =
         FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
           FStar_Options.Medium
          in
       if uu____79473
       then
         let uu____79476 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____79476
       else ());
      (let uu____79481 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____79481 with
       | (vars,pat_term) ->
           let uu____79498 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____79540  ->
                     fun v1  ->
                       match uu____79540 with
                       | (env1,vars1) ->
                           let uu____79576 =
                             FStar_SMTEncoding_Env.gen_term_var env1 v1  in
                           (match uu____79576 with
                            | (xx,uu____79595,env2) ->
                                let uu____79599 =
                                  let uu____79606 =
                                    let uu____79611 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xx,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    (v1, uu____79611)  in
                                  uu____79606 :: vars1  in
                                (env2, uu____79599))) (env, []))
              in
           (match uu____79498 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____79666 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____79667 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____79668 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____79676 = encode_const c env1  in
                      (match uu____79676 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____79684::uu____79685 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____79689 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon
                            env1.FStar_SMTEncoding_Env.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____79712 =
                          FStar_TypeChecker_Env.datacons_of_typ
                            env1.FStar_SMTEncoding_Env.tcenv tc_name
                           in
                        match uu____79712 with
                        | (uu____79720,uu____79721::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____79726 ->
                            FStar_SMTEncoding_Env.mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____79762  ->
                                  match uu____79762 with
                                  | (arg,uu____79772) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____79781 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____79781))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____79813) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____79844 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____79869 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____79915  ->
                                  match uu____79915 with
                                  | (arg,uu____79931) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____79940 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____79940))
                         in
                      FStar_All.pipe_right uu____79869 FStar_List.flatten
                   in
                let pat_term1 uu____79971 = encode_term pat_term env1  in
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
      let uu____79981 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____80029  ->
                fun uu____80030  ->
                  match (uu____80029, uu____80030) with
                  | ((tms,decls),(t,uu____80070)) ->
                      let uu____80097 = encode_term t env  in
                      (match uu____80097 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____79981 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____80154 = FStar_Syntax_Util.list_elements e  in
        match uu____80154 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____80185 =
          let uu____80202 = FStar_Syntax_Util.unmeta p  in
          FStar_All.pipe_right uu____80202 FStar_Syntax_Util.head_and_args
           in
        match uu____80185 with
        | (head1,args) ->
            let uu____80253 =
              let uu____80268 =
                let uu____80269 = FStar_Syntax_Util.un_uinst head1  in
                uu____80269.FStar_Syntax_Syntax.n  in
              (uu____80268, args)  in
            (match uu____80253 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____80291,uu____80292)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____80344 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or1 t1 =
          let uu____80399 =
            let uu____80416 = FStar_Syntax_Util.unmeta t1  in
            FStar_All.pipe_right uu____80416 FStar_Syntax_Util.head_and_args
             in
          match uu____80399 with
          | (head1,args) ->
              let uu____80463 =
                let uu____80478 =
                  let uu____80479 = FStar_Syntax_Util.un_uinst head1  in
                  uu____80479.FStar_Syntax_Syntax.n  in
                (uu____80478, args)  in
              (match uu____80463 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____80498)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____80535 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____80565 = smt_pat_or1 t1  in
            (match uu____80565 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____80587 = list_elements1 e  in
                 FStar_All.pipe_right uu____80587
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____80617 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____80617
                           (FStar_List.map one_pat)))
             | uu____80640 ->
                 let uu____80645 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____80645])
        | uu____80696 ->
            let uu____80699 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____80699]
         in
      let uu____80750 =
        let uu____80765 =
          let uu____80766 = FStar_Syntax_Subst.compress t  in
          uu____80766.FStar_Syntax_Syntax.n  in
        match uu____80765 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____80805 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____80805 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____80840;
                        FStar_Syntax_Syntax.effect_name = uu____80841;
                        FStar_Syntax_Syntax.result_typ = uu____80842;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____80844)::(post,uu____80846)::(pats,uu____80848)::[];
                        FStar_Syntax_Syntax.flags = uu____80849;_}
                      ->
                      let uu____80910 = lemma_pats pats  in
                      (binders1, pre, post, uu____80910)
                  | uu____80921 -> failwith "impos"))
        | uu____80937 -> failwith "Impos"  in
      match uu____80750 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___1940_80974 = env  in
            {
              FStar_SMTEncoding_Env.bvar_bindings =
                (uu___1940_80974.FStar_SMTEncoding_Env.bvar_bindings);
              FStar_SMTEncoding_Env.fvar_bindings =
                (uu___1940_80974.FStar_SMTEncoding_Env.fvar_bindings);
              FStar_SMTEncoding_Env.depth =
                (uu___1940_80974.FStar_SMTEncoding_Env.depth);
              FStar_SMTEncoding_Env.tcenv =
                (uu___1940_80974.FStar_SMTEncoding_Env.tcenv);
              FStar_SMTEncoding_Env.warn =
                (uu___1940_80974.FStar_SMTEncoding_Env.warn);
              FStar_SMTEncoding_Env.nolabels =
                (uu___1940_80974.FStar_SMTEncoding_Env.nolabels);
              FStar_SMTEncoding_Env.use_zfuel_name = true;
              FStar_SMTEncoding_Env.encode_non_total_function_typ =
                (uu___1940_80974.FStar_SMTEncoding_Env.encode_non_total_function_typ);
              FStar_SMTEncoding_Env.current_module_name =
                (uu___1940_80974.FStar_SMTEncoding_Env.current_module_name);
              FStar_SMTEncoding_Env.encoding_quantifier =
                (uu___1940_80974.FStar_SMTEncoding_Env.encoding_quantifier);
              FStar_SMTEncoding_Env.global_cache =
                (uu___1940_80974.FStar_SMTEncoding_Env.global_cache)
            }  in
          let uu____80976 =
            encode_binders FStar_Pervasives_Native.None binders env1  in
          (match uu____80976 with
           | (vars,guards,env2,decls,uu____81001) ->
               let uu____81014 = encode_smt_patterns patterns env2  in
               (match uu____81014 with
                | (pats,decls') ->
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
                    let env3 =
                      let uu___1953_81041 = env2  in
                      {
                        FStar_SMTEncoding_Env.bvar_bindings =
                          (uu___1953_81041.FStar_SMTEncoding_Env.bvar_bindings);
                        FStar_SMTEncoding_Env.fvar_bindings =
                          (uu___1953_81041.FStar_SMTEncoding_Env.fvar_bindings);
                        FStar_SMTEncoding_Env.depth =
                          (uu___1953_81041.FStar_SMTEncoding_Env.depth);
                        FStar_SMTEncoding_Env.tcenv =
                          (uu___1953_81041.FStar_SMTEncoding_Env.tcenv);
                        FStar_SMTEncoding_Env.warn =
                          (uu___1953_81041.FStar_SMTEncoding_Env.warn);
                        FStar_SMTEncoding_Env.nolabels = true;
                        FStar_SMTEncoding_Env.use_zfuel_name =
                          (uu___1953_81041.FStar_SMTEncoding_Env.use_zfuel_name);
                        FStar_SMTEncoding_Env.encode_non_total_function_typ =
                          (uu___1953_81041.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                        FStar_SMTEncoding_Env.current_module_name =
                          (uu___1953_81041.FStar_SMTEncoding_Env.current_module_name);
                        FStar_SMTEncoding_Env.encoding_quantifier =
                          (uu___1953_81041.FStar_SMTEncoding_Env.encoding_quantifier);
                        FStar_SMTEncoding_Env.global_cache =
                          (uu___1953_81041.FStar_SMTEncoding_Env.global_cache)
                      }  in
                    let uu____81043 =
                      let uu____81048 = FStar_Syntax_Util.unmeta pre  in
                      encode_formula uu____81048 env3  in
                    (match uu____81043 with
                     | (pre1,decls'') ->
                         let uu____81055 =
                           let uu____81060 = FStar_Syntax_Util.unmeta post1
                              in
                           encode_formula uu____81060 env3  in
                         (match uu____81055 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append decls'
                                     (FStar_List.append decls'' decls'''))
                                 in
                              let uu____81070 =
                                let uu____81071 =
                                  let uu____81082 =
                                    let uu____81083 =
                                      let uu____81088 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards)
                                         in
                                      (uu____81088, post2)  in
                                    FStar_SMTEncoding_Util.mkImp uu____81083
                                     in
                                  (pats, vars, uu____81082)  in
                                FStar_SMTEncoding_Term.mkForall
                                  t.FStar_Syntax_Syntax.pos uu____81071
                                 in
                              (uu____81070, decls1)))))

and (encode_smt_patterns :
  FStar_Syntax_Syntax.arg Prims.list Prims.list ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term Prims.list Prims.list *
        FStar_SMTEncoding_Term.decls_t))
  =
  fun pats_l  ->
    fun env  ->
      let env1 =
        let uu___1965_81108 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___1965_81108.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___1965_81108.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___1965_81108.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___1965_81108.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___1965_81108.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___1965_81108.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___1965_81108.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___1965_81108.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___1965_81108.FStar_SMTEncoding_Env.encoding_quantifier);
          FStar_SMTEncoding_Env.global_cache =
            (uu___1965_81108.FStar_SMTEncoding_Env.global_cache)
        }  in
      let encode_smt_pattern t =
        let uu____81124 = FStar_Syntax_Util.head_and_args t  in
        match uu____81124 with
        | (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____81187::(x,uu____81189)::(t1,uu____81191)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____81258 = encode_term x env1  in
                 (match uu____81258 with
                  | (x1,decls) ->
                      let uu____81269 = encode_term t1 env1  in
                      (match uu____81269 with
                       | (t2,decls') ->
                           let uu____81280 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                           (uu____81280, (FStar_List.append decls decls'))))
             | uu____81281 -> encode_term t env1)
         in
      FStar_List.fold_right
        (fun pats  ->
           fun uu____81324  ->
             match uu____81324 with
             | (pats_l1,decls) ->
                 let uu____81369 =
                   FStar_List.fold_right
                     (fun uu____81404  ->
                        fun uu____81405  ->
                          match (uu____81404, uu____81405) with
                          | ((p,uu____81447),(pats1,decls1)) ->
                              let uu____81482 = encode_smt_pattern p  in
                              (match uu____81482 with
                               | (t,d) ->
                                   let uu____81497 =
                                     FStar_SMTEncoding_Term.check_pattern_ok
                                       t
                                      in
                                   (match uu____81497 with
                                    | FStar_Pervasives_Native.None  ->
                                        ((t :: pats1),
                                          (FStar_List.append d decls1))
                                    | FStar_Pervasives_Native.Some
                                        illegal_subterm ->
                                        ((let uu____81514 =
                                            let uu____81520 =
                                              let uu____81522 =
                                                FStar_Syntax_Print.term_to_string
                                                  p
                                                 in
                                              let uu____81524 =
                                                FStar_SMTEncoding_Term.print_smt_term
                                                  illegal_subterm
                                                 in
                                              FStar_Util.format2
                                                "Pattern %s contains illegal sub-term (%s); dropping it"
                                                uu____81522 uu____81524
                                               in
                                            (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                                              uu____81520)
                                             in
                                          FStar_Errors.log_issue
                                            p.FStar_Syntax_Syntax.pos
                                            uu____81514);
                                         (pats1,
                                           (FStar_List.append d decls1))))))
                     pats ([], decls)
                    in
                 (match uu____81369 with
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
        let uu____81584 =
          FStar_All.pipe_left
            (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____81584
        then
          let uu____81589 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____81591 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____81589 uu____81591
        else ()  in
      let enc f r l =
        let uu____81633 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____81665 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____81665 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____81633 with
        | (decls,args) ->
            let uu____81696 =
              let uu___2029_81697 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___2029_81697.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___2029_81697.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____81696, decls)
         in
      let const_op f r uu____81732 =
        let uu____81745 = f r  in (uu____81745, [])  in
      let un_op f l =
        let uu____81768 = FStar_List.hd l  in
        FStar_All.pipe_left f uu____81768  in
      let bin_op f uu___632_81788 =
        match uu___632_81788 with
        | t1::t2::[] -> f (t1, t2)
        | uu____81799 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____81840 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____81865  ->
                 match uu____81865 with
                 | (t,uu____81881) ->
                     let uu____81886 = encode_formula t env  in
                     (match uu____81886 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____81840 with
        | (decls,phis) ->
            let uu____81915 =
              let uu___2059_81916 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___2059_81916.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___2059_81916.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____81915, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____81979  ->
               match uu____81979 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____82000) -> false
                    | uu____82003 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____82022 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____82022
        else
          (let uu____82039 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____82039 r rf)
         in
      let eq3_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____82111 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::t1::v0::v1::[] ->
                     let uu____82143 =
                       let uu____82148 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____82149 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____82148, uu____82149)  in
                     FStar_SMTEncoding_Util.mkAnd uu____82143
                 | uu____82150 -> failwith "Impossible")
             in
          uu____82111 r args
        else
          (let uu____82156 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____82156)
         in
      let h_equals_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____82228 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::v0::t1::v1::[] ->
                     let uu____82260 =
                       let uu____82265 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____82266 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____82265, uu____82266)  in
                     FStar_SMTEncoding_Util.mkAnd uu____82260
                 | uu____82267 -> failwith "Impossible")
             in
          uu____82228 r args
        else
          (let uu____82273 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____82273)
         in
      let mk_imp1 r uu___633_82308 =
        match uu___633_82308 with
        | (lhs,uu____82314)::(rhs,uu____82316)::[] ->
            let uu____82357 = encode_formula rhs env  in
            (match uu____82357 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____82372) ->
                      (l1, decls1)
                  | uu____82377 ->
                      let uu____82378 = encode_formula lhs env  in
                      (match uu____82378 with
                       | (l2,decls2) ->
                           let uu____82389 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____82389, (FStar_List.append decls1 decls2)))))
        | uu____82390 -> failwith "impossible"  in
      let mk_ite r uu___634_82418 =
        match uu___634_82418 with
        | (guard,uu____82424)::(_then,uu____82426)::(_else,uu____82428)::[]
            ->
            let uu____82485 = encode_formula guard env  in
            (match uu____82485 with
             | (g,decls1) ->
                 let uu____82496 = encode_formula _then env  in
                 (match uu____82496 with
                  | (t,decls2) ->
                      let uu____82507 = encode_formula _else env  in
                      (match uu____82507 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____82519 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____82549 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l
           in
        f uu____82549  in
      let connectives =
        let uu____82579 =
          let uu____82604 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____82604)  in
        let uu____82647 =
          let uu____82674 =
            let uu____82699 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____82699)  in
          let uu____82742 =
            let uu____82769 =
              let uu____82796 =
                let uu____82821 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____82821)  in
              let uu____82864 =
                let uu____82891 =
                  let uu____82918 =
                    let uu____82943 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____82943)  in
                  [uu____82918;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.c_eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq3_op);
                  (FStar_Parser_Const.c_eq3_lid, h_equals_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____82891  in
              uu____82796 :: uu____82864  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____82769  in
          uu____82674 :: uu____82742  in
        uu____82579 :: uu____82647  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____83488 = encode_formula phi' env  in
            (match uu____83488 with
             | (phi2,decls) ->
                 let uu____83499 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____83499, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____83501 ->
            let uu____83508 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____83508 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____83547 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____83547 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____83559;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____83561;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____83563;
                 FStar_Syntax_Syntax.lbpos = uu____83564;_}::[]),e2)
            ->
            let uu____83591 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____83591 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____83644::(x,uu____83646)::(t,uu____83648)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____83715 = encode_term x env  in
                 (match uu____83715 with
                  | (x1,decls) ->
                      let uu____83726 = encode_term t env  in
                      (match uu____83726 with
                       | (t1,decls') ->
                           let uu____83737 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____83737, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____83740)::(msg,uu____83742)::(phi2,uu____83744)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____83811 =
                   let uu____83816 =
                     let uu____83817 = FStar_Syntax_Subst.compress r  in
                     uu____83817.FStar_Syntax_Syntax.n  in
                   let uu____83820 =
                     let uu____83821 = FStar_Syntax_Subst.compress msg  in
                     uu____83821.FStar_Syntax_Syntax.n  in
                   (uu____83816, uu____83820)  in
                 (match uu____83811 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____83830))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____83841 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____83848)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____83883 when head_redex env head2 ->
                 let uu____83898 = whnf env phi1  in
                 encode_formula uu____83898 env
             | uu____83899 ->
                 let uu____83914 = encode_term phi1 env  in
                 (match uu____83914 with
                  | (tt,decls) ->
                      let tt1 =
                        let uu____83926 =
                          let uu____83928 =
                            FStar_Range.use_range
                              tt.FStar_SMTEncoding_Term.rng
                             in
                          let uu____83929 =
                            FStar_Range.use_range
                              phi1.FStar_Syntax_Syntax.pos
                             in
                          FStar_Range.rng_included uu____83928 uu____83929
                           in
                        if uu____83926
                        then tt
                        else
                          (let uu___2246_83933 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___2246_83933.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___2246_83933.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      let uu____83934 = FStar_SMTEncoding_Term.mk_Valid tt1
                         in
                      (uu____83934, decls)))
        | uu____83935 ->
            let uu____83936 = encode_term phi1 env  in
            (match uu____83936 with
             | (tt,decls) ->
                 let tt1 =
                   let uu____83948 =
                     let uu____83950 =
                       FStar_Range.use_range tt.FStar_SMTEncoding_Term.rng
                        in
                     let uu____83951 =
                       FStar_Range.use_range phi1.FStar_Syntax_Syntax.pos  in
                     FStar_Range.rng_included uu____83950 uu____83951  in
                   if uu____83948
                   then tt
                   else
                     (let uu___2254_83955 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___2254_83955.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___2254_83955.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 let uu____83956 = FStar_SMTEncoding_Term.mk_Valid tt1  in
                 (uu____83956, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____84000 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____84000 with
        | (vars,guards,env2,decls,uu____84039) ->
            let uu____84052 = encode_smt_patterns ps env2  in
            (match uu____84052 with
             | (pats,decls') ->
                 let uu____84089 = encode_formula body env2  in
                 (match uu____84089 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____84121;
                             FStar_SMTEncoding_Term.rng = uu____84122;_}::[])::[]
                            when
                            let uu____84142 =
                              FStar_Ident.text_of_lid
                                FStar_Parser_Const.guard_free
                               in
                            uu____84142 = gf -> []
                        | uu____84145 -> guards  in
                      let uu____84150 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____84150, body1,
                        (FStar_List.append decls
                           (FStar_List.append decls' decls'')))))
         in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi  in
       let uu____84161 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____84161 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____84170 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____84276  ->
                     match uu____84276 with
                     | (l,uu____84301) -> FStar_Ident.lid_equals op l))
              in
           (match uu____84170 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____84370,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____84462 = encode_q_body env vars pats body  in
             match uu____84462 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____84507 =
                     let uu____84518 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____84518)  in
                   FStar_SMTEncoding_Term.mkForall
                     phi1.FStar_Syntax_Syntax.pos uu____84507
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____84549 = encode_q_body env vars pats body  in
             match uu____84549 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____84593 =
                   let uu____84594 =
                     let uu____84605 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____84605)  in
                   FStar_SMTEncoding_Term.mkExists
                     phi1.FStar_Syntax_Syntax.pos uu____84594
                    in
                 (uu____84593, decls))))
