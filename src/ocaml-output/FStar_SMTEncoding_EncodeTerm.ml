open Prims
let mkForall_fuel' :
  'Auu____71268 .
    Prims.string ->
      FStar_Range.range ->
        'Auu____71268 ->
          (FStar_SMTEncoding_Term.pat Prims.list Prims.list *
            FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term) ->
            FStar_SMTEncoding_Term.term
  =
  fun mname  ->
    fun r  ->
      fun n1  ->
        fun uu____71299  ->
          match uu____71299 with
          | (pats,vars,body) ->
              let fallback uu____71327 =
                FStar_SMTEncoding_Term.mkForall r (pats, vars, body)  in
              let uu____71332 = FStar_Options.unthrottle_inductives ()  in
              if uu____71332
              then fallback ()
              else
                (let uu____71337 =
                   FStar_SMTEncoding_Env.fresh_fvar mname "f"
                     FStar_SMTEncoding_Term.Fuel_sort
                    in
                 match uu____71337 with
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
                               | uu____71377 -> p))
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
                                 let uu____71398 = add_fuel1 guards  in
                                 FStar_SMTEncoding_Util.mk_and_l uu____71398
                             | uu____71401 ->
                                 let uu____71402 = add_fuel1 [guard]  in
                                 FStar_All.pipe_right uu____71402
                                   FStar_List.hd
                              in
                           FStar_SMTEncoding_Util.mkImp (guard1, body')
                       | uu____71407 -> body  in
                     let vars1 =
                       let uu____71419 =
                         FStar_SMTEncoding_Term.mk_fv
                           (fsym, FStar_SMTEncoding_Term.Fuel_sort)
                          in
                       uu____71419 :: vars  in
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
      | FStar_Syntax_Syntax.Tm_arrow uu____71483 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____71499 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____71507 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____71509 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____71523 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____71543 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____71546 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____71546 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____71565;
             FStar_Syntax_Syntax.vars = uu____71566;_},uu____71567)
          ->
          let uu____71592 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____71592 FStar_Option.isNone
      | uu____71610 -> false
  
let (head_redex :
  FStar_SMTEncoding_Env.env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____71624 =
        let uu____71625 = FStar_Syntax_Util.un_uinst t  in
        uu____71625.FStar_Syntax_Syntax.n  in
      match uu____71624 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____71629,uu____71630,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___630_71655  ->
                  match uu___630_71655 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____71658 -> false)
               rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____71661 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____71661 FStar_Option.isSome
      | uu____71679 -> false
  
let (whnf :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____71692 = head_normal env t  in
      if uu____71692
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
    let uu____71714 =
      let uu____71715 = FStar_Syntax_Syntax.null_binder t  in [uu____71715]
       in
    let uu____71734 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    FStar_Syntax_Util.abs uu____71714 uu____71734
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
                let uu____71756 = FStar_SMTEncoding_Term.fv_sort var  in
                match uu____71756 with
                | FStar_SMTEncoding_Term.Fuel_sort  ->
                    let uu____71757 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____71757
                | s ->
                    let uu____71760 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____71760) e)
  
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
          let uu____71816 =
            let uu____71822 =
              let uu____71824 = FStar_Util.string_of_int arity  in
              let uu____71826 = FStar_Util.string_of_int n_args  in
              FStar_Util.format3
                "Head symbol %s expects at least %s arguments; got only %s"
                head1 uu____71824 uu____71826
               in
            (FStar_Errors.Fatal_SMTEncodingArityMismatch, uu____71822)  in
          FStar_Errors.raise_error uu____71816 rng
  
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
                  (let uu____71885 = FStar_Util.first_N arity args  in
                   match uu____71885 with
                   | (args1,rest) ->
                       let head3 =
                         FStar_SMTEncoding_Util.mkApp' (head2, args1)  in
                       mk_Apply_args head3 rest)
                else
                  (let uu____71909 =
                     FStar_SMTEncoding_Term.op_to_string head2  in
                   raise_arity_mismatch uu____71909 arity n_args rng)
  
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
          let uu____71936 = FStar_SMTEncoding_Env.force_thunk fvb  in
          mk_Apply_args uu____71936 args
        else
          maybe_curry_app rng
            (FStar_Util.Inl
               (FStar_SMTEncoding_Term.Var (fvb.FStar_SMTEncoding_Env.smt_id)))
            fvb.FStar_SMTEncoding_Env.smt_arity args
  
let (is_app : FStar_SMTEncoding_Term.op -> Prims.bool) =
  fun uu___631_71945  ->
    match uu___631_71945 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____71951 -> false
  
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
                       FStar_SMTEncoding_Term.freevars = uu____71999;
                       FStar_SMTEncoding_Term.rng = uu____72000;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____72031) ->
              let uu____72041 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____72058 -> false) args (FStar_List.rev xs))
                 in
              if uu____72041
              then FStar_SMTEncoding_Env.tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____72065,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t  in
              let uu____72069 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____72077 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars
                           in
                        Prims.op_Negation uu____72077))
                 in
              if uu____72069
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____72084 -> FStar_Pervasives_Native.None  in
        check_partial_applications body (FStar_List.rev vars)
  
let check_pattern_vars :
  'Auu____72102 'Auu____72103 .
    FStar_SMTEncoding_Env.env_t ->
      (FStar_Syntax_Syntax.bv * 'Auu____72102) Prims.list ->
        (FStar_Syntax_Syntax.term * 'Auu____72103) Prims.list -> unit
  =
  fun env  ->
    fun vars  ->
      fun pats  ->
        let pats1 =
          FStar_All.pipe_right pats
            (FStar_List.map
               (fun uu____72161  ->
                  match uu____72161 with
                  | (x,uu____72167) ->
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
              let uu____72175 = FStar_Syntax_Free.names hd1  in
              FStar_List.fold_left
                (fun out  ->
                   fun x  ->
                     let uu____72187 = FStar_Syntax_Free.names x  in
                     FStar_Util.set_union out uu____72187) uu____72175 tl1
               in
            let uu____72190 =
              FStar_All.pipe_right vars
                (FStar_Util.find_opt
                   (fun uu____72217  ->
                      match uu____72217 with
                      | (b,uu____72224) ->
                          let uu____72225 = FStar_Util.set_mem b pat_vars  in
                          Prims.op_Negation uu____72225))
               in
            (match uu____72190 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some (x,uu____72232) ->
                 let pos =
                   FStar_List.fold_left
                     (fun out  ->
                        fun t  ->
                          FStar_Range.union_ranges out
                            t.FStar_Syntax_Syntax.pos)
                     hd1.FStar_Syntax_Syntax.pos tl1
                    in
                 let uu____72246 =
                   let uu____72252 =
                     let uu____72254 = FStar_Syntax_Print.bv_to_string x  in
                     FStar_Util.format1
                       "SMT pattern misses at least one bound variable: %s"
                       uu____72254
                      in
                   (FStar_Errors.Warning_SMTPatternIllFormed, uu____72252)
                    in
                 FStar_Errors.log_issue pos uu____72246)
  
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
        | FStar_Syntax_Syntax.Tm_arrow uu____72540 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____72555 ->
            let uu____72562 = FStar_Syntax_Util.unrefine t1  in
            aux true uu____72562
        | uu____72564 ->
            if norm1
            then let uu____72566 = whnf env t1  in aux false uu____72566
            else
              (let uu____72570 =
                 let uu____72572 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let uu____72574 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____72572 uu____72574
                  in
               failwith uu____72570)
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
    | FStar_Syntax_Syntax.Tm_refine (bv,uu____72616) ->
        let uu____72621 =
          curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort  in
        (match uu____72621 with
         | (args,res) ->
             (match args with
              | [] ->
                  let uu____72642 = FStar_Syntax_Syntax.mk_Total k1  in
                  ([], uu____72642)
              | uu____72649 -> (args, res)))
    | uu____72650 ->
        let uu____72651 = FStar_Syntax_Syntax.mk_Total k1  in
        ([], uu____72651)
  
let is_arithmetic_primitive :
  'Auu____72665 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____72665 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____72688::uu____72689::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____72693::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____72696 -> false
  
let (isInteger : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____72727 -> false
  
let (getInteger : FStar_Syntax_Syntax.term' -> Prims.int) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____72750 -> failwith "Expected an Integer term"
  
let is_BitVector_primitive :
  'Auu____72760 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____72760)
        Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____72802)::uu____72803::uu____72804::[]) ->
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
         fv,(sz_arg,uu____72855)::uu____72856::[]) ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____72893 -> false
  
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
          let uu____73217 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue  in
          (uu____73217, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____73219 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse  in
          (uu____73219, [])
      | FStar_Const.Const_char c1 ->
          let uu____73222 =
            let uu____73223 =
              let uu____73231 =
                let uu____73234 =
                  let uu____73235 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1)
                     in
                  FStar_SMTEncoding_Term.boxInt uu____73235  in
                [uu____73234]  in
              ("FStar.Char.__char_of_int", uu____73231)  in
            FStar_SMTEncoding_Util.mkApp uu____73223  in
          (uu____73222, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____73253 =
            let uu____73254 = FStar_SMTEncoding_Util.mkInteger i  in
            FStar_SMTEncoding_Term.boxInt uu____73254  in
          (uu____73253, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.FStar_SMTEncoding_Env.tcenv).FStar_TypeChecker_Env.dsenv
              repr sw FStar_Range.dummyRange
             in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____73275) ->
          let uu____73278 =
            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.string_const s
             in
          (uu____73278, [])
      | FStar_Const.Const_range uu____73279 ->
          let uu____73280 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          (uu____73280, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | FStar_Const.Const_real r ->
          let uu____73283 =
            let uu____73284 = FStar_SMTEncoding_Util.mkReal r  in
            FStar_SMTEncoding_Term.boxReal uu____73284  in
          (uu____73283, [])
      | c1 ->
          let uu____73286 =
            let uu____73288 = FStar_Syntax_Print.const_to_string c1  in
            FStar_Util.format1 "Unhandled constant: %s" uu____73288  in
          failwith uu____73286

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
        (let uu____73317 =
           FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
             FStar_Options.Medium
            in
         if uu____73317
         then
           let uu____73320 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____73320
         else ());
        (let uu____73326 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____73408  ->
                   fun b  ->
                     match uu____73408 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____73473 =
                           let x = FStar_Pervasives_Native.fst b  in
                           let uu____73489 =
                             FStar_SMTEncoding_Env.gen_term_var env1 x  in
                           match uu____73489 with
                           | (xxsym,xx,env') ->
                               let uu____73514 =
                                 let uu____73519 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____73519 env1
                                   xx
                                  in
                               (match uu____73514 with
                                | (guard_x_t,decls') ->
                                    let uu____73534 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xxsym,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    (uu____73534, guard_x_t, env', decls', x))
                            in
                         (match uu____73473 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____73326 with
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
          let uu____73634 = encode_term t env  in
          match uu____73634 with
          | (t1,decls) ->
              let uu____73645 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____73645, decls)

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
          let uu____73656 = encode_term t env  in
          match uu____73656 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____73671 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____73671, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____73673 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____73673, decls))

and (encode_arith_term :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____73679 = encode_args args_e env  in
        match uu____73679 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____73698 -> failwith "Impossible"  in
            let unary unbox arg_tms1 =
              let uu____73720 = FStar_List.hd arg_tms1  in unbox uu____73720
               in
            let binary unbox arg_tms1 =
              let uu____73745 =
                let uu____73746 = FStar_List.hd arg_tms1  in
                unbox uu____73746  in
              let uu____73747 =
                let uu____73748 =
                  let uu____73749 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____73749  in
                unbox uu____73748  in
              (uu____73745, uu____73747)  in
            let mk_default uu____73757 =
              let uu____73758 =
                FStar_SMTEncoding_Env.lookup_free_var_sym env
                  head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____73758 with
              | (fname,fuel_args,arity) ->
                  let args = FStar_List.append fuel_args arg_tms  in
                  maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity
                    args
               in
            let mk_l box op mk_args ts =
              let uu____73847 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____73847
              then
                let uu____73850 =
                  let uu____73851 = mk_args ts  in op uu____73851  in
                FStar_All.pipe_right uu____73850 box
              else mk_default ()  in
            let mk_nl box unbox nm op ts =
              let uu____73909 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____73909
              then
                let uu____73912 = binary unbox ts  in
                match uu____73912 with
                | (t1,t2) ->
                    let uu____73919 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____73919 box
              else
                (let uu____73925 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____73925
                 then
                   let uu____73928 =
                     let uu____73929 = binary unbox ts  in op uu____73929  in
                   FStar_All.pipe_right uu____73928 box
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
            let uu____74364 =
              let uu____74374 =
                FStar_List.tryFind
                  (fun uu____74398  ->
                     match uu____74398 with
                     | (l,uu____74409) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____74374 FStar_Util.must  in
            (match uu____74364 with
             | (uu____74453,op) ->
                 let uu____74465 = op arg_tms  in (uu____74465, decls))

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
        let uu____74481 = FStar_List.hd args_e  in
        match uu____74481 with
        | (tm_sz,uu____74497) ->
            let uu____74506 = uu____74481  in
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let t_decls1 = FStar_SMTEncoding_Term.mkBvConstructor sz  in
              FStar_SMTEncoding_Term.mk_decls "" sz_key t_decls1 []  in
            let uu____74517 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____74543::(sz_arg,uu____74545)::uu____74546::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____74613 =
                    let uu____74614 = FStar_List.tail args_e  in
                    FStar_List.tail uu____74614  in
                  let uu____74641 =
                    let uu____74645 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____74645  in
                  (uu____74613, uu____74641)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____74652::(sz_arg,uu____74654)::uu____74655::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____74722 =
                    let uu____74724 =
                      FStar_Syntax_Print.term_to_string sz_arg  in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____74724
                     in
                  failwith uu____74722
              | uu____74734 ->
                  let uu____74749 = FStar_List.tail args_e  in
                  (uu____74749, FStar_Pervasives_Native.None)
               in
            (match uu____74517 with
             | (arg_tms,ext_sz) ->
                 let uu____74776 = encode_args arg_tms env  in
                 (match uu____74776 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____74797 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____74809 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____74809  in
                      let unary_arith arg_tms2 =
                        let uu____74820 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____74820  in
                      let binary arg_tms2 =
                        let uu____74835 =
                          let uu____74836 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____74836
                           in
                        let uu____74837 =
                          let uu____74838 =
                            let uu____74839 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____74839  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____74838
                           in
                        (uu____74835, uu____74837)  in
                      let binary_arith arg_tms2 =
                        let uu____74856 =
                          let uu____74857 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____74857
                           in
                        let uu____74858 =
                          let uu____74859 =
                            let uu____74860 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____74860  in
                          FStar_SMTEncoding_Term.unboxInt uu____74859  in
                        (uu____74856, uu____74858)  in
                      let mk_bv op mk_args resBox ts =
                        let uu____74918 =
                          let uu____74919 = mk_args ts  in op uu____74919  in
                        FStar_All.pipe_right uu____74918 resBox  in
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
                        let uu____75051 =
                          let uu____75056 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____75056  in
                        let uu____75065 =
                          let uu____75070 =
                            let uu____75072 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____75072  in
                          FStar_SMTEncoding_Term.boxBitVec uu____75070  in
                        mk_bv uu____75051 unary uu____75065 arg_tms2  in
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
                      let uu____75312 =
                        let uu____75322 =
                          FStar_List.tryFind
                            (fun uu____75346  ->
                               match uu____75346 with
                               | (l,uu____75357) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____75322 FStar_Util.must  in
                      (match uu____75312 with
                       | (uu____75403,op) ->
                           let uu____75415 = op arg_tms1  in
                           (uu____75415, (FStar_List.append sz_decls decls)))))

and (encode_deeply_embedded_quantifier :
  FStar_Syntax_Syntax.term ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let env1 =
        let uu___1170_75425 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___1170_75425.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___1170_75425.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___1170_75425.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___1170_75425.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___1170_75425.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___1170_75425.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name =
            (uu___1170_75425.FStar_SMTEncoding_Env.use_zfuel_name);
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___1170_75425.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___1170_75425.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier = true;
          FStar_SMTEncoding_Env.global_cache =
            (uu___1170_75425.FStar_SMTEncoding_Env.global_cache)
        }  in
      let uu____75427 = encode_term t env1  in
      match uu____75427 with
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
               (uu____75453,{
                              FStar_SMTEncoding_Term.tm =
                                FStar_SMTEncoding_Term.FreeV uu____75454;
                              FStar_SMTEncoding_Term.freevars = uu____75455;
                              FStar_SMTEncoding_Term.rng = uu____75456;_}::
                {
                  FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV
                    uu____75457;
                  FStar_SMTEncoding_Term.freevars = uu____75458;
                  FStar_SMTEncoding_Term.rng = uu____75459;_}::[])
               ->
               (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                  (FStar_Errors.Warning_QuantifierWithoutPattern,
                    "Not encoding deeply embedded, unguarded quantifier to SMT");
                (tm, decls))
           | uu____75505 ->
               let uu____75506 = encode_formula t env1  in
               (match uu____75506 with
                | (phi,decls') ->
                    let interp =
                      match vars with
                      | [] ->
                          let uu____75526 =
                            let uu____75531 =
                              FStar_SMTEncoding_Term.mk_Valid tm  in
                            (uu____75531, phi)  in
                          FStar_SMTEncoding_Util.mkIff uu____75526
                      | uu____75532 ->
                          let uu____75533 =
                            let uu____75544 =
                              let uu____75545 =
                                let uu____75550 =
                                  FStar_SMTEncoding_Term.mk_Valid tm  in
                                (uu____75550, phi)  in
                              FStar_SMTEncoding_Util.mkIff uu____75545  in
                            ([[valid_tm]], vars, uu____75544)  in
                          FStar_SMTEncoding_Term.mkForall
                            t.FStar_Syntax_Syntax.pos uu____75533
                       in
                    let ax =
                      let uu____75560 =
                        let uu____75568 =
                          let uu____75570 =
                            FStar_Util.digest_of_string tkey_hash  in
                          Prims.op_Hat "l_quant_interp_" uu____75570  in
                        (interp,
                          (FStar_Pervasives_Native.Some
                             "Interpretation of deeply embedded quantifier"),
                          uu____75568)
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____75560  in
                    let uu____75576 =
                      let uu____75577 =
                        let uu____75580 =
                          FStar_SMTEncoding_Term.mk_decls "" tkey_hash 
                            [ax] (FStar_List.append decls decls')
                           in
                        FStar_List.append decls' uu____75580  in
                      FStar_List.append decls uu____75577  in
                    (tm, uu____75576)))

and (encode_term :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____75592 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____75592
       then
         let uu____75597 = FStar_Syntax_Print.tag_of_term t  in
         let uu____75599 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____75601 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____75597 uu____75599
           uu____75601
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____75610 ->
           let uu____75633 =
             let uu____75635 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____75638 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____75640 = FStar_Syntax_Print.term_to_string t0  in
             let uu____75642 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____75635
               uu____75638 uu____75640 uu____75642
              in
           failwith uu____75633
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____75649 =
             let uu____75651 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____75654 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____75656 = FStar_Syntax_Print.term_to_string t0  in
             let uu____75658 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____75651
               uu____75654 uu____75656 uu____75658
              in
           failwith uu____75649
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let e = FStar_Syntax_Util.unfold_lazy i  in
           ((let uu____75668 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____75668
             then
               let uu____75673 = FStar_Syntax_Print.term_to_string t0  in
               let uu____75675 = FStar_Syntax_Print.term_to_string e  in
               FStar_Util.print2 ">> Unfolded (%s) ~> (%s)\n" uu____75673
                 uu____75675
             else ());
            encode_term e env)
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____75681 =
             let uu____75683 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____75683
              in
           failwith uu____75681
       | FStar_Syntax_Syntax.Tm_ascribed (t1,(k,uu____75692),uu____75693) ->
           let uu____75742 =
             match k with
             | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
             | uu____75752 -> false  in
           if uu____75742
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t1 env
       | FStar_Syntax_Syntax.Tm_quoted (qt,uu____75770) ->
           let tv =
             let uu____75776 =
               let uu____75783 = FStar_Reflection_Basic.inspect_ln qt  in
               FStar_Syntax_Embeddings.embed
                 FStar_Reflection_Embeddings.e_term_view uu____75783
                in
             uu____75776 t.FStar_Syntax_Syntax.pos
               FStar_Pervasives_Native.None
               FStar_Syntax_Embeddings.id_norm_cb
              in
           ((let uu____75810 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____75810
             then
               let uu____75815 = FStar_Syntax_Print.term_to_string t0  in
               let uu____75817 = FStar_Syntax_Print.term_to_string tv  in
               FStar_Util.print2 ">> Inspected (%s) ~> (%s)\n" uu____75815
                 uu____75817
             else ());
            (let t1 =
               let uu____75825 =
                 let uu____75836 = FStar_Syntax_Syntax.as_arg tv  in
                 [uu____75836]  in
               FStar_Syntax_Util.mk_app
                 (FStar_Reflection_Data.refl_constant_term
                    FStar_Reflection_Data.fstar_refl_pack_ln) uu____75825
                in
             encode_term t1 env))
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_pattern uu____75862) ->
           encode_term t1
             (let uu___1242_75880 = env  in
              {
                FStar_SMTEncoding_Env.bvar_bindings =
                  (uu___1242_75880.FStar_SMTEncoding_Env.bvar_bindings);
                FStar_SMTEncoding_Env.fvar_bindings =
                  (uu___1242_75880.FStar_SMTEncoding_Env.fvar_bindings);
                FStar_SMTEncoding_Env.depth =
                  (uu___1242_75880.FStar_SMTEncoding_Env.depth);
                FStar_SMTEncoding_Env.tcenv =
                  (uu___1242_75880.FStar_SMTEncoding_Env.tcenv);
                FStar_SMTEncoding_Env.warn =
                  (uu___1242_75880.FStar_SMTEncoding_Env.warn);
                FStar_SMTEncoding_Env.nolabels =
                  (uu___1242_75880.FStar_SMTEncoding_Env.nolabels);
                FStar_SMTEncoding_Env.use_zfuel_name =
                  (uu___1242_75880.FStar_SMTEncoding_Env.use_zfuel_name);
                FStar_SMTEncoding_Env.encode_non_total_function_typ =
                  (uu___1242_75880.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                FStar_SMTEncoding_Env.current_module_name =
                  (uu___1242_75880.FStar_SMTEncoding_Env.current_module_name);
                FStar_SMTEncoding_Env.encoding_quantifier = false;
                FStar_SMTEncoding_Env.global_cache =
                  (uu___1242_75880.FStar_SMTEncoding_Env.global_cache)
              })
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____75883) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = FStar_SMTEncoding_Env.lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____75891 = head_redex env t  in
           if uu____75891
           then let uu____75898 = whnf env t  in encode_term uu____75898 env
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
              let uu____75905 =
                if
                  fvb.FStar_SMTEncoding_Env.smt_arity > (Prims.parse_int "0")
                then
                  match tok.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.FreeV uu____75929 ->
                      let sym_name =
                        let uu____75940 =
                          FStar_Util.digest_of_string tkey_hash  in
                        Prims.op_Hat "@kick_partial_app_" uu____75940  in
                      let uu____75943 =
                        let uu____75946 =
                          let uu____75947 =
                            let uu____75955 =
                              FStar_SMTEncoding_Term.kick_partial_app tok  in
                            (uu____75955,
                              (FStar_Pervasives_Native.Some
                                 "kick_partial_app"), sym_name)
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____75947  in
                        [uu____75946]  in
                      (uu____75943, sym_name)
                  | FStar_SMTEncoding_Term.App (uu____75962,[]) ->
                      let sym_name =
                        let uu____75967 =
                          FStar_Util.digest_of_string tkey_hash  in
                        Prims.op_Hat "@kick_partial_app_" uu____75967  in
                      let uu____75970 =
                        let uu____75973 =
                          let uu____75974 =
                            let uu____75982 =
                              FStar_SMTEncoding_Term.kick_partial_app tok  in
                            (uu____75982,
                              (FStar_Pervasives_Native.Some
                                 "kick_partial_app"), sym_name)
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____75974  in
                        [uu____75973]  in
                      (uu____75970, sym_name)
                  | uu____75989 -> ([], "")
                else ([], "")  in
              match uu____75905 with
              | (aux_decls,sym_name) ->
                  let uu____76012 =
                    if aux_decls = []
                    then
                      FStar_All.pipe_right []
                        FStar_SMTEncoding_Term.mk_decls_trivial
                    else
                      FStar_SMTEncoding_Term.mk_decls sym_name tkey_hash
                        aux_decls []
                     in
                  (tok, uu____76012))
       | FStar_Syntax_Syntax.Tm_type uu____76020 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____76022) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.FStar_SMTEncoding_Env.current_module_name
              in
           let uu____76052 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____76052 with
            | (binders1,res) ->
                let uu____76063 =
                  (env.FStar_SMTEncoding_Env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____76063
                then
                  let uu____76070 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____76070 with
                   | (vars,guards,env',decls,uu____76095) ->
                       let fsym =
                         let uu____76109 =
                           let uu____76115 =
                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                               module_name "f"
                              in
                           (uu____76115, FStar_SMTEncoding_Term.Term_sort)
                            in
                         FStar_SMTEncoding_Term.mk_fv uu____76109  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____76121 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___1296_76130 =
                              env.FStar_SMTEncoding_Env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___1296_76130.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___1296_76130.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___1296_76130.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___1296_76130.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___1296_76130.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___1296_76130.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___1296_76130.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___1296_76130.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___1296_76130.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___1296_76130.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___1296_76130.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___1296_76130.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___1296_76130.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___1296_76130.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___1296_76130.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___1296_76130.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___1296_76130.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___1296_76130.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___1296_76130.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___1296_76130.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___1296_76130.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___1296_76130.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___1296_76130.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___1296_76130.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___1296_76130.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___1296_76130.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___1296_76130.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___1296_76130.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___1296_76130.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___1296_76130.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___1296_76130.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___1296_76130.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___1296_76130.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___1296_76130.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___1296_76130.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___1296_76130.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___1296_76130.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___1296_76130.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___1296_76130.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___1296_76130.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___1296_76130.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___1296_76130.FStar_TypeChecker_Env.nbe)
                            }) res
                          in
                       (match uu____76121 with
                        | (pre_opt,res_t) ->
                            let uu____76142 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____76142 with
                             | (res_pred,decls') ->
                                 let uu____76153 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____76166 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____76166, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____76170 =
                                         encode_formula pre env'  in
                                       (match uu____76170 with
                                        | (guard,decls0) ->
                                            let uu____76183 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____76183, decls0))
                                    in
                                 (match uu____76153 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____76197 =
                                          let uu____76208 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____76208)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t.FStar_Syntax_Syntax.pos
                                          uu____76197
                                         in
                                      let cvars =
                                        let uu____76228 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____76228
                                          (FStar_List.filter
                                             (fun x  ->
                                                let uu____76247 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    x
                                                   in
                                                let uu____76249 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    fsym
                                                   in
                                                uu____76247 <> uu____76249))
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
                                        let uu____76271 =
                                          FStar_Util.digest_of_string
                                            tkey_hash
                                           in
                                        Prims.op_Hat "Tm_arrow_" uu____76271
                                         in
                                      let cvar_sorts =
                                        FStar_List.map
                                          FStar_SMTEncoding_Term.fv_sort
                                          cvars
                                         in
                                      let caption =
                                        let uu____76286 =
                                          FStar_Options.log_queries ()  in
                                        if uu____76286
                                        then
                                          let uu____76289 =
                                            let uu____76291 =
                                              FStar_TypeChecker_Normalize.term_to_string
                                                env.FStar_SMTEncoding_Env.tcenv
                                                t0
                                               in
                                            FStar_Util.replace_char
                                              uu____76291 10 32
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____76289
                                        else FStar_Pervasives_Native.None  in
                                      let tdecl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (tsym, cvar_sorts,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            caption)
                                         in
                                      let t1 =
                                        let uu____76304 =
                                          let uu____76312 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              cvars
                                             in
                                          (tsym, uu____76312)  in
                                        FStar_SMTEncoding_Util.mkApp
                                          uu____76304
                                         in
                                      let t_has_kind =
                                        FStar_SMTEncoding_Term.mk_HasType t1
                                          FStar_SMTEncoding_Term.mk_Term_type
                                         in
                                      let k_assumption =
                                        let a_name =
                                          Prims.op_Hat "kinding_" tsym  in
                                        let uu____76331 =
                                          let uu____76339 =
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              ([[t_has_kind]], cvars,
                                                t_has_kind)
                                             in
                                          (uu____76339,
                                            (FStar_Pervasives_Native.Some
                                               a_name), a_name)
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____76331
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
                                        let uu____76356 =
                                          let uu____76364 =
                                            let uu____76365 =
                                              let uu____76376 =
                                                let uu____76377 =
                                                  let uu____76382 =
                                                    let uu____76383 =
                                                      FStar_SMTEncoding_Term.mk_PreType
                                                        f
                                                       in
                                                    FStar_SMTEncoding_Term.mk_tester
                                                      "Tm_arrow" uu____76383
                                                     in
                                                  (f_has_t, uu____76382)  in
                                                FStar_SMTEncoding_Util.mkImp
                                                  uu____76377
                                                 in
                                              ([[f_has_t]], (fsym :: cvars),
                                                uu____76376)
                                               in
                                            let uu____76401 =
                                              mkForall_fuel module_name
                                                t0.FStar_Syntax_Syntax.pos
                                               in
                                            uu____76401 uu____76365  in
                                          (uu____76364,
                                            (FStar_Pervasives_Native.Some
                                               "pre-typing for functions"),
                                            (Prims.op_Hat module_name
                                               (Prims.op_Hat "_" a_name)))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____76356
                                         in
                                      let t_interp1 =
                                        let a_name =
                                          Prims.op_Hat "interpretation_" tsym
                                           in
                                        let uu____76424 =
                                          let uu____76432 =
                                            let uu____76433 =
                                              let uu____76444 =
                                                FStar_SMTEncoding_Util.mkIff
                                                  (f_has_t_z, t_interp)
                                                 in
                                              ([[f_has_t_z]], (fsym ::
                                                cvars), uu____76444)
                                               in
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              uu____76433
                                             in
                                          (uu____76432,
                                            (FStar_Pervasives_Native.Some
                                               a_name),
                                            (Prims.op_Hat module_name
                                               (Prims.op_Hat "_" a_name)))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____76424
                                         in
                                      let t_decls1 =
                                        [tdecl;
                                        k_assumption;
                                        pre_typing;
                                        t_interp1]  in
                                      let uu____76467 =
                                        let uu____76468 =
                                          let uu____76471 =
                                            let uu____76474 =
                                              FStar_SMTEncoding_Term.mk_decls
                                                tsym tkey_hash t_decls1
                                                (FStar_List.append decls
                                                   (FStar_List.append decls'
                                                      guard_decls))
                                               in
                                            FStar_List.append guard_decls
                                              uu____76474
                                             in
                                          FStar_List.append decls'
                                            uu____76471
                                           in
                                        FStar_List.append decls uu____76468
                                         in
                                      (t1, uu____76467)))))
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
                     let uu____76495 =
                       let uu____76503 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____76503,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"), a_name)
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____76495  in
                   let fsym =
                     FStar_SMTEncoding_Term.mk_fv
                       ("f", FStar_SMTEncoding_Term.Term_sort)
                      in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.op_Hat "pre_typing_" tsym  in
                     let uu____76516 =
                       let uu____76524 =
                         let uu____76525 =
                           let uu____76536 =
                             let uu____76537 =
                               let uu____76542 =
                                 let uu____76543 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____76543
                                  in
                               (f_has_t, uu____76542)  in
                             FStar_SMTEncoding_Util.mkImp uu____76537  in
                           ([[f_has_t]], [fsym], uu____76536)  in
                         let uu____76569 =
                           mkForall_fuel module_name
                             t0.FStar_Syntax_Syntax.pos
                            in
                         uu____76569 uu____76525  in
                       (uu____76524, (FStar_Pervasives_Native.Some a_name),
                         a_name)
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____76516  in
                   let uu____76586 =
                     FStar_All.pipe_right [tdecl; t_kinding; t_interp]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                      in
                   (t1, uu____76586)))
       | FStar_Syntax_Syntax.Tm_refine uu____76589 ->
           let uu____76596 =
             let uu____76601 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Env.Weak;
                 FStar_TypeChecker_Env.HNF;
                 FStar_TypeChecker_Env.EraseUniverses]
                 env.FStar_SMTEncoding_Env.tcenv t0
                in
             match uu____76601 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____76608;
                 FStar_Syntax_Syntax.vars = uu____76609;_} ->
                 let uu____76616 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____76616 with
                  | (b,f1) ->
                      let uu____76641 =
                        let uu____76642 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____76642  in
                      (uu____76641, f1))
             | uu____76657 -> failwith "impossible"  in
           (match uu____76596 with
            | (x,f) ->
                let uu____76669 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____76669 with
                 | (base_t,decls) ->
                     let uu____76680 =
                       FStar_SMTEncoding_Env.gen_term_var env x  in
                     (match uu____76680 with
                      | (x1,xtm,env') ->
                          let uu____76697 = encode_formula f env'  in
                          (match uu____76697 with
                           | (refinement,decls') ->
                               let uu____76708 =
                                 FStar_SMTEncoding_Env.fresh_fvar
                                   env.FStar_SMTEncoding_Env.current_module_name
                                   "f" FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____76708 with
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
                                      let uu____76736 =
                                        let uu____76747 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____76758 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____76747
                                          uu____76758
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____76736
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun y  ->
                                              (let uu____76812 =
                                                 FStar_SMTEncoding_Term.fv_name
                                                   y
                                                  in
                                               uu____76812 <> x1) &&
                                                (let uu____76816 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     y
                                                    in
                                                 uu____76816 <> fsym)))
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
                                      let uu____76852 =
                                        FStar_Util.digest_of_string tkey_hash
                                         in
                                      Prims.op_Hat "Tm_refine_" uu____76852
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
                                      let uu____76872 =
                                        let uu____76880 =
                                          FStar_List.map
                                            FStar_SMTEncoding_Util.mkFreeV
                                            cvars1
                                           in
                                        (tsym, uu____76880)  in
                                      FStar_SMTEncoding_Util.mkApp
                                        uu____76872
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
                                      let uu____76900 =
                                        let uu____76908 =
                                          let uu____76909 =
                                            let uu____76920 =
                                              FStar_SMTEncoding_Util.mkIff
                                                (t_haseq_ref, t_haseq_base)
                                               in
                                            ([[t_haseq_ref]], cvars1,
                                              uu____76920)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            t0.FStar_Syntax_Syntax.pos
                                            uu____76909
                                           in
                                        (uu____76908,
                                          (FStar_Pervasives_Native.Some
                                             (Prims.op_Hat "haseq for " tsym)),
                                          (Prims.op_Hat "haseq" tsym))
                                         in
                                      FStar_SMTEncoding_Util.mkAssume
                                        uu____76900
                                       in
                                    let t_kinding =
                                      let uu____76934 =
                                        let uu____76942 =
                                          FStar_SMTEncoding_Term.mkForall
                                            t0.FStar_Syntax_Syntax.pos
                                            ([[t_has_kind]], cvars1,
                                              t_has_kind)
                                           in
                                        (uu____76942,
                                          (FStar_Pervasives_Native.Some
                                             "refinement kinding"),
                                          (Prims.op_Hat "refinement_kinding_"
                                             tsym))
                                         in
                                      FStar_SMTEncoding_Util.mkAssume
                                        uu____76934
                                       in
                                    let t_interp =
                                      let uu____76956 =
                                        let uu____76964 =
                                          let uu____76965 =
                                            let uu____76976 =
                                              FStar_SMTEncoding_Util.mkIff
                                                (x_has_t, encoding)
                                               in
                                            ([[x_has_t]], (ffv :: xfv ::
                                              cvars1), uu____76976)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            t0.FStar_Syntax_Syntax.pos
                                            uu____76965
                                           in
                                        (uu____76964,
                                          (FStar_Pervasives_Native.Some
                                             "refinement_interpretation"),
                                          (Prims.op_Hat
                                             "refinement_interpretation_"
                                             tsym))
                                         in
                                      FStar_SMTEncoding_Util.mkAssume
                                        uu____76956
                                       in
                                    let t_decls1 =
                                      [tdecl; t_kinding; t_interp; t_haseq1]
                                       in
                                    let uu____77008 =
                                      let uu____77009 =
                                        let uu____77012 =
                                          FStar_SMTEncoding_Term.mk_decls
                                            tsym tkey_hash t_decls1
                                            (FStar_List.append decls decls')
                                           in
                                        FStar_List.append decls' uu____77012
                                         in
                                      FStar_List.append decls uu____77009  in
                                    (t1, uu____77008))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,uu____77016) ->
           let ttm =
             let uu____77034 =
               FStar_Syntax_Unionfind.uvar_id
                 uv.FStar_Syntax_Syntax.ctx_uvar_head
                in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____77034  in
           let uu____77036 =
             encode_term_pred FStar_Pervasives_Native.None
               uv.FStar_Syntax_Syntax.ctx_uvar_typ env ttm
              in
           (match uu____77036 with
            | (t_has_k,decls) ->
                let d =
                  let uu____77048 =
                    let uu____77056 =
                      let uu____77058 =
                        let uu____77060 =
                          let uu____77062 =
                            FStar_Syntax_Unionfind.uvar_id
                              uv.FStar_Syntax_Syntax.ctx_uvar_head
                             in
                          FStar_Util.string_of_int uu____77062  in
                        FStar_Util.format1 "uvar_typing_%s" uu____77060  in
                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                        uu____77058
                       in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____77056)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____77048  in
                let uu____77068 =
                  let uu____77069 =
                    FStar_All.pipe_right [d]
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append decls uu____77069  in
                (ttm, uu____77068))
       | FStar_Syntax_Syntax.Tm_app uu____77076 ->
           let uu____77093 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____77093 with
            | (head1,args_e) ->
                let uu____77140 =
                  let uu____77155 =
                    let uu____77156 = FStar_Syntax_Subst.compress head1  in
                    uu____77156.FStar_Syntax_Syntax.n  in
                  (uu____77155, args_e)  in
                (match uu____77140 with
                 | uu____77173 when head_redex env head1 ->
                     let uu____77188 = whnf env t  in
                     encode_term uu____77188 env
                 | uu____77189 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____77212 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_fvar fv,uu____77230) when
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
                       FStar_Syntax_Syntax.pos = uu____77252;
                       FStar_Syntax_Syntax.vars = uu____77253;_},uu____77254),uu____77255)
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
                       FStar_Syntax_Syntax.pos = uu____77281;
                       FStar_Syntax_Syntax.vars = uu____77282;_},uu____77283),
                    (v0,uu____77285)::(v1,uu____77287)::(v2,uu____77289)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____77360 = encode_term v0 env  in
                     (match uu____77360 with
                      | (v01,decls0) ->
                          let uu____77371 = encode_term v1 env  in
                          (match uu____77371 with
                           | (v11,decls1) ->
                               let uu____77382 = encode_term v2 env  in
                               (match uu____77382 with
                                | (v21,decls2) ->
                                    let uu____77393 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____77393,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(v0,uu____77396)::(v1,uu____77398)::(v2,uu____77400)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____77467 = encode_term v0 env  in
                     (match uu____77467 with
                      | (v01,decls0) ->
                          let uu____77478 = encode_term v1 env  in
                          (match uu____77478 with
                           | (v11,decls1) ->
                               let uu____77489 = encode_term v2 env  in
                               (match uu____77489 with
                                | (v21,decls2) ->
                                    let uu____77500 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____77500,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____77502)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____77538)::(rng,uu____77540)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____77591) ->
                     let e0 =
                       let uu____77613 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg
                         env.FStar_SMTEncoding_Env.tcenv head1 uu____77613
                        in
                     ((let uu____77623 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug
                              env.FStar_SMTEncoding_Env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____77623
                       then
                         let uu____77628 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____77628
                       else ());
                      (let e =
                         let uu____77636 =
                           let uu____77641 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____77642 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____77641
                             uu____77642
                            in
                         uu____77636 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____77653),(arg,uu____77655)::[]) ->
                     encode_term arg env
                 | uu____77690 ->
                     let uu____77705 = encode_args args_e env  in
                     (match uu____77705 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____77766 = encode_term head1 env  in
                            match uu____77766 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____77838 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____77838 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____77936  ->
                                                 fun uu____77937  ->
                                                   match (uu____77936,
                                                           uu____77937)
                                                   with
                                                   | ((bv,uu____77967),
                                                      (a,uu____77969)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____77999 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____77999
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____78000 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm
                                             in
                                          (match uu____78000 with
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
                                                 let uu____78017 =
                                                   let uu____78025 =
                                                     FStar_SMTEncoding_Term.mkForall
                                                       t0.FStar_Syntax_Syntax.pos
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____78034 =
                                                     let uu____78036 =
                                                       let uu____78038 =
                                                         FStar_SMTEncoding_Term.hash_of_term
                                                           app_tm
                                                          in
                                                       FStar_Util.digest_of_string
                                                         uu____78038
                                                        in
                                                     Prims.op_Hat
                                                       "partial_app_typing_"
                                                       uu____78036
                                                      in
                                                   (uu____78025,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____78034)
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____78017
                                                  in
                                               let uu____78044 =
                                                 let uu____78047 =
                                                   let uu____78050 =
                                                     let uu____78053 =
                                                       FStar_SMTEncoding_Term.mk_decls
                                                         "" tkey_hash
                                                         [e_typing]
                                                         (FStar_List.append
                                                            decls
                                                            (FStar_List.append
                                                               decls' decls''))
                                                        in
                                                     FStar_List.append
                                                       decls'' uu____78053
                                                      in
                                                   FStar_List.append decls'
                                                     uu____78050
                                                    in
                                                 FStar_List.append decls
                                                   uu____78047
                                                  in
                                               (app_tm, uu____78044))))
                             in
                          let encode_full_app fv =
                            let uu____78073 =
                              FStar_SMTEncoding_Env.lookup_free_var_sym env
                                fv
                               in
                            match uu____78073 with
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
                                   FStar_Syntax_Syntax.pos = uu____78116;
                                   FStar_Syntax_Syntax.vars = uu____78117;_},uu____78118)
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
                                   FStar_Syntax_Syntax.pos = uu____78125;
                                   FStar_Syntax_Syntax.vars = uu____78126;_},uu____78127)
                                ->
                                let uu____78132 =
                                  let uu____78133 =
                                    let uu____78138 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____78138
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____78133
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____78132
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____78168 =
                                  let uu____78169 =
                                    let uu____78174 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____78174
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____78169
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____78168
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____78203,(FStar_Util.Inl t1,uu____78205),uu____78206)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____78253,(FStar_Util.Inr c,uu____78255),uu____78256)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____78303 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____78324 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Env.Weak;
                                     FStar_TypeChecker_Env.HNF;
                                     FStar_TypeChecker_Env.EraseUniverses]
                                     env.FStar_SMTEncoding_Env.tcenv
                                     head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____78324
                                  in
                               let uu____78325 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____78325 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____78341;
                                            FStar_Syntax_Syntax.vars =
                                              uu____78342;_},uu____78343)
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
                                     | uu____78361 ->
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
           let uu____78440 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____78440 with
            | (bs1,body1,opening) ->
                let fallback uu____78463 =
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
                  let uu____78473 =
                    let uu____78474 =
                      FStar_SMTEncoding_Term.mk_fv
                        (f, FStar_SMTEncoding_Term.Term_sort)
                       in
                    FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV
                      uu____78474
                     in
                  let uu____78476 =
                    FStar_All.pipe_right [decl]
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  (uu____78473, uu____78476)  in
                let is_impure rc =
                  let uu____78486 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                      env.FStar_SMTEncoding_Env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____78486 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____78501 =
                          let uu____78514 =
                            FStar_TypeChecker_Env.get_range
                              env.FStar_SMTEncoding_Env.tcenv
                             in
                          FStar_TypeChecker_Util.new_implicit_var
                            "SMTEncoding codomain" uu____78514
                            env.FStar_SMTEncoding_Env.tcenv
                            FStar_Syntax_Util.ktype0
                           in
                        (match uu____78501 with
                         | (t1,uu____78517,uu____78518) -> t1)
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  let uu____78536 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                     in
                  if uu____78536
                  then
                    let uu____78541 = FStar_Syntax_Syntax.mk_Total res_typ
                       in
                    FStar_Pervasives_Native.Some uu____78541
                  else
                    (let uu____78544 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid
                        in
                     if uu____78544
                     then
                       let uu____78549 =
                         FStar_Syntax_Syntax.mk_GTotal res_typ  in
                       FStar_Pervasives_Native.Some uu____78549
                     else FStar_Pervasives_Native.None)
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____78557 =
                         let uu____78563 =
                           let uu____78565 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____78565
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____78563)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____78557);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____78570 =
                       (is_impure rc) &&
                         (let uu____78573 =
                            FStar_TypeChecker_Env.is_reifiable_rc
                              env.FStar_SMTEncoding_Env.tcenv rc
                             in
                          Prims.op_Negation uu____78573)
                        in
                     if uu____78570
                     then fallback ()
                     else
                       (let uu____78582 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____78582 with
                        | (vars,guards,envbody,decls,uu____78607) ->
                            let body2 =
                              let uu____78621 =
                                FStar_TypeChecker_Env.is_reifiable_rc
                                  env.FStar_SMTEncoding_Env.tcenv rc
                                 in
                              if uu____78621
                              then
                                FStar_TypeChecker_Util.reify_body
                                  env.FStar_SMTEncoding_Env.tcenv body1
                              else body1  in
                            let uu____78626 = encode_term body2 envbody  in
                            (match uu____78626 with
                             | (body3,decls') ->
                                 let uu____78637 =
                                   let uu____78646 = codomain_eff rc  in
                                   match uu____78646 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____78665 = encode_term tfun env
                                          in
                                       (match uu____78665 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____78637 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____78699 =
                                          let uu____78710 =
                                            let uu____78711 =
                                              let uu____78716 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____78716, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____78711
                                             in
                                          ([], vars, uu____78710)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t0.FStar_Syntax_Syntax.pos
                                          uu____78699
                                         in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body
                                         in
                                      let uu____78724 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            (cvars, key_body)
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____78740 =
                                              let uu____78743 =
                                                let uu____78754 =
                                                  FStar_SMTEncoding_Term.free_variables
                                                    t1
                                                   in
                                                FStar_List.append uu____78754
                                                  cvars
                                                 in
                                              FStar_Util.remove_dups
                                                FStar_SMTEncoding_Term.fv_eq
                                                uu____78743
                                               in
                                            let uu____78781 =
                                              FStar_SMTEncoding_Util.mkAnd
                                                (key_body, t1)
                                               in
                                            (uu____78740, uu____78781)
                                         in
                                      (match uu____78724 with
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
                                           let uu____78803 =
                                             is_an_eta_expansion env vars
                                               body3
                                              in
                                           (match uu____78803 with
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
                                                  let uu____78819 =
                                                    FStar_Util.digest_of_string
                                                      tkey_hash
                                                     in
                                                  Prims.op_Hat "Tm_abs_"
                                                    uu____78819
                                                   in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None)
                                                   in
                                                let f =
                                                  let uu____78828 =
                                                    let uu____78836 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    (fsym, uu____78836)  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____78828
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
                                                      let uu____78853 =
                                                        let uu____78854 =
                                                          let uu____78862 =
                                                            FStar_SMTEncoding_Term.mkForall
                                                              t0.FStar_Syntax_Syntax.pos
                                                              ([[f]], cvars1,
                                                                f_has_t)
                                                             in
                                                          (uu____78862,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name)
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____78854
                                                         in
                                                      [uu____78853]
                                                   in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.op_Hat
                                                      "interpretation_" fsym
                                                     in
                                                  let uu____78877 =
                                                    let uu____78885 =
                                                      let uu____78886 =
                                                        let uu____78897 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3)
                                                           in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____78897)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        t0.FStar_Syntax_Syntax.pos
                                                        uu____78886
                                                       in
                                                    (uu____78885,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____78877
                                                   in
                                                let f_decls =
                                                  FStar_List.append (fdecl ::
                                                    typing_f) [interp_f]
                                                   in
                                                let uu____78911 =
                                                  let uu____78912 =
                                                    let uu____78915 =
                                                      let uu____78918 =
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
                                                        decls'' uu____78918
                                                       in
                                                    FStar_List.append decls'
                                                      uu____78915
                                                     in
                                                  FStar_List.append decls
                                                    uu____78912
                                                   in
                                                (f, uu____78911))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____78921,{
                           FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                             uu____78922;
                           FStar_Syntax_Syntax.lbunivs = uu____78923;
                           FStar_Syntax_Syntax.lbtyp = uu____78924;
                           FStar_Syntax_Syntax.lbeff = uu____78925;
                           FStar_Syntax_Syntax.lbdef = uu____78926;
                           FStar_Syntax_Syntax.lbattrs = uu____78927;
                           FStar_Syntax_Syntax.lbpos = uu____78928;_}::uu____78929),uu____78930)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____78964;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____78966;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____78968;
                FStar_Syntax_Syntax.lbpos = uu____78969;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____78996 ->
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
              let uu____79068 =
                let uu____79073 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____79073 env  in
              match uu____79068 with
              | (ee1,decls1) ->
                  let uu____79098 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____79098 with
                   | (xs,e21) ->
                       let uu____79123 = FStar_List.hd xs  in
                       (match uu____79123 with
                        | (x1,uu____79141) ->
                            let env' =
                              FStar_SMTEncoding_Env.push_term_var env x1 ee1
                               in
                            let uu____79147 = encode_body e21 env'  in
                            (match uu____79147 with
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
            let uu____79177 =
              let uu____79185 =
                let uu____79186 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____79186  in
              FStar_SMTEncoding_Env.gen_term_var env uu____79185  in
            match uu____79177 with
            | (scrsym,scr',env1) ->
                let uu____79196 = encode_term e env1  in
                (match uu____79196 with
                 | (scr,decls) ->
                     let uu____79207 =
                       let encode_branch b uu____79236 =
                         match uu____79236 with
                         | (else_case,decls1) ->
                             let uu____79255 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____79255 with
                              | (p,w,br) ->
                                  let uu____79281 = encode_pat env1 p  in
                                  (match uu____79281 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____79318  ->
                                                   match uu____79318 with
                                                   | (x,t) ->
                                                       FStar_SMTEncoding_Env.push_term_var
                                                         env2 x t) env1)
                                          in
                                       let uu____79325 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____79347 =
                                               encode_term w1 env2  in
                                             (match uu____79347 with
                                              | (w2,decls2) ->
                                                  let uu____79360 =
                                                    let uu____79361 =
                                                      let uu____79366 =
                                                        let uu____79367 =
                                                          let uu____79372 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____79372)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____79367
                                                         in
                                                      (guard, uu____79366)
                                                       in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____79361
                                                     in
                                                  (uu____79360, decls2))
                                          in
                                       (match uu____79325 with
                                        | (guard1,decls2) ->
                                            let uu____79387 =
                                              encode_br br env2  in
                                            (match uu____79387 with
                                             | (br1,decls3) ->
                                                 let uu____79400 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____79400,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____79207 with
                      | (match_tm,decls1) ->
                          let uu____79421 =
                            let uu____79422 =
                              let uu____79433 =
                                let uu____79440 =
                                  let uu____79445 =
                                    FStar_SMTEncoding_Term.mk_fv
                                      (scrsym,
                                        FStar_SMTEncoding_Term.Term_sort)
                                     in
                                  (uu____79445, scr)  in
                                [uu____79440]  in
                              (uu____79433, match_tm)  in
                            FStar_SMTEncoding_Term.mkLet' uu____79422
                              FStar_Range.dummyRange
                             in
                          (uu____79421, decls1)))

and (encode_pat :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.pat -> (FStar_SMTEncoding_Env.env_t * pattern))
  =
  fun env  ->
    fun pat  ->
      (let uu____79468 =
         FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
           FStar_Options.Medium
          in
       if uu____79468
       then
         let uu____79471 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____79471
       else ());
      (let uu____79476 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____79476 with
       | (vars,pat_term) ->
           let uu____79493 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____79535  ->
                     fun v1  ->
                       match uu____79535 with
                       | (env1,vars1) ->
                           let uu____79571 =
                             FStar_SMTEncoding_Env.gen_term_var env1 v1  in
                           (match uu____79571 with
                            | (xx,uu____79590,env2) ->
                                let uu____79594 =
                                  let uu____79601 =
                                    let uu____79606 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xx,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    (v1, uu____79606)  in
                                  uu____79601 :: vars1  in
                                (env2, uu____79594))) (env, []))
              in
           (match uu____79493 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____79661 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____79662 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____79663 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____79671 = encode_const c env1  in
                      (match uu____79671 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____79679::uu____79680 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____79684 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon
                            env1.FStar_SMTEncoding_Env.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____79707 =
                          FStar_TypeChecker_Env.datacons_of_typ
                            env1.FStar_SMTEncoding_Env.tcenv tc_name
                           in
                        match uu____79707 with
                        | (uu____79715,uu____79716::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____79721 ->
                            FStar_SMTEncoding_Env.mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____79757  ->
                                  match uu____79757 with
                                  | (arg,uu____79767) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____79776 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____79776))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____79808) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____79839 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____79864 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____79910  ->
                                  match uu____79910 with
                                  | (arg,uu____79926) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____79935 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____79935))
                         in
                      FStar_All.pipe_right uu____79864 FStar_List.flatten
                   in
                let pat_term1 uu____79966 = encode_term pat_term env1  in
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
      let uu____79976 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____80024  ->
                fun uu____80025  ->
                  match (uu____80024, uu____80025) with
                  | ((tms,decls),(t,uu____80065)) ->
                      let uu____80092 = encode_term t env  in
                      (match uu____80092 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____79976 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____80149 = FStar_Syntax_Util.list_elements e  in
        match uu____80149 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____80180 =
          let uu____80197 = FStar_Syntax_Util.unmeta p  in
          FStar_All.pipe_right uu____80197 FStar_Syntax_Util.head_and_args
           in
        match uu____80180 with
        | (head1,args) ->
            let uu____80248 =
              let uu____80263 =
                let uu____80264 = FStar_Syntax_Util.un_uinst head1  in
                uu____80264.FStar_Syntax_Syntax.n  in
              (uu____80263, args)  in
            (match uu____80248 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____80286,uu____80287)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____80339 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or1 t1 =
          let uu____80394 =
            let uu____80411 = FStar_Syntax_Util.unmeta t1  in
            FStar_All.pipe_right uu____80411 FStar_Syntax_Util.head_and_args
             in
          match uu____80394 with
          | (head1,args) ->
              let uu____80458 =
                let uu____80473 =
                  let uu____80474 = FStar_Syntax_Util.un_uinst head1  in
                  uu____80474.FStar_Syntax_Syntax.n  in
                (uu____80473, args)  in
              (match uu____80458 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____80493)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____80530 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____80560 = smt_pat_or1 t1  in
            (match uu____80560 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____80582 = list_elements1 e  in
                 FStar_All.pipe_right uu____80582
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____80612 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____80612
                           (FStar_List.map one_pat)))
             | uu____80635 ->
                 let uu____80640 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____80640])
        | uu____80691 ->
            let uu____80694 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____80694]
         in
      let uu____80745 =
        let uu____80760 =
          let uu____80761 = FStar_Syntax_Subst.compress t  in
          uu____80761.FStar_Syntax_Syntax.n  in
        match uu____80760 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____80800 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____80800 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____80835;
                        FStar_Syntax_Syntax.effect_name = uu____80836;
                        FStar_Syntax_Syntax.result_typ = uu____80837;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____80839)::(post,uu____80841)::(pats,uu____80843)::[];
                        FStar_Syntax_Syntax.flags = uu____80844;_}
                      ->
                      let uu____80905 = lemma_pats pats  in
                      (binders1, pre, post, uu____80905)
                  | uu____80916 -> failwith "impos"))
        | uu____80932 -> failwith "Impos"  in
      match uu____80745 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___1940_80969 = env  in
            {
              FStar_SMTEncoding_Env.bvar_bindings =
                (uu___1940_80969.FStar_SMTEncoding_Env.bvar_bindings);
              FStar_SMTEncoding_Env.fvar_bindings =
                (uu___1940_80969.FStar_SMTEncoding_Env.fvar_bindings);
              FStar_SMTEncoding_Env.depth =
                (uu___1940_80969.FStar_SMTEncoding_Env.depth);
              FStar_SMTEncoding_Env.tcenv =
                (uu___1940_80969.FStar_SMTEncoding_Env.tcenv);
              FStar_SMTEncoding_Env.warn =
                (uu___1940_80969.FStar_SMTEncoding_Env.warn);
              FStar_SMTEncoding_Env.nolabels =
                (uu___1940_80969.FStar_SMTEncoding_Env.nolabels);
              FStar_SMTEncoding_Env.use_zfuel_name = true;
              FStar_SMTEncoding_Env.encode_non_total_function_typ =
                (uu___1940_80969.FStar_SMTEncoding_Env.encode_non_total_function_typ);
              FStar_SMTEncoding_Env.current_module_name =
                (uu___1940_80969.FStar_SMTEncoding_Env.current_module_name);
              FStar_SMTEncoding_Env.encoding_quantifier =
                (uu___1940_80969.FStar_SMTEncoding_Env.encoding_quantifier);
              FStar_SMTEncoding_Env.global_cache =
                (uu___1940_80969.FStar_SMTEncoding_Env.global_cache)
            }  in
          let uu____80971 =
            encode_binders FStar_Pervasives_Native.None binders env1  in
          (match uu____80971 with
           | (vars,guards,env2,decls,uu____80996) ->
               let uu____81009 = encode_smt_patterns patterns env2  in
               (match uu____81009 with
                | (pats,decls') ->
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
                    let env3 =
                      let uu___1953_81036 = env2  in
                      {
                        FStar_SMTEncoding_Env.bvar_bindings =
                          (uu___1953_81036.FStar_SMTEncoding_Env.bvar_bindings);
                        FStar_SMTEncoding_Env.fvar_bindings =
                          (uu___1953_81036.FStar_SMTEncoding_Env.fvar_bindings);
                        FStar_SMTEncoding_Env.depth =
                          (uu___1953_81036.FStar_SMTEncoding_Env.depth);
                        FStar_SMTEncoding_Env.tcenv =
                          (uu___1953_81036.FStar_SMTEncoding_Env.tcenv);
                        FStar_SMTEncoding_Env.warn =
                          (uu___1953_81036.FStar_SMTEncoding_Env.warn);
                        FStar_SMTEncoding_Env.nolabels = true;
                        FStar_SMTEncoding_Env.use_zfuel_name =
                          (uu___1953_81036.FStar_SMTEncoding_Env.use_zfuel_name);
                        FStar_SMTEncoding_Env.encode_non_total_function_typ =
                          (uu___1953_81036.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                        FStar_SMTEncoding_Env.current_module_name =
                          (uu___1953_81036.FStar_SMTEncoding_Env.current_module_name);
                        FStar_SMTEncoding_Env.encoding_quantifier =
                          (uu___1953_81036.FStar_SMTEncoding_Env.encoding_quantifier);
                        FStar_SMTEncoding_Env.global_cache =
                          (uu___1953_81036.FStar_SMTEncoding_Env.global_cache)
                      }  in
                    let uu____81038 =
                      let uu____81043 = FStar_Syntax_Util.unmeta pre  in
                      encode_formula uu____81043 env3  in
                    (match uu____81038 with
                     | (pre1,decls'') ->
                         let uu____81050 =
                           let uu____81055 = FStar_Syntax_Util.unmeta post1
                              in
                           encode_formula uu____81055 env3  in
                         (match uu____81050 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append decls'
                                     (FStar_List.append decls'' decls'''))
                                 in
                              let uu____81065 =
                                let uu____81066 =
                                  let uu____81077 =
                                    let uu____81078 =
                                      let uu____81083 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards)
                                         in
                                      (uu____81083, post2)  in
                                    FStar_SMTEncoding_Util.mkImp uu____81078
                                     in
                                  (pats, vars, uu____81077)  in
                                FStar_SMTEncoding_Term.mkForall
                                  t.FStar_Syntax_Syntax.pos uu____81066
                                 in
                              (uu____81065, decls1)))))

and (encode_smt_patterns :
  FStar_Syntax_Syntax.arg Prims.list Prims.list ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term Prims.list Prims.list *
        FStar_SMTEncoding_Term.decls_t))
  =
  fun pats_l  ->
    fun env  ->
      let env1 =
        let uu___1965_81103 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___1965_81103.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___1965_81103.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___1965_81103.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___1965_81103.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___1965_81103.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___1965_81103.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___1965_81103.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___1965_81103.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___1965_81103.FStar_SMTEncoding_Env.encoding_quantifier);
          FStar_SMTEncoding_Env.global_cache =
            (uu___1965_81103.FStar_SMTEncoding_Env.global_cache)
        }  in
      let encode_smt_pattern t =
        let uu____81119 = FStar_Syntax_Util.head_and_args t  in
        match uu____81119 with
        | (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____81182::(x,uu____81184)::(t1,uu____81186)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____81253 = encode_term x env1  in
                 (match uu____81253 with
                  | (x1,decls) ->
                      let uu____81264 = encode_term t1 env1  in
                      (match uu____81264 with
                       | (t2,decls') ->
                           let uu____81275 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                           (uu____81275, (FStar_List.append decls decls'))))
             | uu____81276 -> encode_term t env1)
         in
      FStar_List.fold_right
        (fun pats  ->
           fun uu____81319  ->
             match uu____81319 with
             | (pats_l1,decls) ->
                 let uu____81364 =
                   FStar_List.fold_right
                     (fun uu____81399  ->
                        fun uu____81400  ->
                          match (uu____81399, uu____81400) with
                          | ((p,uu____81442),(pats1,decls1)) ->
                              let uu____81477 = encode_smt_pattern p  in
                              (match uu____81477 with
                               | (t,d) ->
                                   let uu____81492 =
                                     FStar_SMTEncoding_Term.check_pattern_ok
                                       t
                                      in
                                   (match uu____81492 with
                                    | FStar_Pervasives_Native.None  ->
                                        ((t :: pats1),
                                          (FStar_List.append d decls1))
                                    | FStar_Pervasives_Native.Some
                                        illegal_subterm ->
                                        ((let uu____81509 =
                                            let uu____81515 =
                                              let uu____81517 =
                                                FStar_Syntax_Print.term_to_string
                                                  p
                                                 in
                                              let uu____81519 =
                                                FStar_SMTEncoding_Term.print_smt_term
                                                  illegal_subterm
                                                 in
                                              FStar_Util.format2
                                                "Pattern %s contains illegal sub-term (%s); dropping it"
                                                uu____81517 uu____81519
                                               in
                                            (FStar_Errors.Warning_SMTPatternIllFormed,
                                              uu____81515)
                                             in
                                          FStar_Errors.log_issue
                                            p.FStar_Syntax_Syntax.pos
                                            uu____81509);
                                         (pats1,
                                           (FStar_List.append d decls1))))))
                     pats ([], decls)
                    in
                 (match uu____81364 with
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
        let uu____81579 =
          FStar_All.pipe_left
            (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____81579
        then
          let uu____81584 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____81586 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____81584 uu____81586
        else ()  in
      let enc f r l =
        let uu____81628 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____81660 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____81660 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____81628 with
        | (decls,args) ->
            let uu____81691 =
              let uu___2029_81692 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___2029_81692.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___2029_81692.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____81691, decls)
         in
      let const_op f r uu____81727 =
        let uu____81740 = f r  in (uu____81740, [])  in
      let un_op f l =
        let uu____81763 = FStar_List.hd l  in
        FStar_All.pipe_left f uu____81763  in
      let bin_op f uu___632_81783 =
        match uu___632_81783 with
        | t1::t2::[] -> f (t1, t2)
        | uu____81794 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____81835 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____81860  ->
                 match uu____81860 with
                 | (t,uu____81876) ->
                     let uu____81881 = encode_formula t env  in
                     (match uu____81881 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____81835 with
        | (decls,phis) ->
            let uu____81910 =
              let uu___2059_81911 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___2059_81911.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___2059_81911.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____81910, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____81974  ->
               match uu____81974 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____81995) -> false
                    | uu____81998 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____82017 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____82017
        else
          (let uu____82034 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____82034 r rf)
         in
      let eq3_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____82106 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::t1::v0::v1::[] ->
                     let uu____82138 =
                       let uu____82143 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____82144 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____82143, uu____82144)  in
                     FStar_SMTEncoding_Util.mkAnd uu____82138
                 | uu____82145 -> failwith "Impossible")
             in
          uu____82106 r args
        else
          (let uu____82151 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____82151)
         in
      let h_equals_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____82223 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::v0::t1::v1::[] ->
                     let uu____82255 =
                       let uu____82260 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____82261 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____82260, uu____82261)  in
                     FStar_SMTEncoding_Util.mkAnd uu____82255
                 | uu____82262 -> failwith "Impossible")
             in
          uu____82223 r args
        else
          (let uu____82268 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____82268)
         in
      let mk_imp1 r uu___633_82303 =
        match uu___633_82303 with
        | (lhs,uu____82309)::(rhs,uu____82311)::[] ->
            let uu____82352 = encode_formula rhs env  in
            (match uu____82352 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____82367) ->
                      (l1, decls1)
                  | uu____82372 ->
                      let uu____82373 = encode_formula lhs env  in
                      (match uu____82373 with
                       | (l2,decls2) ->
                           let uu____82384 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____82384, (FStar_List.append decls1 decls2)))))
        | uu____82385 -> failwith "impossible"  in
      let mk_ite r uu___634_82413 =
        match uu___634_82413 with
        | (guard,uu____82419)::(_then,uu____82421)::(_else,uu____82423)::[]
            ->
            let uu____82480 = encode_formula guard env  in
            (match uu____82480 with
             | (g,decls1) ->
                 let uu____82491 = encode_formula _then env  in
                 (match uu____82491 with
                  | (t,decls2) ->
                      let uu____82502 = encode_formula _else env  in
                      (match uu____82502 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____82514 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____82544 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l
           in
        f uu____82544  in
      let connectives =
        let uu____82574 =
          let uu____82599 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____82599)  in
        let uu____82642 =
          let uu____82669 =
            let uu____82694 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____82694)  in
          let uu____82737 =
            let uu____82764 =
              let uu____82791 =
                let uu____82816 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____82816)  in
              let uu____82859 =
                let uu____82886 =
                  let uu____82913 =
                    let uu____82938 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____82938)  in
                  [uu____82913;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.c_eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq3_op);
                  (FStar_Parser_Const.c_eq3_lid, h_equals_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____82886  in
              uu____82791 :: uu____82859  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____82764  in
          uu____82669 :: uu____82737  in
        uu____82574 :: uu____82642  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____83483 = encode_formula phi' env  in
            (match uu____83483 with
             | (phi2,decls) ->
                 let uu____83494 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____83494, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____83496 ->
            let uu____83503 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____83503 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____83542 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____83542 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____83554;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____83556;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____83558;
                 FStar_Syntax_Syntax.lbpos = uu____83559;_}::[]),e2)
            ->
            let uu____83586 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____83586 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____83639::(x,uu____83641)::(t,uu____83643)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____83710 = encode_term x env  in
                 (match uu____83710 with
                  | (x1,decls) ->
                      let uu____83721 = encode_term t env  in
                      (match uu____83721 with
                       | (t1,decls') ->
                           let uu____83732 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____83732, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____83735)::(msg,uu____83737)::(phi2,uu____83739)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____83806 =
                   let uu____83811 =
                     let uu____83812 = FStar_Syntax_Subst.compress r  in
                     uu____83812.FStar_Syntax_Syntax.n  in
                   let uu____83815 =
                     let uu____83816 = FStar_Syntax_Subst.compress msg  in
                     uu____83816.FStar_Syntax_Syntax.n  in
                   (uu____83811, uu____83815)  in
                 (match uu____83806 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____83825))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____83836 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____83843)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____83878 when head_redex env head2 ->
                 let uu____83893 = whnf env phi1  in
                 encode_formula uu____83893 env
             | uu____83894 ->
                 let uu____83909 = encode_term phi1 env  in
                 (match uu____83909 with
                  | (tt,decls) ->
                      let tt1 =
                        let uu____83921 =
                          let uu____83923 =
                            FStar_Range.use_range
                              tt.FStar_SMTEncoding_Term.rng
                             in
                          let uu____83924 =
                            FStar_Range.use_range
                              phi1.FStar_Syntax_Syntax.pos
                             in
                          FStar_Range.rng_included uu____83923 uu____83924
                           in
                        if uu____83921
                        then tt
                        else
                          (let uu___2246_83928 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___2246_83928.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___2246_83928.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      let uu____83929 = FStar_SMTEncoding_Term.mk_Valid tt1
                         in
                      (uu____83929, decls)))
        | uu____83930 ->
            let uu____83931 = encode_term phi1 env  in
            (match uu____83931 with
             | (tt,decls) ->
                 let tt1 =
                   let uu____83943 =
                     let uu____83945 =
                       FStar_Range.use_range tt.FStar_SMTEncoding_Term.rng
                        in
                     let uu____83946 =
                       FStar_Range.use_range phi1.FStar_Syntax_Syntax.pos  in
                     FStar_Range.rng_included uu____83945 uu____83946  in
                   if uu____83943
                   then tt
                   else
                     (let uu___2254_83950 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___2254_83950.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___2254_83950.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 let uu____83951 = FStar_SMTEncoding_Term.mk_Valid tt1  in
                 (uu____83951, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____83995 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____83995 with
        | (vars,guards,env2,decls,uu____84034) ->
            let uu____84047 = encode_smt_patterns ps env2  in
            (match uu____84047 with
             | (pats,decls') ->
                 let uu____84084 = encode_formula body env2  in
                 (match uu____84084 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____84116;
                             FStar_SMTEncoding_Term.rng = uu____84117;_}::[])::[]
                            when
                            let uu____84137 =
                              FStar_Ident.text_of_lid
                                FStar_Parser_Const.guard_free
                               in
                            uu____84137 = gf -> []
                        | uu____84140 -> guards  in
                      let uu____84145 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____84145, body1,
                        (FStar_List.append decls
                           (FStar_List.append decls' decls'')))))
         in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi  in
       let uu____84156 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____84156 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____84165 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____84271  ->
                     match uu____84271 with
                     | (l,uu____84296) -> FStar_Ident.lid_equals op l))
              in
           (match uu____84165 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____84365,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____84457 = encode_q_body env vars pats body  in
             match uu____84457 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____84502 =
                     let uu____84513 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____84513)  in
                   FStar_SMTEncoding_Term.mkForall
                     phi1.FStar_Syntax_Syntax.pos uu____84502
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____84544 = encode_q_body env vars pats body  in
             match uu____84544 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____84588 =
                   let uu____84589 =
                     let uu____84600 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____84600)  in
                   FStar_SMTEncoding_Term.mkExists
                     phi1.FStar_Syntax_Syntax.pos uu____84589
                    in
                 (uu____84588, decls))))
