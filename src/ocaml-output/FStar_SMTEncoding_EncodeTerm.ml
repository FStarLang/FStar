open Prims
let mkForall_fuel' :
  'Auu____66273 .
    Prims.string ->
      FStar_Range.range ->
        'Auu____66273 ->
          (FStar_SMTEncoding_Term.pat Prims.list Prims.list *
            FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term) ->
            FStar_SMTEncoding_Term.term
  =
  fun mname  ->
    fun r  ->
      fun n1  ->
        fun uu____66304  ->
          match uu____66304 with
          | (pats,vars,body) ->
              let fallback uu____66332 =
                FStar_SMTEncoding_Term.mkForall r (pats, vars, body)  in
              let uu____66337 = FStar_Options.unthrottle_inductives ()  in
              if uu____66337
              then fallback ()
              else
                (let uu____66342 =
                   FStar_SMTEncoding_Env.fresh_fvar mname "f"
                     FStar_SMTEncoding_Term.Fuel_sort
                    in
                 match uu____66342 with
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
                               | uu____66382 -> p))
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
                                 let uu____66403 = add_fuel1 guards  in
                                 FStar_SMTEncoding_Util.mk_and_l uu____66403
                             | uu____66406 ->
                                 let uu____66407 = add_fuel1 [guard]  in
                                 FStar_All.pipe_right uu____66407
                                   FStar_List.hd
                              in
                           FStar_SMTEncoding_Util.mkImp (guard1, body')
                       | uu____66412 -> body  in
                     let vars1 =
                       let uu____66424 =
                         FStar_SMTEncoding_Term.mk_fv
                           (fsym, FStar_SMTEncoding_Term.Fuel_sort)
                          in
                       uu____66424 :: vars  in
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
      | FStar_Syntax_Syntax.Tm_arrow uu____66488 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____66504 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____66512 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____66514 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____66528 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____66548 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____66551 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____66551 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____66570;
             FStar_Syntax_Syntax.vars = uu____66571;_},uu____66572)
          ->
          let uu____66597 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____66597 FStar_Option.isNone
      | uu____66615 -> false
  
let (head_redex :
  FStar_SMTEncoding_Env.env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____66629 =
        let uu____66630 = FStar_Syntax_Util.un_uinst t  in
        uu____66630.FStar_Syntax_Syntax.n  in
      match uu____66629 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____66634,uu____66635,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___630_66660  ->
                  match uu___630_66660 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____66663 -> false)
               rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____66666 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____66666 FStar_Option.isSome
      | uu____66684 -> false
  
let (whnf :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____66697 = head_normal env t  in
      if uu____66697
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
    let uu____66719 =
      let uu____66720 = FStar_Syntax_Syntax.null_binder t  in [uu____66720]
       in
    let uu____66739 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    FStar_Syntax_Util.abs uu____66719 uu____66739
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
                let uu____66761 = FStar_SMTEncoding_Term.fv_sort var  in
                match uu____66761 with
                | FStar_SMTEncoding_Term.Fuel_sort  ->
                    let uu____66762 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____66762
                | s ->
                    let uu____66765 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____66765) e)
  
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
          let uu____66821 =
            let uu____66827 =
              let uu____66829 = FStar_Util.string_of_int arity  in
              let uu____66831 = FStar_Util.string_of_int n_args  in
              FStar_Util.format3
                "Head symbol %s expects at least %s arguments; got only %s"
                head1 uu____66829 uu____66831
               in
            (FStar_Errors.Fatal_SMTEncodingArityMismatch, uu____66827)  in
          FStar_Errors.raise_error uu____66821 rng
  
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
                  (let uu____66880 = FStar_Util.first_N arity args  in
                   match uu____66880 with
                   | (args1,rest) ->
                       let head3 =
                         FStar_SMTEncoding_Util.mkApp' (head2, args1)  in
                       mk_Apply_args head3 rest)
                else
                  (let uu____66904 =
                     FStar_SMTEncoding_Term.op_to_string head2  in
                   raise_arity_mismatch uu____66904 arity n_args rng)
  
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
          let uu____66927 = FStar_SMTEncoding_Env.force_thunk fvb  in
          mk_Apply_args uu____66927 args
        else
          maybe_curry_app rng
            (FStar_Util.Inl
               (FStar_SMTEncoding_Term.Var (fvb.FStar_SMTEncoding_Env.smt_id)))
            fvb.FStar_SMTEncoding_Env.smt_arity args
  
let (is_app : FStar_SMTEncoding_Term.op -> Prims.bool) =
  fun uu___631_66936  ->
    match uu___631_66936 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____66942 -> false
  
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
                       FStar_SMTEncoding_Term.freevars = uu____66990;
                       FStar_SMTEncoding_Term.rng = uu____66991;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____67022) ->
              let uu____67032 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____67049 -> false) args (FStar_List.rev xs))
                 in
              if uu____67032
              then FStar_SMTEncoding_Env.tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____67056,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t  in
              let uu____67060 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____67068 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars
                           in
                        Prims.op_Negation uu____67068))
                 in
              if uu____67060
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____67075 -> FStar_Pervasives_Native.None  in
        check_partial_applications body (FStar_List.rev vars)
  
let check_pattern_vars :
  'Auu____67093 'Auu____67094 .
    FStar_SMTEncoding_Env.env_t ->
      (FStar_Syntax_Syntax.bv * 'Auu____67093) Prims.list ->
        (FStar_Syntax_Syntax.term * 'Auu____67094) Prims.list -> unit
  =
  fun env  ->
    fun vars  ->
      fun pats  ->
        let pats1 =
          FStar_All.pipe_right pats
            (FStar_List.map
               (fun uu____67152  ->
                  match uu____67152 with
                  | (x,uu____67158) ->
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
              let uu____67166 = FStar_Syntax_Free.names hd1  in
              FStar_List.fold_left
                (fun out  ->
                   fun x  ->
                     let uu____67178 = FStar_Syntax_Free.names x  in
                     FStar_Util.set_union out uu____67178) uu____67166 tl1
               in
            let uu____67181 =
              FStar_All.pipe_right vars
                (FStar_Util.find_opt
                   (fun uu____67208  ->
                      match uu____67208 with
                      | (b,uu____67215) ->
                          let uu____67216 = FStar_Util.set_mem b pat_vars  in
                          Prims.op_Negation uu____67216))
               in
            (match uu____67181 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some (x,uu____67223) ->
                 let pos =
                   FStar_List.fold_left
                     (fun out  ->
                        fun t  ->
                          FStar_Range.union_ranges out
                            t.FStar_Syntax_Syntax.pos)
                     hd1.FStar_Syntax_Syntax.pos tl1
                    in
                 let uu____67237 =
                   let uu____67243 =
                     let uu____67245 = FStar_Syntax_Print.bv_to_string x  in
                     FStar_Util.format1
                       "SMT pattern misses at least one bound variable: %s"
                       uu____67245
                      in
                   (FStar_Errors.Warning_SMTPatternIllFormed, uu____67243)
                    in
                 FStar_Errors.log_issue pos uu____67237)
  
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
        | FStar_Syntax_Syntax.Tm_arrow uu____67531 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____67546 ->
            let uu____67553 = FStar_Syntax_Util.unrefine t1  in
            aux true uu____67553
        | uu____67555 ->
            if norm1
            then let uu____67557 = whnf env t1  in aux false uu____67557
            else
              (let uu____67561 =
                 let uu____67563 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let uu____67565 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____67563 uu____67565
                  in
               failwith uu____67561)
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
    | FStar_Syntax_Syntax.Tm_refine (bv,uu____67607) ->
        let uu____67612 =
          curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort  in
        (match uu____67612 with
         | (args,res) ->
             (match args with
              | [] ->
                  let uu____67633 = FStar_Syntax_Syntax.mk_Total k1  in
                  ([], uu____67633)
              | uu____67640 -> (args, res)))
    | uu____67641 ->
        let uu____67642 = FStar_Syntax_Syntax.mk_Total k1  in
        ([], uu____67642)
  
let is_arithmetic_primitive :
  'Auu____67656 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____67656 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____67679::uu____67680::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____67684::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____67687 -> false
  
let (isInteger : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____67718 -> false
  
let (getInteger : FStar_Syntax_Syntax.term' -> Prims.int) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____67741 -> failwith "Expected an Integer term"
  
let is_BitVector_primitive :
  'Auu____67751 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____67751)
        Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____67793)::uu____67794::uu____67795::[]) ->
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
         fv,(sz_arg,uu____67846)::uu____67847::[]) ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____67884 -> false
  
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
          let uu____68208 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue  in
          (uu____68208, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____68210 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse  in
          (uu____68210, [])
      | FStar_Const.Const_char c1 ->
          let uu____68213 =
            let uu____68214 =
              let uu____68222 =
                let uu____68225 =
                  let uu____68226 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1)
                     in
                  FStar_SMTEncoding_Term.boxInt uu____68226  in
                [uu____68225]  in
              ("FStar.Char.__char_of_int", uu____68222)  in
            FStar_SMTEncoding_Util.mkApp uu____68214  in
          (uu____68213, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____68244 =
            let uu____68245 = FStar_SMTEncoding_Util.mkInteger i  in
            FStar_SMTEncoding_Term.boxInt uu____68245  in
          (uu____68244, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.FStar_SMTEncoding_Env.tcenv).FStar_TypeChecker_Env.dsenv
              repr sw FStar_Range.dummyRange
             in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____68266) ->
          let uu____68269 =
            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.string_const s
             in
          (uu____68269, [])
      | FStar_Const.Const_range uu____68270 ->
          let uu____68271 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          (uu____68271, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | FStar_Const.Const_real r ->
          let uu____68274 =
            let uu____68275 = FStar_SMTEncoding_Util.mkReal r  in
            FStar_SMTEncoding_Term.boxReal uu____68275  in
          (uu____68274, [])
      | c1 ->
          let uu____68277 =
            let uu____68279 = FStar_Syntax_Print.const_to_string c1  in
            FStar_Util.format1 "Unhandled constant: %s" uu____68279  in
          failwith uu____68277

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
        (let uu____68308 =
           FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
             FStar_Options.Medium
            in
         if uu____68308
         then
           let uu____68311 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____68311
         else ());
        (let uu____68317 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____68399  ->
                   fun b  ->
                     match uu____68399 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____68464 =
                           let x = FStar_Pervasives_Native.fst b  in
                           let uu____68480 =
                             FStar_SMTEncoding_Env.gen_term_var env1 x  in
                           match uu____68480 with
                           | (xxsym,xx,env') ->
                               let uu____68505 =
                                 let uu____68510 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____68510 env1
                                   xx
                                  in
                               (match uu____68505 with
                                | (guard_x_t,decls') ->
                                    let uu____68525 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xxsym,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    (uu____68525, guard_x_t, env', decls', x))
                            in
                         (match uu____68464 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____68317 with
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
          let uu____68625 = encode_term t env  in
          match uu____68625 with
          | (t1,decls) ->
              let uu____68636 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____68636, decls)

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
          let uu____68647 = encode_term t env  in
          match uu____68647 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____68662 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____68662, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____68664 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____68664, decls))

and (encode_arith_term :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____68670 = encode_args args_e env  in
        match uu____68670 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____68689 -> failwith "Impossible"  in
            let unary unbox arg_tms1 =
              let uu____68711 = FStar_List.hd arg_tms1  in unbox uu____68711
               in
            let binary unbox arg_tms1 =
              let uu____68736 =
                let uu____68737 = FStar_List.hd arg_tms1  in
                unbox uu____68737  in
              let uu____68738 =
                let uu____68739 =
                  let uu____68740 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____68740  in
                unbox uu____68739  in
              (uu____68736, uu____68738)  in
            let mk_default uu____68748 =
              let uu____68749 =
                FStar_SMTEncoding_Env.lookup_free_var_sym env
                  head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____68749 with
              | (fname,fuel_args,arity) ->
                  let args = FStar_List.append fuel_args arg_tms  in
                  maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity
                    args
               in
            let mk_l box op mk_args ts =
              let uu____68838 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____68838
              then
                let uu____68841 =
                  let uu____68842 = mk_args ts  in op uu____68842  in
                FStar_All.pipe_right uu____68841 box
              else mk_default ()  in
            let mk_nl box unbox nm op ts =
              let uu____68900 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____68900
              then
                let uu____68903 = binary unbox ts  in
                match uu____68903 with
                | (t1,t2) ->
                    let uu____68910 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____68910 box
              else
                (let uu____68916 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____68916
                 then
                   let uu____68919 =
                     let uu____68920 = binary unbox ts  in op uu____68920  in
                   FStar_All.pipe_right uu____68919 box
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
            let uu____69355 =
              let uu____69365 =
                FStar_List.tryFind
                  (fun uu____69389  ->
                     match uu____69389 with
                     | (l,uu____69400) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____69365 FStar_Util.must  in
            (match uu____69355 with
             | (uu____69444,op) ->
                 let uu____69456 = op arg_tms  in (uu____69456, decls))

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
        let uu____69472 = FStar_List.hd args_e  in
        match uu____69472 with
        | (tm_sz,uu____69488) ->
            let uu____69497 = uu____69472  in
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let t_decls1 = FStar_SMTEncoding_Term.mkBvConstructor sz  in
              FStar_SMTEncoding_Term.mk_decls "" sz_key t_decls1 []  in
            let uu____69508 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____69534::(sz_arg,uu____69536)::uu____69537::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____69604 =
                    let uu____69605 = FStar_List.tail args_e  in
                    FStar_List.tail uu____69605  in
                  let uu____69632 =
                    let uu____69636 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____69636  in
                  (uu____69604, uu____69632)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____69643::(sz_arg,uu____69645)::uu____69646::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____69713 =
                    let uu____69715 =
                      FStar_Syntax_Print.term_to_string sz_arg  in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____69715
                     in
                  failwith uu____69713
              | uu____69725 ->
                  let uu____69740 = FStar_List.tail args_e  in
                  (uu____69740, FStar_Pervasives_Native.None)
               in
            (match uu____69508 with
             | (arg_tms,ext_sz) ->
                 let uu____69767 = encode_args arg_tms env  in
                 (match uu____69767 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____69788 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____69800 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____69800  in
                      let unary_arith arg_tms2 =
                        let uu____69811 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____69811  in
                      let binary arg_tms2 =
                        let uu____69826 =
                          let uu____69827 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____69827
                           in
                        let uu____69828 =
                          let uu____69829 =
                            let uu____69830 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____69830  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____69829
                           in
                        (uu____69826, uu____69828)  in
                      let binary_arith arg_tms2 =
                        let uu____69847 =
                          let uu____69848 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____69848
                           in
                        let uu____69849 =
                          let uu____69850 =
                            let uu____69851 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____69851  in
                          FStar_SMTEncoding_Term.unboxInt uu____69850  in
                        (uu____69847, uu____69849)  in
                      let mk_bv op mk_args resBox ts =
                        let uu____69909 =
                          let uu____69910 = mk_args ts  in op uu____69910  in
                        FStar_All.pipe_right uu____69909 resBox  in
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
                        let uu____70042 =
                          let uu____70047 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____70047  in
                        let uu____70056 =
                          let uu____70061 =
                            let uu____70063 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____70063  in
                          FStar_SMTEncoding_Term.boxBitVec uu____70061  in
                        mk_bv uu____70042 unary uu____70056 arg_tms2  in
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
                      let uu____70303 =
                        let uu____70313 =
                          FStar_List.tryFind
                            (fun uu____70337  ->
                               match uu____70337 with
                               | (l,uu____70348) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____70313 FStar_Util.must  in
                      (match uu____70303 with
                       | (uu____70394,op) ->
                           let uu____70406 = op arg_tms1  in
                           (uu____70406, (FStar_List.append sz_decls decls)))))

and (encode_deeply_embedded_quantifier :
  FStar_Syntax_Syntax.term ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let env1 =
        let uu___1170_70416 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___1170_70416.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___1170_70416.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___1170_70416.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___1170_70416.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___1170_70416.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___1170_70416.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name =
            (uu___1170_70416.FStar_SMTEncoding_Env.use_zfuel_name);
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___1170_70416.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___1170_70416.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier = true;
          FStar_SMTEncoding_Env.global_cache =
            (uu___1170_70416.FStar_SMTEncoding_Env.global_cache)
        }  in
      let uu____70418 = encode_term t env1  in
      match uu____70418 with
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
               (uu____70444,{
                              FStar_SMTEncoding_Term.tm =
                                FStar_SMTEncoding_Term.FreeV uu____70445;
                              FStar_SMTEncoding_Term.freevars = uu____70446;
                              FStar_SMTEncoding_Term.rng = uu____70447;_}::
                {
                  FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV
                    uu____70448;
                  FStar_SMTEncoding_Term.freevars = uu____70449;
                  FStar_SMTEncoding_Term.rng = uu____70450;_}::[])
               ->
               (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                  (FStar_Errors.Warning_QuantifierWithoutPattern,
                    "Not encoding deeply embedded, unguarded quantifier to SMT");
                (tm, decls))
           | uu____70496 ->
               let uu____70497 = encode_formula t env1  in
               (match uu____70497 with
                | (phi,decls') ->
                    let interp =
                      match vars with
                      | [] ->
                          let uu____70517 =
                            let uu____70522 =
                              FStar_SMTEncoding_Term.mk_Valid tm  in
                            (uu____70522, phi)  in
                          FStar_SMTEncoding_Util.mkIff uu____70517
                      | uu____70523 ->
                          let uu____70524 =
                            let uu____70535 =
                              let uu____70536 =
                                let uu____70541 =
                                  FStar_SMTEncoding_Term.mk_Valid tm  in
                                (uu____70541, phi)  in
                              FStar_SMTEncoding_Util.mkIff uu____70536  in
                            ([[valid_tm]], vars, uu____70535)  in
                          FStar_SMTEncoding_Term.mkForall
                            t.FStar_Syntax_Syntax.pos uu____70524
                       in
                    let ax =
                      let uu____70551 =
                        let uu____70559 =
                          let uu____70561 =
                            FStar_Util.digest_of_string tkey_hash  in
                          Prims.op_Hat "l_quant_interp_" uu____70561  in
                        (interp,
                          (FStar_Pervasives_Native.Some
                             "Interpretation of deeply embedded quantifier"),
                          uu____70559)
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____70551  in
                    let uu____70567 =
                      let uu____70568 =
                        let uu____70571 =
                          FStar_SMTEncoding_Term.mk_decls "" tkey_hash 
                            [ax] (FStar_List.append decls decls')
                           in
                        FStar_List.append decls' uu____70571  in
                      FStar_List.append decls uu____70568  in
                    (tm, uu____70567)))

and (encode_term :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____70583 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____70583
       then
         let uu____70588 = FStar_Syntax_Print.tag_of_term t  in
         let uu____70590 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____70592 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____70588 uu____70590
           uu____70592
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____70601 ->
           let uu____70624 =
             let uu____70626 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____70629 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____70631 = FStar_Syntax_Print.term_to_string t0  in
             let uu____70633 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____70626
               uu____70629 uu____70631 uu____70633
              in
           failwith uu____70624
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____70640 =
             let uu____70642 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____70645 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____70647 = FStar_Syntax_Print.term_to_string t0  in
             let uu____70649 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____70642
               uu____70645 uu____70647 uu____70649
              in
           failwith uu____70640
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let e = FStar_Syntax_Util.unfold_lazy i  in
           ((let uu____70659 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____70659
             then
               let uu____70664 = FStar_Syntax_Print.term_to_string t0  in
               let uu____70666 = FStar_Syntax_Print.term_to_string e  in
               FStar_Util.print2 ">> Unfolded (%s) ~> (%s)\n" uu____70664
                 uu____70666
             else ());
            encode_term e env)
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____70672 =
             let uu____70674 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____70674
              in
           failwith uu____70672
       | FStar_Syntax_Syntax.Tm_ascribed (t1,(k,uu____70683),uu____70684) ->
           let uu____70733 =
             match k with
             | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
             | uu____70743 -> false  in
           if uu____70733
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t1 env
       | FStar_Syntax_Syntax.Tm_quoted (qt,uu____70761) ->
           let tv =
             let uu____70767 =
               let uu____70774 = FStar_Reflection_Basic.inspect_ln qt  in
               FStar_Syntax_Embeddings.embed
                 FStar_Reflection_Embeddings.e_term_view uu____70774
                in
             uu____70767 t.FStar_Syntax_Syntax.pos
               FStar_Pervasives_Native.None
               FStar_Syntax_Embeddings.id_norm_cb
              in
           ((let uu____70778 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____70778
             then
               let uu____70783 = FStar_Syntax_Print.term_to_string t0  in
               let uu____70785 = FStar_Syntax_Print.term_to_string tv  in
               FStar_Util.print2 ">> Inspected (%s) ~> (%s)\n" uu____70783
                 uu____70785
             else ());
            (let t1 =
               let uu____70793 =
                 let uu____70804 = FStar_Syntax_Syntax.as_arg tv  in
                 [uu____70804]  in
               FStar_Syntax_Util.mk_app
                 (FStar_Reflection_Data.refl_constant_term
                    FStar_Reflection_Data.fstar_refl_pack_ln) uu____70793
                in
             encode_term t1 env))
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_pattern uu____70830) ->
           encode_term t1
             (let uu___1242_70848 = env  in
              {
                FStar_SMTEncoding_Env.bvar_bindings =
                  (uu___1242_70848.FStar_SMTEncoding_Env.bvar_bindings);
                FStar_SMTEncoding_Env.fvar_bindings =
                  (uu___1242_70848.FStar_SMTEncoding_Env.fvar_bindings);
                FStar_SMTEncoding_Env.depth =
                  (uu___1242_70848.FStar_SMTEncoding_Env.depth);
                FStar_SMTEncoding_Env.tcenv =
                  (uu___1242_70848.FStar_SMTEncoding_Env.tcenv);
                FStar_SMTEncoding_Env.warn =
                  (uu___1242_70848.FStar_SMTEncoding_Env.warn);
                FStar_SMTEncoding_Env.nolabels =
                  (uu___1242_70848.FStar_SMTEncoding_Env.nolabels);
                FStar_SMTEncoding_Env.use_zfuel_name =
                  (uu___1242_70848.FStar_SMTEncoding_Env.use_zfuel_name);
                FStar_SMTEncoding_Env.encode_non_total_function_typ =
                  (uu___1242_70848.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                FStar_SMTEncoding_Env.current_module_name =
                  (uu___1242_70848.FStar_SMTEncoding_Env.current_module_name);
                FStar_SMTEncoding_Env.encoding_quantifier = false;
                FStar_SMTEncoding_Env.global_cache =
                  (uu___1242_70848.FStar_SMTEncoding_Env.global_cache)
              })
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____70851) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = FStar_SMTEncoding_Env.lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____70859 = head_redex env t  in
           if uu____70859
           then let uu____70866 = whnf env t  in encode_term uu____70866 env
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
              let uu____70873 =
                if
                  fvb.FStar_SMTEncoding_Env.smt_arity > (Prims.parse_int "0")
                then
                  match tok.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.FreeV uu____70897 ->
                      let sym_name =
                        let uu____70908 =
                          FStar_Util.digest_of_string tkey_hash  in
                        Prims.op_Hat "@kick_partial_app_" uu____70908  in
                      let uu____70911 =
                        let uu____70914 =
                          let uu____70915 =
                            let uu____70923 =
                              FStar_SMTEncoding_Term.kick_partial_app tok  in
                            (uu____70923,
                              (FStar_Pervasives_Native.Some
                                 "kick_partial_app"), sym_name)
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____70915  in
                        [uu____70914]  in
                      (uu____70911, sym_name)
                  | FStar_SMTEncoding_Term.App (uu____70930,[]) ->
                      let sym_name =
                        let uu____70935 =
                          FStar_Util.digest_of_string tkey_hash  in
                        Prims.op_Hat "@kick_partial_app_" uu____70935  in
                      let uu____70938 =
                        let uu____70941 =
                          let uu____70942 =
                            let uu____70950 =
                              FStar_SMTEncoding_Term.kick_partial_app tok  in
                            (uu____70950,
                              (FStar_Pervasives_Native.Some
                                 "kick_partial_app"), sym_name)
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____70942  in
                        [uu____70941]  in
                      (uu____70938, sym_name)
                  | uu____70957 -> ([], "")
                else ([], "")  in
              match uu____70873 with
              | (aux_decls,sym_name) ->
                  let uu____70980 =
                    if aux_decls = []
                    then
                      FStar_All.pipe_right []
                        FStar_SMTEncoding_Term.mk_decls_trivial
                    else
                      FStar_SMTEncoding_Term.mk_decls sym_name tkey_hash
                        aux_decls []
                     in
                  (tok, uu____70980))
       | FStar_Syntax_Syntax.Tm_type uu____70988 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____70990) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.FStar_SMTEncoding_Env.current_module_name
              in
           let uu____71020 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____71020 with
            | (binders1,res) ->
                let uu____71031 =
                  (env.FStar_SMTEncoding_Env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____71031
                then
                  let uu____71038 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____71038 with
                   | (vars,guards,env',decls,uu____71063) ->
                       let fsym =
                         let uu____71077 =
                           let uu____71083 =
                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                               module_name "f"
                              in
                           (uu____71083, FStar_SMTEncoding_Term.Term_sort)
                            in
                         FStar_SMTEncoding_Term.mk_fv uu____71077  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____71089 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___1296_71098 =
                              env.FStar_SMTEncoding_Env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___1296_71098.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___1296_71098.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___1296_71098.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___1296_71098.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___1296_71098.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___1296_71098.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___1296_71098.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___1296_71098.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___1296_71098.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___1296_71098.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___1296_71098.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___1296_71098.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___1296_71098.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___1296_71098.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___1296_71098.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___1296_71098.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___1296_71098.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___1296_71098.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___1296_71098.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___1296_71098.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___1296_71098.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___1296_71098.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___1296_71098.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___1296_71098.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___1296_71098.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___1296_71098.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___1296_71098.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___1296_71098.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___1296_71098.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___1296_71098.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___1296_71098.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___1296_71098.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___1296_71098.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___1296_71098.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___1296_71098.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___1296_71098.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___1296_71098.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___1296_71098.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___1296_71098.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___1296_71098.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___1296_71098.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___1296_71098.FStar_TypeChecker_Env.nbe)
                            }) res
                          in
                       (match uu____71089 with
                        | (pre_opt,res_t) ->
                            let uu____71110 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____71110 with
                             | (res_pred,decls') ->
                                 let uu____71121 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____71134 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____71134, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____71138 =
                                         encode_formula pre env'  in
                                       (match uu____71138 with
                                        | (guard,decls0) ->
                                            let uu____71151 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____71151, decls0))
                                    in
                                 (match uu____71121 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____71165 =
                                          let uu____71176 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____71176)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t.FStar_Syntax_Syntax.pos
                                          uu____71165
                                         in
                                      let cvars =
                                        let uu____71196 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____71196
                                          (FStar_List.filter
                                             (fun x  ->
                                                let uu____71215 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    x
                                                   in
                                                let uu____71217 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    fsym
                                                   in
                                                uu____71215 <> uu____71217))
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
                                        let uu____71239 =
                                          FStar_Util.digest_of_string
                                            tkey_hash
                                           in
                                        Prims.op_Hat "Tm_arrow_" uu____71239
                                         in
                                      let cvar_sorts =
                                        FStar_List.map
                                          FStar_SMTEncoding_Term.fv_sort
                                          cvars
                                         in
                                      let caption =
                                        let uu____71254 =
                                          FStar_Options.log_queries ()  in
                                        if uu____71254
                                        then
                                          let uu____71257 =
                                            let uu____71259 =
                                              FStar_TypeChecker_Normalize.term_to_string
                                                env.FStar_SMTEncoding_Env.tcenv
                                                t0
                                               in
                                            FStar_Util.replace_char
                                              uu____71259 10 32
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____71257
                                        else FStar_Pervasives_Native.None  in
                                      let tdecl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (tsym, cvar_sorts,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            caption)
                                         in
                                      let t1 =
                                        let uu____71272 =
                                          let uu____71280 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              cvars
                                             in
                                          (tsym, uu____71280)  in
                                        FStar_SMTEncoding_Util.mkApp
                                          uu____71272
                                         in
                                      let t_has_kind =
                                        FStar_SMTEncoding_Term.mk_HasType t1
                                          FStar_SMTEncoding_Term.mk_Term_type
                                         in
                                      let k_assumption =
                                        let a_name =
                                          Prims.op_Hat "kinding_" tsym  in
                                        let uu____71299 =
                                          let uu____71307 =
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              ([[t_has_kind]], cvars,
                                                t_has_kind)
                                             in
                                          (uu____71307,
                                            (FStar_Pervasives_Native.Some
                                               a_name), a_name)
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____71299
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
                                        let uu____71324 =
                                          let uu____71332 =
                                            let uu____71333 =
                                              let uu____71344 =
                                                let uu____71345 =
                                                  let uu____71350 =
                                                    let uu____71351 =
                                                      FStar_SMTEncoding_Term.mk_PreType
                                                        f
                                                       in
                                                    FStar_SMTEncoding_Term.mk_tester
                                                      "Tm_arrow" uu____71351
                                                     in
                                                  (f_has_t, uu____71350)  in
                                                FStar_SMTEncoding_Util.mkImp
                                                  uu____71345
                                                 in
                                              ([[f_has_t]], (fsym :: cvars),
                                                uu____71344)
                                               in
                                            let uu____71369 =
                                              mkForall_fuel module_name
                                                t0.FStar_Syntax_Syntax.pos
                                               in
                                            uu____71369 uu____71333  in
                                          (uu____71332,
                                            (FStar_Pervasives_Native.Some
                                               "pre-typing for functions"),
                                            (Prims.op_Hat module_name
                                               (Prims.op_Hat "_" a_name)))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____71324
                                         in
                                      let t_interp1 =
                                        let a_name =
                                          Prims.op_Hat "interpretation_" tsym
                                           in
                                        let uu____71392 =
                                          let uu____71400 =
                                            let uu____71401 =
                                              let uu____71412 =
                                                FStar_SMTEncoding_Util.mkIff
                                                  (f_has_t_z, t_interp)
                                                 in
                                              ([[f_has_t_z]], (fsym ::
                                                cvars), uu____71412)
                                               in
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              uu____71401
                                             in
                                          (uu____71400,
                                            (FStar_Pervasives_Native.Some
                                               a_name),
                                            (Prims.op_Hat module_name
                                               (Prims.op_Hat "_" a_name)))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____71392
                                         in
                                      let t_decls1 =
                                        [tdecl;
                                        k_assumption;
                                        pre_typing;
                                        t_interp1]  in
                                      let uu____71435 =
                                        let uu____71436 =
                                          let uu____71439 =
                                            let uu____71442 =
                                              FStar_SMTEncoding_Term.mk_decls
                                                tsym tkey_hash t_decls1
                                                (FStar_List.append decls
                                                   (FStar_List.append decls'
                                                      guard_decls))
                                               in
                                            FStar_List.append guard_decls
                                              uu____71442
                                             in
                                          FStar_List.append decls'
                                            uu____71439
                                           in
                                        FStar_List.append decls uu____71436
                                         in
                                      (t1, uu____71435)))))
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
                     let uu____71463 =
                       let uu____71471 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____71471,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"), a_name)
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____71463  in
                   let fsym =
                     FStar_SMTEncoding_Term.mk_fv
                       ("f", FStar_SMTEncoding_Term.Term_sort)
                      in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.op_Hat "pre_typing_" tsym  in
                     let uu____71484 =
                       let uu____71492 =
                         let uu____71493 =
                           let uu____71504 =
                             let uu____71505 =
                               let uu____71510 =
                                 let uu____71511 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____71511
                                  in
                               (f_has_t, uu____71510)  in
                             FStar_SMTEncoding_Util.mkImp uu____71505  in
                           ([[f_has_t]], [fsym], uu____71504)  in
                         let uu____71537 =
                           mkForall_fuel module_name
                             t0.FStar_Syntax_Syntax.pos
                            in
                         uu____71537 uu____71493  in
                       (uu____71492, (FStar_Pervasives_Native.Some a_name),
                         a_name)
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____71484  in
                   let uu____71554 =
                     FStar_All.pipe_right [tdecl; t_kinding; t_interp]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                      in
                   (t1, uu____71554)))
       | FStar_Syntax_Syntax.Tm_refine uu____71557 ->
           let uu____71564 =
             let uu____71569 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Env.Weak;
                 FStar_TypeChecker_Env.HNF;
                 FStar_TypeChecker_Env.EraseUniverses]
                 env.FStar_SMTEncoding_Env.tcenv t0
                in
             match uu____71569 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____71576;
                 FStar_Syntax_Syntax.vars = uu____71577;_} ->
                 let uu____71584 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____71584 with
                  | (b,f1) ->
                      let uu____71609 =
                        let uu____71610 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____71610  in
                      (uu____71609, f1))
             | uu____71625 -> failwith "impossible"  in
           (match uu____71564 with
            | (x,f) ->
                let uu____71637 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____71637 with
                 | (base_t,decls) ->
                     let uu____71648 =
                       FStar_SMTEncoding_Env.gen_term_var env x  in
                     (match uu____71648 with
                      | (x1,xtm,env') ->
                          let uu____71665 = encode_formula f env'  in
                          (match uu____71665 with
                           | (refinement,decls') ->
                               let uu____71676 =
                                 FStar_SMTEncoding_Env.fresh_fvar
                                   env.FStar_SMTEncoding_Env.current_module_name
                                   "f" FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____71676 with
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
                                      let uu____71704 =
                                        let uu____71715 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____71726 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____71715
                                          uu____71726
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____71704
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun y  ->
                                              (let uu____71780 =
                                                 FStar_SMTEncoding_Term.fv_name
                                                   y
                                                  in
                                               uu____71780 <> x1) &&
                                                (let uu____71784 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     y
                                                    in
                                                 uu____71784 <> fsym)))
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
                                      let uu____71820 =
                                        FStar_Util.digest_of_string tkey_hash
                                         in
                                      Prims.op_Hat "Tm_refine_" uu____71820
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
                                      let uu____71840 =
                                        let uu____71848 =
                                          FStar_List.map
                                            FStar_SMTEncoding_Util.mkFreeV
                                            cvars1
                                           in
                                        (tsym, uu____71848)  in
                                      FStar_SMTEncoding_Util.mkApp
                                        uu____71840
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
                                      let uu____71868 =
                                        let uu____71876 =
                                          let uu____71877 =
                                            let uu____71888 =
                                              FStar_SMTEncoding_Util.mkIff
                                                (t_haseq_ref, t_haseq_base)
                                               in
                                            ([[t_haseq_ref]], cvars1,
                                              uu____71888)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            t0.FStar_Syntax_Syntax.pos
                                            uu____71877
                                           in
                                        (uu____71876,
                                          (FStar_Pervasives_Native.Some
                                             (Prims.op_Hat "haseq for " tsym)),
                                          (Prims.op_Hat "haseq" tsym))
                                         in
                                      FStar_SMTEncoding_Util.mkAssume
                                        uu____71868
                                       in
                                    let t_kinding =
                                      let uu____71902 =
                                        let uu____71910 =
                                          FStar_SMTEncoding_Term.mkForall
                                            t0.FStar_Syntax_Syntax.pos
                                            ([[t_has_kind]], cvars1,
                                              t_has_kind)
                                           in
                                        (uu____71910,
                                          (FStar_Pervasives_Native.Some
                                             "refinement kinding"),
                                          (Prims.op_Hat "refinement_kinding_"
                                             tsym))
                                         in
                                      FStar_SMTEncoding_Util.mkAssume
                                        uu____71902
                                       in
                                    let t_interp =
                                      let uu____71924 =
                                        let uu____71932 =
                                          let uu____71933 =
                                            let uu____71944 =
                                              FStar_SMTEncoding_Util.mkIff
                                                (x_has_t, encoding)
                                               in
                                            ([[x_has_t]], (ffv :: xfv ::
                                              cvars1), uu____71944)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            t0.FStar_Syntax_Syntax.pos
                                            uu____71933
                                           in
                                        (uu____71932,
                                          (FStar_Pervasives_Native.Some
                                             "refinement_interpretation"),
                                          (Prims.op_Hat
                                             "refinement_interpretation_"
                                             tsym))
                                         in
                                      FStar_SMTEncoding_Util.mkAssume
                                        uu____71924
                                       in
                                    let t_decls1 =
                                      [tdecl; t_kinding; t_interp; t_haseq1]
                                       in
                                    let uu____71976 =
                                      let uu____71977 =
                                        let uu____71980 =
                                          FStar_SMTEncoding_Term.mk_decls
                                            tsym tkey_hash t_decls1
                                            (FStar_List.append decls decls')
                                           in
                                        FStar_List.append decls' uu____71980
                                         in
                                      FStar_List.append decls uu____71977  in
                                    (t1, uu____71976))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,uu____71984) ->
           let ttm =
             let uu____72002 =
               FStar_Syntax_Unionfind.uvar_id
                 uv.FStar_Syntax_Syntax.ctx_uvar_head
                in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____72002  in
           let uu____72004 =
             encode_term_pred FStar_Pervasives_Native.None
               uv.FStar_Syntax_Syntax.ctx_uvar_typ env ttm
              in
           (match uu____72004 with
            | (t_has_k,decls) ->
                let d =
                  let uu____72016 =
                    let uu____72024 =
                      let uu____72026 =
                        let uu____72028 =
                          let uu____72030 =
                            FStar_Syntax_Unionfind.uvar_id
                              uv.FStar_Syntax_Syntax.ctx_uvar_head
                             in
                          FStar_Util.string_of_int uu____72030  in
                        FStar_Util.format1 "uvar_typing_%s" uu____72028  in
                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                        uu____72026
                       in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____72024)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____72016  in
                let uu____72036 =
                  let uu____72037 =
                    FStar_All.pipe_right [d]
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append decls uu____72037  in
                (ttm, uu____72036))
       | FStar_Syntax_Syntax.Tm_app uu____72044 ->
           let uu____72061 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____72061 with
            | (head1,args_e) ->
                let uu____72108 =
                  let uu____72123 =
                    let uu____72124 = FStar_Syntax_Subst.compress head1  in
                    uu____72124.FStar_Syntax_Syntax.n  in
                  (uu____72123, args_e)  in
                (match uu____72108 with
                 | uu____72141 when head_redex env head1 ->
                     let uu____72156 = whnf env t  in
                     encode_term uu____72156 env
                 | uu____72157 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____72180 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_fvar fv,uu____72198) when
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
                       FStar_Syntax_Syntax.pos = uu____72220;
                       FStar_Syntax_Syntax.vars = uu____72221;_},uu____72222),uu____72223)
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
                       FStar_Syntax_Syntax.pos = uu____72249;
                       FStar_Syntax_Syntax.vars = uu____72250;_},uu____72251),
                    (v0,uu____72253)::(v1,uu____72255)::(v2,uu____72257)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____72328 = encode_term v0 env  in
                     (match uu____72328 with
                      | (v01,decls0) ->
                          let uu____72339 = encode_term v1 env  in
                          (match uu____72339 with
                           | (v11,decls1) ->
                               let uu____72350 = encode_term v2 env  in
                               (match uu____72350 with
                                | (v21,decls2) ->
                                    let uu____72361 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____72361,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(v0,uu____72364)::(v1,uu____72366)::(v2,uu____72368)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____72435 = encode_term v0 env  in
                     (match uu____72435 with
                      | (v01,decls0) ->
                          let uu____72446 = encode_term v1 env  in
                          (match uu____72446 with
                           | (v11,decls1) ->
                               let uu____72457 = encode_term v2 env  in
                               (match uu____72457 with
                                | (v21,decls2) ->
                                    let uu____72468 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____72468,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____72470)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____72506)::(rng,uu____72508)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____72559) ->
                     let e0 =
                       let uu____72581 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg
                         env.FStar_SMTEncoding_Env.tcenv head1 uu____72581
                        in
                     ((let uu____72591 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug
                              env.FStar_SMTEncoding_Env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____72591
                       then
                         let uu____72596 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____72596
                       else ());
                      (let e =
                         let uu____72604 =
                           let uu____72609 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____72610 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____72609
                             uu____72610
                            in
                         uu____72604 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____72619),(arg,uu____72621)::[]) ->
                     encode_term arg env
                 | uu____72656 ->
                     let uu____72671 = encode_args args_e env  in
                     (match uu____72671 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____72732 = encode_term head1 env  in
                            match uu____72732 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____72804 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____72804 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____72902  ->
                                                 fun uu____72903  ->
                                                   match (uu____72902,
                                                           uu____72903)
                                                   with
                                                   | ((bv,uu____72933),
                                                      (a,uu____72935)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____72965 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____72965
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____72966 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm
                                             in
                                          (match uu____72966 with
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
                                                 let uu____72983 =
                                                   let uu____72991 =
                                                     FStar_SMTEncoding_Term.mkForall
                                                       t0.FStar_Syntax_Syntax.pos
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____73000 =
                                                     let uu____73002 =
                                                       let uu____73004 =
                                                         FStar_SMTEncoding_Term.hash_of_term
                                                           app_tm
                                                          in
                                                       FStar_Util.digest_of_string
                                                         uu____73004
                                                        in
                                                     Prims.op_Hat
                                                       "partial_app_typing_"
                                                       uu____73002
                                                      in
                                                   (uu____72991,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____73000)
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____72983
                                                  in
                                               let uu____73010 =
                                                 let uu____73013 =
                                                   let uu____73016 =
                                                     let uu____73019 =
                                                       FStar_SMTEncoding_Term.mk_decls
                                                         "" tkey_hash
                                                         [e_typing]
                                                         (FStar_List.append
                                                            decls
                                                            (FStar_List.append
                                                               decls' decls''))
                                                        in
                                                     FStar_List.append
                                                       decls'' uu____73019
                                                      in
                                                   FStar_List.append decls'
                                                     uu____73016
                                                    in
                                                 FStar_List.append decls
                                                   uu____73013
                                                  in
                                               (app_tm, uu____73010))))
                             in
                          let encode_full_app fv =
                            let uu____73039 =
                              FStar_SMTEncoding_Env.lookup_free_var_sym env
                                fv
                               in
                            match uu____73039 with
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
                                   FStar_Syntax_Syntax.pos = uu____73082;
                                   FStar_Syntax_Syntax.vars = uu____73083;_},uu____73084)
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
                                   FStar_Syntax_Syntax.pos = uu____73091;
                                   FStar_Syntax_Syntax.vars = uu____73092;_},uu____73093)
                                ->
                                let uu____73098 =
                                  let uu____73099 =
                                    let uu____73104 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____73104
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____73099
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____73098
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____73134 =
                                  let uu____73135 =
                                    let uu____73140 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____73140
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____73135
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____73134
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____73169,(FStar_Util.Inl t1,uu____73171),uu____73172)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____73219,(FStar_Util.Inr c,uu____73221),uu____73222)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____73269 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____73290 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Env.Weak;
                                     FStar_TypeChecker_Env.HNF;
                                     FStar_TypeChecker_Env.EraseUniverses]
                                     env.FStar_SMTEncoding_Env.tcenv
                                     head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____73290
                                  in
                               let uu____73291 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____73291 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____73307;
                                            FStar_Syntax_Syntax.vars =
                                              uu____73308;_},uu____73309)
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
                                     | uu____73327 ->
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
           let uu____73406 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____73406 with
            | (bs1,body1,opening) ->
                let fallback uu____73429 =
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
                  let uu____73439 =
                    let uu____73440 =
                      FStar_SMTEncoding_Term.mk_fv
                        (f, FStar_SMTEncoding_Term.Term_sort)
                       in
                    FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV
                      uu____73440
                     in
                  let uu____73442 =
                    FStar_All.pipe_right [decl]
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  (uu____73439, uu____73442)  in
                let is_impure rc =
                  let uu____73452 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                      env.FStar_SMTEncoding_Env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____73452 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____73467 =
                          let uu____73480 =
                            FStar_TypeChecker_Env.get_range
                              env.FStar_SMTEncoding_Env.tcenv
                             in
                          FStar_TypeChecker_Util.new_implicit_var
                            "SMTEncoding codomain" uu____73480
                            env.FStar_SMTEncoding_Env.tcenv
                            FStar_Syntax_Util.ktype0
                           in
                        (match uu____73467 with
                         | (t1,uu____73483,uu____73484) -> t1)
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  let uu____73502 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                     in
                  if uu____73502
                  then
                    let uu____73507 = FStar_Syntax_Syntax.mk_Total res_typ
                       in
                    FStar_Pervasives_Native.Some uu____73507
                  else
                    (let uu____73510 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid
                        in
                     if uu____73510
                     then
                       let uu____73515 =
                         FStar_Syntax_Syntax.mk_GTotal res_typ  in
                       FStar_Pervasives_Native.Some uu____73515
                     else FStar_Pervasives_Native.None)
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____73523 =
                         let uu____73529 =
                           let uu____73531 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____73531
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____73529)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____73523);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____73536 =
                       (is_impure rc) &&
                         (let uu____73539 =
                            FStar_TypeChecker_Env.is_reifiable_rc
                              env.FStar_SMTEncoding_Env.tcenv rc
                             in
                          Prims.op_Negation uu____73539)
                        in
                     if uu____73536
                     then fallback ()
                     else
                       (let uu____73548 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____73548 with
                        | (vars,guards,envbody,decls,uu____73573) ->
                            let body2 =
                              let uu____73587 =
                                FStar_TypeChecker_Env.is_reifiable_rc
                                  env.FStar_SMTEncoding_Env.tcenv rc
                                 in
                              if uu____73587
                              then
                                FStar_TypeChecker_Util.reify_body
                                  env.FStar_SMTEncoding_Env.tcenv body1
                              else body1  in
                            let uu____73592 = encode_term body2 envbody  in
                            (match uu____73592 with
                             | (body3,decls') ->
                                 let uu____73603 =
                                   let uu____73612 = codomain_eff rc  in
                                   match uu____73612 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____73631 = encode_term tfun env
                                          in
                                       (match uu____73631 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____73603 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____73665 =
                                          let uu____73676 =
                                            let uu____73677 =
                                              let uu____73682 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____73682, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____73677
                                             in
                                          ([], vars, uu____73676)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t0.FStar_Syntax_Syntax.pos
                                          uu____73665
                                         in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body
                                         in
                                      let uu____73690 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            (cvars, key_body)
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____73706 =
                                              let uu____73709 =
                                                let uu____73720 =
                                                  FStar_SMTEncoding_Term.free_variables
                                                    t1
                                                   in
                                                FStar_List.append uu____73720
                                                  cvars
                                                 in
                                              FStar_Util.remove_dups
                                                FStar_SMTEncoding_Term.fv_eq
                                                uu____73709
                                               in
                                            let uu____73747 =
                                              FStar_SMTEncoding_Util.mkAnd
                                                (key_body, t1)
                                               in
                                            (uu____73706, uu____73747)
                                         in
                                      (match uu____73690 with
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
                                           let uu____73769 =
                                             is_an_eta_expansion env vars
                                               body3
                                              in
                                           (match uu____73769 with
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
                                                  let uu____73785 =
                                                    FStar_Util.digest_of_string
                                                      tkey_hash
                                                     in
                                                  Prims.op_Hat "Tm_abs_"
                                                    uu____73785
                                                   in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None)
                                                   in
                                                let f =
                                                  let uu____73794 =
                                                    let uu____73802 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    (fsym, uu____73802)  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____73794
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
                                                      let uu____73819 =
                                                        let uu____73820 =
                                                          let uu____73828 =
                                                            FStar_SMTEncoding_Term.mkForall
                                                              t0.FStar_Syntax_Syntax.pos
                                                              ([[f]], cvars1,
                                                                f_has_t)
                                                             in
                                                          (uu____73828,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name)
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____73820
                                                         in
                                                      [uu____73819]
                                                   in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.op_Hat
                                                      "interpretation_" fsym
                                                     in
                                                  let uu____73843 =
                                                    let uu____73851 =
                                                      let uu____73852 =
                                                        let uu____73863 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3)
                                                           in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____73863)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        t0.FStar_Syntax_Syntax.pos
                                                        uu____73852
                                                       in
                                                    (uu____73851,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____73843
                                                   in
                                                let f_decls =
                                                  FStar_List.append (fdecl ::
                                                    typing_f) [interp_f]
                                                   in
                                                let uu____73877 =
                                                  let uu____73878 =
                                                    let uu____73881 =
                                                      let uu____73884 =
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
                                                        decls'' uu____73884
                                                       in
                                                    FStar_List.append decls'
                                                      uu____73881
                                                     in
                                                  FStar_List.append decls
                                                    uu____73878
                                                   in
                                                (f, uu____73877))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____73887,{
                           FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                             uu____73888;
                           FStar_Syntax_Syntax.lbunivs = uu____73889;
                           FStar_Syntax_Syntax.lbtyp = uu____73890;
                           FStar_Syntax_Syntax.lbeff = uu____73891;
                           FStar_Syntax_Syntax.lbdef = uu____73892;
                           FStar_Syntax_Syntax.lbattrs = uu____73893;
                           FStar_Syntax_Syntax.lbpos = uu____73894;_}::uu____73895),uu____73896)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____73930;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____73932;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____73934;
                FStar_Syntax_Syntax.lbpos = uu____73935;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____73962 ->
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
              let uu____74034 =
                let uu____74039 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____74039 env  in
              match uu____74034 with
              | (ee1,decls1) ->
                  let uu____74064 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____74064 with
                   | (xs,e21) ->
                       let uu____74089 = FStar_List.hd xs  in
                       (match uu____74089 with
                        | (x1,uu____74107) ->
                            let env' =
                              FStar_SMTEncoding_Env.push_term_var env x1 ee1
                               in
                            let uu____74113 = encode_body e21 env'  in
                            (match uu____74113 with
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
            let uu____74143 =
              let uu____74151 =
                let uu____74152 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____74152  in
              FStar_SMTEncoding_Env.gen_term_var env uu____74151  in
            match uu____74143 with
            | (scrsym,scr',env1) ->
                let uu____74162 = encode_term e env1  in
                (match uu____74162 with
                 | (scr,decls) ->
                     let uu____74173 =
                       let encode_branch b uu____74202 =
                         match uu____74202 with
                         | (else_case,decls1) ->
                             let uu____74221 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____74221 with
                              | (p,w,br) ->
                                  let uu____74247 = encode_pat env1 p  in
                                  (match uu____74247 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____74284  ->
                                                   match uu____74284 with
                                                   | (x,t) ->
                                                       FStar_SMTEncoding_Env.push_term_var
                                                         env2 x t) env1)
                                          in
                                       let uu____74291 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____74313 =
                                               encode_term w1 env2  in
                                             (match uu____74313 with
                                              | (w2,decls2) ->
                                                  let uu____74326 =
                                                    let uu____74327 =
                                                      let uu____74332 =
                                                        let uu____74333 =
                                                          let uu____74338 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____74338)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____74333
                                                         in
                                                      (guard, uu____74332)
                                                       in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____74327
                                                     in
                                                  (uu____74326, decls2))
                                          in
                                       (match uu____74291 with
                                        | (guard1,decls2) ->
                                            let uu____74353 =
                                              encode_br br env2  in
                                            (match uu____74353 with
                                             | (br1,decls3) ->
                                                 let uu____74366 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____74366,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____74173 with
                      | (match_tm,decls1) ->
                          let uu____74387 =
                            let uu____74388 =
                              let uu____74399 =
                                let uu____74406 =
                                  let uu____74411 =
                                    FStar_SMTEncoding_Term.mk_fv
                                      (scrsym,
                                        FStar_SMTEncoding_Term.Term_sort)
                                     in
                                  (uu____74411, scr)  in
                                [uu____74406]  in
                              (uu____74399, match_tm)  in
                            FStar_SMTEncoding_Term.mkLet' uu____74388
                              FStar_Range.dummyRange
                             in
                          (uu____74387, decls1)))

and (encode_pat :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.pat -> (FStar_SMTEncoding_Env.env_t * pattern))
  =
  fun env  ->
    fun pat  ->
      (let uu____74434 =
         FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
           FStar_Options.Medium
          in
       if uu____74434
       then
         let uu____74437 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____74437
       else ());
      (let uu____74442 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____74442 with
       | (vars,pat_term) ->
           let uu____74459 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____74501  ->
                     fun v1  ->
                       match uu____74501 with
                       | (env1,vars1) ->
                           let uu____74537 =
                             FStar_SMTEncoding_Env.gen_term_var env1 v1  in
                           (match uu____74537 with
                            | (xx,uu____74556,env2) ->
                                let uu____74560 =
                                  let uu____74567 =
                                    let uu____74572 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xx,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    (v1, uu____74572)  in
                                  uu____74567 :: vars1  in
                                (env2, uu____74560))) (env, []))
              in
           (match uu____74459 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____74627 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____74628 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____74629 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____74637 = encode_const c env1  in
                      (match uu____74637 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____74645::uu____74646 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____74650 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon
                            env1.FStar_SMTEncoding_Env.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____74673 =
                          FStar_TypeChecker_Env.datacons_of_typ
                            env1.FStar_SMTEncoding_Env.tcenv tc_name
                           in
                        match uu____74673 with
                        | (uu____74681,uu____74682::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____74687 ->
                            FStar_SMTEncoding_Env.mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____74723  ->
                                  match uu____74723 with
                                  | (arg,uu____74733) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____74742 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____74742))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____74774) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____74805 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____74830 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____74876  ->
                                  match uu____74876 with
                                  | (arg,uu____74892) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____74901 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____74901))
                         in
                      FStar_All.pipe_right uu____74830 FStar_List.flatten
                   in
                let pat_term1 uu____74932 = encode_term pat_term env1  in
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
      let uu____74942 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____74990  ->
                fun uu____74991  ->
                  match (uu____74990, uu____74991) with
                  | ((tms,decls),(t,uu____75031)) ->
                      let uu____75058 = encode_term t env  in
                      (match uu____75058 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____74942 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____75115 = FStar_Syntax_Util.list_elements e  in
        match uu____75115 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____75146 =
          let uu____75163 = FStar_Syntax_Util.unmeta p  in
          FStar_All.pipe_right uu____75163 FStar_Syntax_Util.head_and_args
           in
        match uu____75146 with
        | (head1,args) ->
            let uu____75214 =
              let uu____75229 =
                let uu____75230 = FStar_Syntax_Util.un_uinst head1  in
                uu____75230.FStar_Syntax_Syntax.n  in
              (uu____75229, args)  in
            (match uu____75214 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____75252,uu____75253)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____75305 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or1 t1 =
          let uu____75360 =
            let uu____75377 = FStar_Syntax_Util.unmeta t1  in
            FStar_All.pipe_right uu____75377 FStar_Syntax_Util.head_and_args
             in
          match uu____75360 with
          | (head1,args) ->
              let uu____75424 =
                let uu____75439 =
                  let uu____75440 = FStar_Syntax_Util.un_uinst head1  in
                  uu____75440.FStar_Syntax_Syntax.n  in
                (uu____75439, args)  in
              (match uu____75424 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____75459)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____75496 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____75526 = smt_pat_or1 t1  in
            (match uu____75526 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____75548 = list_elements1 e  in
                 FStar_All.pipe_right uu____75548
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____75578 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____75578
                           (FStar_List.map one_pat)))
             | uu____75601 ->
                 let uu____75606 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____75606])
        | uu____75657 ->
            let uu____75660 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____75660]
         in
      let uu____75711 =
        let uu____75726 =
          let uu____75727 = FStar_Syntax_Subst.compress t  in
          uu____75727.FStar_Syntax_Syntax.n  in
        match uu____75726 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____75766 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____75766 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____75801;
                        FStar_Syntax_Syntax.effect_name = uu____75802;
                        FStar_Syntax_Syntax.result_typ = uu____75803;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____75805)::(post,uu____75807)::(pats,uu____75809)::[];
                        FStar_Syntax_Syntax.flags = uu____75810;_}
                      ->
                      let uu____75871 = lemma_pats pats  in
                      (binders1, pre, post, uu____75871)
                  | uu____75882 -> failwith "impos"))
        | uu____75898 -> failwith "Impos"  in
      match uu____75711 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___1940_75935 = env  in
            {
              FStar_SMTEncoding_Env.bvar_bindings =
                (uu___1940_75935.FStar_SMTEncoding_Env.bvar_bindings);
              FStar_SMTEncoding_Env.fvar_bindings =
                (uu___1940_75935.FStar_SMTEncoding_Env.fvar_bindings);
              FStar_SMTEncoding_Env.depth =
                (uu___1940_75935.FStar_SMTEncoding_Env.depth);
              FStar_SMTEncoding_Env.tcenv =
                (uu___1940_75935.FStar_SMTEncoding_Env.tcenv);
              FStar_SMTEncoding_Env.warn =
                (uu___1940_75935.FStar_SMTEncoding_Env.warn);
              FStar_SMTEncoding_Env.nolabels =
                (uu___1940_75935.FStar_SMTEncoding_Env.nolabels);
              FStar_SMTEncoding_Env.use_zfuel_name = true;
              FStar_SMTEncoding_Env.encode_non_total_function_typ =
                (uu___1940_75935.FStar_SMTEncoding_Env.encode_non_total_function_typ);
              FStar_SMTEncoding_Env.current_module_name =
                (uu___1940_75935.FStar_SMTEncoding_Env.current_module_name);
              FStar_SMTEncoding_Env.encoding_quantifier =
                (uu___1940_75935.FStar_SMTEncoding_Env.encoding_quantifier);
              FStar_SMTEncoding_Env.global_cache =
                (uu___1940_75935.FStar_SMTEncoding_Env.global_cache)
            }  in
          let uu____75937 =
            encode_binders FStar_Pervasives_Native.None binders env1  in
          (match uu____75937 with
           | (vars,guards,env2,decls,uu____75962) ->
               let uu____75975 = encode_smt_patterns patterns env2  in
               (match uu____75975 with
                | (pats,decls') ->
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
                    let env3 =
                      let uu___1953_76002 = env2  in
                      {
                        FStar_SMTEncoding_Env.bvar_bindings =
                          (uu___1953_76002.FStar_SMTEncoding_Env.bvar_bindings);
                        FStar_SMTEncoding_Env.fvar_bindings =
                          (uu___1953_76002.FStar_SMTEncoding_Env.fvar_bindings);
                        FStar_SMTEncoding_Env.depth =
                          (uu___1953_76002.FStar_SMTEncoding_Env.depth);
                        FStar_SMTEncoding_Env.tcenv =
                          (uu___1953_76002.FStar_SMTEncoding_Env.tcenv);
                        FStar_SMTEncoding_Env.warn =
                          (uu___1953_76002.FStar_SMTEncoding_Env.warn);
                        FStar_SMTEncoding_Env.nolabels = true;
                        FStar_SMTEncoding_Env.use_zfuel_name =
                          (uu___1953_76002.FStar_SMTEncoding_Env.use_zfuel_name);
                        FStar_SMTEncoding_Env.encode_non_total_function_typ =
                          (uu___1953_76002.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                        FStar_SMTEncoding_Env.current_module_name =
                          (uu___1953_76002.FStar_SMTEncoding_Env.current_module_name);
                        FStar_SMTEncoding_Env.encoding_quantifier =
                          (uu___1953_76002.FStar_SMTEncoding_Env.encoding_quantifier);
                        FStar_SMTEncoding_Env.global_cache =
                          (uu___1953_76002.FStar_SMTEncoding_Env.global_cache)
                      }  in
                    let uu____76004 =
                      let uu____76009 = FStar_Syntax_Util.unmeta pre  in
                      encode_formula uu____76009 env3  in
                    (match uu____76004 with
                     | (pre1,decls'') ->
                         let uu____76016 =
                           let uu____76021 = FStar_Syntax_Util.unmeta post1
                              in
                           encode_formula uu____76021 env3  in
                         (match uu____76016 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append decls'
                                     (FStar_List.append decls'' decls'''))
                                 in
                              let uu____76031 =
                                let uu____76032 =
                                  let uu____76043 =
                                    let uu____76044 =
                                      let uu____76049 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards)
                                         in
                                      (uu____76049, post2)  in
                                    FStar_SMTEncoding_Util.mkImp uu____76044
                                     in
                                  (pats, vars, uu____76043)  in
                                FStar_SMTEncoding_Term.mkForall
                                  t.FStar_Syntax_Syntax.pos uu____76032
                                 in
                              (uu____76031, decls1)))))

and (encode_smt_patterns :
  FStar_Syntax_Syntax.arg Prims.list Prims.list ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term Prims.list Prims.list *
        FStar_SMTEncoding_Term.decls_t))
  =
  fun pats_l  ->
    fun env  ->
      let env1 =
        let uu___1965_76069 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___1965_76069.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___1965_76069.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___1965_76069.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___1965_76069.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___1965_76069.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___1965_76069.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___1965_76069.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___1965_76069.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___1965_76069.FStar_SMTEncoding_Env.encoding_quantifier);
          FStar_SMTEncoding_Env.global_cache =
            (uu___1965_76069.FStar_SMTEncoding_Env.global_cache)
        }  in
      let encode_smt_pattern t =
        let uu____76085 = FStar_Syntax_Util.head_and_args t  in
        match uu____76085 with
        | (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____76148::(x,uu____76150)::(t1,uu____76152)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____76219 = encode_term x env1  in
                 (match uu____76219 with
                  | (x1,decls) ->
                      let uu____76230 = encode_term t1 env1  in
                      (match uu____76230 with
                       | (t2,decls') ->
                           let uu____76241 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                           (uu____76241, (FStar_List.append decls decls'))))
             | uu____76242 -> encode_term t env1)
         in
      FStar_List.fold_right
        (fun pats  ->
           fun uu____76285  ->
             match uu____76285 with
             | (pats_l1,decls) ->
                 let uu____76330 =
                   FStar_List.fold_right
                     (fun uu____76365  ->
                        fun uu____76366  ->
                          match (uu____76365, uu____76366) with
                          | ((p,uu____76408),(pats1,decls1)) ->
                              let uu____76443 = encode_smt_pattern p  in
                              (match uu____76443 with
                               | (t,d) ->
                                   let uu____76458 =
                                     FStar_SMTEncoding_Term.check_pattern_ok
                                       t
                                      in
                                   (match uu____76458 with
                                    | FStar_Pervasives_Native.None  ->
                                        ((t :: pats1),
                                          (FStar_List.append d decls1))
                                    | FStar_Pervasives_Native.Some
                                        illegal_subterm ->
                                        ((let uu____76475 =
                                            let uu____76481 =
                                              let uu____76483 =
                                                FStar_Syntax_Print.term_to_string
                                                  p
                                                 in
                                              let uu____76485 =
                                                FStar_SMTEncoding_Term.print_smt_term
                                                  illegal_subterm
                                                 in
                                              FStar_Util.format2
                                                "Pattern %s contains illegal sub-term (%s); dropping it"
                                                uu____76483 uu____76485
                                               in
                                            (FStar_Errors.Warning_SMTPatternIllFormed,
                                              uu____76481)
                                             in
                                          FStar_Errors.log_issue
                                            p.FStar_Syntax_Syntax.pos
                                            uu____76475);
                                         (pats1,
                                           (FStar_List.append d decls1))))))
                     pats ([], decls)
                    in
                 (match uu____76330 with
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
        let uu____76545 =
          FStar_All.pipe_left
            (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____76545
        then
          let uu____76550 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____76552 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____76550 uu____76552
        else ()  in
      let enc f r l =
        let uu____76594 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____76626 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____76626 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____76594 with
        | (decls,args) ->
            let uu____76657 =
              let uu___2029_76658 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___2029_76658.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___2029_76658.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____76657, decls)
         in
      let const_op f r uu____76693 =
        let uu____76706 = f r  in (uu____76706, [])  in
      let un_op f l =
        let uu____76729 = FStar_List.hd l  in
        FStar_All.pipe_left f uu____76729  in
      let bin_op f uu___632_76749 =
        match uu___632_76749 with
        | t1::t2::[] -> f (t1, t2)
        | uu____76760 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____76801 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____76826  ->
                 match uu____76826 with
                 | (t,uu____76842) ->
                     let uu____76847 = encode_formula t env  in
                     (match uu____76847 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____76801 with
        | (decls,phis) ->
            let uu____76876 =
              let uu___2059_76877 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___2059_76877.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___2059_76877.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____76876, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____76940  ->
               match uu____76940 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____76961) -> false
                    | uu____76964 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____76983 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____76983
        else
          (let uu____77000 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____77000 r rf)
         in
      let eq3_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____77068 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::t1::v0::v1::[] ->
                     let uu____77100 =
                       let uu____77105 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____77106 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____77105, uu____77106)  in
                     FStar_SMTEncoding_Util.mkAnd uu____77100
                 | uu____77107 -> failwith "Impossible")
             in
          uu____77068 r args
        else
          (let uu____77113 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____77113)
         in
      let h_equals_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____77175 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::v0::t1::v1::[] ->
                     let uu____77207 =
                       let uu____77212 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____77213 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____77212, uu____77213)  in
                     FStar_SMTEncoding_Util.mkAnd uu____77207
                 | uu____77214 -> failwith "Impossible")
             in
          uu____77175 r args
        else
          (let uu____77220 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____77220)
         in
      let mk_imp1 r uu___633_77249 =
        match uu___633_77249 with
        | (lhs,uu____77255)::(rhs,uu____77257)::[] ->
            let uu____77298 = encode_formula rhs env  in
            (match uu____77298 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____77313) ->
                      (l1, decls1)
                  | uu____77318 ->
                      let uu____77319 = encode_formula lhs env  in
                      (match uu____77319 with
                       | (l2,decls2) ->
                           let uu____77330 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____77330, (FStar_List.append decls1 decls2)))))
        | uu____77331 -> failwith "impossible"  in
      let mk_ite r uu___634_77359 =
        match uu___634_77359 with
        | (guard,uu____77365)::(_then,uu____77367)::(_else,uu____77369)::[]
            ->
            let uu____77426 = encode_formula guard env  in
            (match uu____77426 with
             | (g,decls1) ->
                 let uu____77437 = encode_formula _then env  in
                 (match uu____77437 with
                  | (t,decls2) ->
                      let uu____77448 = encode_formula _else env  in
                      (match uu____77448 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____77460 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____77490 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l
           in
        f uu____77490  in
      let connectives =
        let uu____77520 =
          let uu____77545 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____77545)  in
        let uu____77588 =
          let uu____77615 =
            let uu____77640 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____77640)  in
          let uu____77683 =
            let uu____77710 =
              let uu____77737 =
                let uu____77762 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____77762)  in
              let uu____77805 =
                let uu____77832 =
                  let uu____77859 =
                    let uu____77884 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____77884)  in
                  [uu____77859;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.c_eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq3_op);
                  (FStar_Parser_Const.c_eq3_lid, h_equals_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____77832  in
              uu____77737 :: uu____77805  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____77710  in
          uu____77615 :: uu____77683  in
        uu____77520 :: uu____77588  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____78429 = encode_formula phi' env  in
            (match uu____78429 with
             | (phi2,decls) ->
                 let uu____78440 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____78440, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____78442 ->
            let uu____78449 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____78449 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____78488 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____78488 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____78500;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____78502;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____78504;
                 FStar_Syntax_Syntax.lbpos = uu____78505;_}::[]),e2)
            ->
            let uu____78532 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____78532 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____78585::(x,uu____78587)::(t,uu____78589)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____78656 = encode_term x env  in
                 (match uu____78656 with
                  | (x1,decls) ->
                      let uu____78667 = encode_term t env  in
                      (match uu____78667 with
                       | (t1,decls') ->
                           let uu____78678 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____78678, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____78681)::(msg,uu____78683)::(phi2,uu____78685)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____78752 =
                   let uu____78757 =
                     let uu____78758 = FStar_Syntax_Subst.compress r  in
                     uu____78758.FStar_Syntax_Syntax.n  in
                   let uu____78761 =
                     let uu____78762 = FStar_Syntax_Subst.compress msg  in
                     uu____78762.FStar_Syntax_Syntax.n  in
                   (uu____78757, uu____78761)  in
                 (match uu____78752 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____78771))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____78782 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____78789)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____78824 when head_redex env head2 ->
                 let uu____78839 = whnf env phi1  in
                 encode_formula uu____78839 env
             | uu____78840 ->
                 let uu____78855 = encode_term phi1 env  in
                 (match uu____78855 with
                  | (tt,decls) ->
                      let tt1 =
                        let uu____78867 =
                          let uu____78869 =
                            FStar_Range.use_range
                              tt.FStar_SMTEncoding_Term.rng
                             in
                          let uu____78870 =
                            FStar_Range.use_range
                              phi1.FStar_Syntax_Syntax.pos
                             in
                          FStar_Range.rng_included uu____78869 uu____78870
                           in
                        if uu____78867
                        then tt
                        else
                          (let uu___2246_78874 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___2246_78874.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___2246_78874.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      let uu____78875 = FStar_SMTEncoding_Term.mk_Valid tt1
                         in
                      (uu____78875, decls)))
        | uu____78876 ->
            let uu____78877 = encode_term phi1 env  in
            (match uu____78877 with
             | (tt,decls) ->
                 let tt1 =
                   let uu____78889 =
                     let uu____78891 =
                       FStar_Range.use_range tt.FStar_SMTEncoding_Term.rng
                        in
                     let uu____78892 =
                       FStar_Range.use_range phi1.FStar_Syntax_Syntax.pos  in
                     FStar_Range.rng_included uu____78891 uu____78892  in
                   if uu____78889
                   then tt
                   else
                     (let uu___2254_78896 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___2254_78896.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___2254_78896.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 let uu____78897 = FStar_SMTEncoding_Term.mk_Valid tt1  in
                 (uu____78897, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____78941 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____78941 with
        | (vars,guards,env2,decls,uu____78980) ->
            let uu____78993 = encode_smt_patterns ps env2  in
            (match uu____78993 with
             | (pats,decls') ->
                 let uu____79030 = encode_formula body env2  in
                 (match uu____79030 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____79062;
                             FStar_SMTEncoding_Term.rng = uu____79063;_}::[])::[]
                            when
                            let uu____79083 =
                              FStar_Ident.text_of_lid
                                FStar_Parser_Const.guard_free
                               in
                            uu____79083 = gf -> []
                        | uu____79086 -> guards  in
                      let uu____79091 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____79091, body1,
                        (FStar_List.append decls
                           (FStar_List.append decls' decls'')))))
         in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi  in
       let uu____79102 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____79102 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____79111 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____79217  ->
                     match uu____79217 with
                     | (l,uu____79242) -> FStar_Ident.lid_equals op l))
              in
           (match uu____79111 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____79311,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____79403 = encode_q_body env vars pats body  in
             match uu____79403 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____79448 =
                     let uu____79459 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____79459)  in
                   FStar_SMTEncoding_Term.mkForall
                     phi1.FStar_Syntax_Syntax.pos uu____79448
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____79490 = encode_q_body env vars pats body  in
             match uu____79490 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____79534 =
                   let uu____79535 =
                     let uu____79546 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____79546)  in
                   FStar_SMTEncoding_Term.mkExists
                     phi1.FStar_Syntax_Syntax.pos uu____79535
                    in
                 (uu____79534, decls))))
