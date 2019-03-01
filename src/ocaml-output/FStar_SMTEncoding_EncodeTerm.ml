open Prims
let mkForall_fuel' :
  'Auu____71245 .
    Prims.string ->
      FStar_Range.range ->
        'Auu____71245 ->
          (FStar_SMTEncoding_Term.pat Prims.list Prims.list *
            FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term) ->
            FStar_SMTEncoding_Term.term
  =
  fun mname  ->
    fun r  ->
      fun n1  ->
        fun uu____71276  ->
          match uu____71276 with
          | (pats,vars,body) ->
              let fallback uu____71304 =
                FStar_SMTEncoding_Term.mkForall r (pats, vars, body)  in
              let uu____71309 = FStar_Options.unthrottle_inductives ()  in
              if uu____71309
              then fallback ()
              else
                (let uu____71314 =
                   FStar_SMTEncoding_Env.fresh_fvar mname "f"
                     FStar_SMTEncoding_Term.Fuel_sort
                    in
                 match uu____71314 with
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
                               | uu____71354 -> p))
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
                                 let uu____71375 = add_fuel1 guards  in
                                 FStar_SMTEncoding_Util.mk_and_l uu____71375
                             | uu____71378 ->
                                 let uu____71379 = add_fuel1 [guard]  in
                                 FStar_All.pipe_right uu____71379
                                   FStar_List.hd
                              in
                           FStar_SMTEncoding_Util.mkImp (guard1, body')
                       | uu____71384 -> body  in
                     let vars1 =
                       let uu____71396 =
                         FStar_SMTEncoding_Term.mk_fv
                           (fsym, FStar_SMTEncoding_Term.Fuel_sort)
                          in
                       uu____71396 :: vars  in
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
      | FStar_Syntax_Syntax.Tm_arrow uu____71460 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____71476 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____71484 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____71486 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____71500 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____71520 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____71523 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____71523 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____71542;
             FStar_Syntax_Syntax.vars = uu____71543;_},uu____71544)
          ->
          let uu____71569 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____71569 FStar_Option.isNone
      | uu____71587 -> false
  
let (head_redex :
  FStar_SMTEncoding_Env.env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____71601 =
        let uu____71602 = FStar_Syntax_Util.un_uinst t  in
        uu____71602.FStar_Syntax_Syntax.n  in
      match uu____71601 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____71606,uu____71607,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___630_71632  ->
                  match uu___630_71632 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____71635 -> false)
               rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____71638 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____71638 FStar_Option.isSome
      | uu____71656 -> false
  
let (whnf :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____71669 = head_normal env t  in
      if uu____71669
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
    let uu____71691 =
      let uu____71692 = FStar_Syntax_Syntax.null_binder t  in [uu____71692]
       in
    let uu____71711 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    FStar_Syntax_Util.abs uu____71691 uu____71711
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
                let uu____71733 = FStar_SMTEncoding_Term.fv_sort var  in
                match uu____71733 with
                | FStar_SMTEncoding_Term.Fuel_sort  ->
                    let uu____71734 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____71734
                | s ->
                    let uu____71737 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____71737) e)
  
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
          let uu____71793 =
            let uu____71799 =
              let uu____71801 = FStar_Util.string_of_int arity  in
              let uu____71803 = FStar_Util.string_of_int n_args  in
              FStar_Util.format3
                "Head symbol %s expects at least %s arguments; got only %s"
                head1 uu____71801 uu____71803
               in
            (FStar_Errors.Fatal_SMTEncodingArityMismatch, uu____71799)  in
          FStar_Errors.raise_error uu____71793 rng
  
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
                  (let uu____71862 = FStar_Util.first_N arity args  in
                   match uu____71862 with
                   | (args1,rest) ->
                       let head3 =
                         FStar_SMTEncoding_Util.mkApp' (head2, args1)  in
                       mk_Apply_args head3 rest)
                else
                  (let uu____71886 =
                     FStar_SMTEncoding_Term.op_to_string head2  in
                   raise_arity_mismatch uu____71886 arity n_args rng)
  
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
          let uu____71913 = FStar_SMTEncoding_Env.force_thunk fvb  in
          mk_Apply_args uu____71913 args
        else
          maybe_curry_app rng
            (FStar_Util.Inl
               (FStar_SMTEncoding_Term.Var (fvb.FStar_SMTEncoding_Env.smt_id)))
            fvb.FStar_SMTEncoding_Env.smt_arity args
  
let (is_app : FStar_SMTEncoding_Term.op -> Prims.bool) =
  fun uu___631_71922  ->
    match uu___631_71922 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____71928 -> false
  
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
                       FStar_SMTEncoding_Term.freevars = uu____71976;
                       FStar_SMTEncoding_Term.rng = uu____71977;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____72008) ->
              let uu____72018 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____72035 -> false) args (FStar_List.rev xs))
                 in
              if uu____72018
              then FStar_SMTEncoding_Env.tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____72042,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t  in
              let uu____72046 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____72054 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars
                           in
                        Prims.op_Negation uu____72054))
                 in
              if uu____72046
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____72061 -> FStar_Pervasives_Native.None  in
        check_partial_applications body (FStar_List.rev vars)
  
let check_pattern_vars :
  'Auu____72079 'Auu____72080 .
    FStar_SMTEncoding_Env.env_t ->
      (FStar_Syntax_Syntax.bv * 'Auu____72079) Prims.list ->
        (FStar_Syntax_Syntax.term * 'Auu____72080) Prims.list -> unit
  =
  fun env  ->
    fun vars  ->
      fun pats  ->
        let pats1 =
          FStar_All.pipe_right pats
            (FStar_List.map
               (fun uu____72138  ->
                  match uu____72138 with
                  | (x,uu____72144) ->
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
              let uu____72152 = FStar_Syntax_Free.names hd1  in
              FStar_List.fold_left
                (fun out  ->
                   fun x  ->
                     let uu____72164 = FStar_Syntax_Free.names x  in
                     FStar_Util.set_union out uu____72164) uu____72152 tl1
               in
            let uu____72167 =
              FStar_All.pipe_right vars
                (FStar_Util.find_opt
                   (fun uu____72194  ->
                      match uu____72194 with
                      | (b,uu____72201) ->
                          let uu____72202 = FStar_Util.set_mem b pat_vars  in
                          Prims.op_Negation uu____72202))
               in
            (match uu____72167 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some (x,uu____72209) ->
                 let pos =
                   FStar_List.fold_left
                     (fun out  ->
                        fun t  ->
                          FStar_Range.union_ranges out
                            t.FStar_Syntax_Syntax.pos)
                     hd1.FStar_Syntax_Syntax.pos tl1
                    in
                 let uu____72223 =
                   let uu____72229 =
                     let uu____72231 = FStar_Syntax_Print.bv_to_string x  in
                     FStar_Util.format1
                       "SMT pattern misses at least one bound variable: %s"
                       uu____72231
                      in
                   (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                     uu____72229)
                    in
                 FStar_Errors.log_issue pos uu____72223)
  
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
        | FStar_Syntax_Syntax.Tm_arrow uu____72517 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____72532 ->
            let uu____72539 = FStar_Syntax_Util.unrefine t1  in
            aux true uu____72539
        | uu____72541 ->
            if norm1
            then let uu____72543 = whnf env t1  in aux false uu____72543
            else
              (let uu____72547 =
                 let uu____72549 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let uu____72551 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____72549 uu____72551
                  in
               failwith uu____72547)
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
    | FStar_Syntax_Syntax.Tm_refine (bv,uu____72593) ->
        let uu____72598 =
          curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort  in
        (match uu____72598 with
         | (args,res) ->
             (match args with
              | [] ->
                  let uu____72619 = FStar_Syntax_Syntax.mk_Total k1  in
                  ([], uu____72619)
              | uu____72626 -> (args, res)))
    | uu____72627 ->
        let uu____72628 = FStar_Syntax_Syntax.mk_Total k1  in
        ([], uu____72628)
  
let is_arithmetic_primitive :
  'Auu____72642 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____72642 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____72665::uu____72666::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____72670::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____72673 -> false
  
let (isInteger : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____72704 -> false
  
let (getInteger : FStar_Syntax_Syntax.term' -> Prims.int) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____72727 -> failwith "Expected an Integer term"
  
let is_BitVector_primitive :
  'Auu____72737 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____72737)
        Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____72779)::uu____72780::uu____72781::[]) ->
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
         fv,(sz_arg,uu____72832)::uu____72833::[]) ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____72870 -> false
  
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
          let uu____73194 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue  in
          (uu____73194, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____73196 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse  in
          (uu____73196, [])
      | FStar_Const.Const_char c1 ->
          let uu____73199 =
            let uu____73200 =
              let uu____73208 =
                let uu____73211 =
                  let uu____73212 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1)
                     in
                  FStar_SMTEncoding_Term.boxInt uu____73212  in
                [uu____73211]  in
              ("FStar.Char.__char_of_int", uu____73208)  in
            FStar_SMTEncoding_Util.mkApp uu____73200  in
          (uu____73199, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____73230 =
            let uu____73231 = FStar_SMTEncoding_Util.mkInteger i  in
            FStar_SMTEncoding_Term.boxInt uu____73231  in
          (uu____73230, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.FStar_SMTEncoding_Env.tcenv).FStar_TypeChecker_Env.dsenv
              repr sw FStar_Range.dummyRange
             in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____73252) ->
          let uu____73255 =
            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.string_const s
             in
          (uu____73255, [])
      | FStar_Const.Const_range uu____73256 ->
          let uu____73257 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          (uu____73257, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | FStar_Const.Const_real r ->
          let uu____73260 =
            let uu____73261 = FStar_SMTEncoding_Util.mkReal r  in
            FStar_SMTEncoding_Term.boxReal uu____73261  in
          (uu____73260, [])
      | c1 ->
          let uu____73263 =
            let uu____73265 = FStar_Syntax_Print.const_to_string c1  in
            FStar_Util.format1 "Unhandled constant: %s" uu____73265  in
          failwith uu____73263

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
        (let uu____73294 =
           FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
             FStar_Options.Medium
            in
         if uu____73294
         then
           let uu____73297 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____73297
         else ());
        (let uu____73303 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____73385  ->
                   fun b  ->
                     match uu____73385 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____73450 =
                           let x = FStar_Pervasives_Native.fst b  in
                           let uu____73466 =
                             FStar_SMTEncoding_Env.gen_term_var env1 x  in
                           match uu____73466 with
                           | (xxsym,xx,env') ->
                               let uu____73491 =
                                 let uu____73496 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____73496 env1
                                   xx
                                  in
                               (match uu____73491 with
                                | (guard_x_t,decls') ->
                                    let uu____73511 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xxsym,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    (uu____73511, guard_x_t, env', decls', x))
                            in
                         (match uu____73450 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____73303 with
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
          let uu____73611 = encode_term t env  in
          match uu____73611 with
          | (t1,decls) ->
              let uu____73622 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____73622, decls)

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
          let uu____73633 = encode_term t env  in
          match uu____73633 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____73648 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____73648, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____73650 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____73650, decls))

and (encode_arith_term :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____73656 = encode_args args_e env  in
        match uu____73656 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____73675 -> failwith "Impossible"  in
            let unary unbox arg_tms1 =
              let uu____73697 = FStar_List.hd arg_tms1  in unbox uu____73697
               in
            let binary unbox arg_tms1 =
              let uu____73722 =
                let uu____73723 = FStar_List.hd arg_tms1  in
                unbox uu____73723  in
              let uu____73724 =
                let uu____73725 =
                  let uu____73726 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____73726  in
                unbox uu____73725  in
              (uu____73722, uu____73724)  in
            let mk_default uu____73734 =
              let uu____73735 =
                FStar_SMTEncoding_Env.lookup_free_var_sym env
                  head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____73735 with
              | (fname,fuel_args,arity) ->
                  let args = FStar_List.append fuel_args arg_tms  in
                  maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity
                    args
               in
            let mk_l box op mk_args ts =
              let uu____73824 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____73824
              then
                let uu____73827 =
                  let uu____73828 = mk_args ts  in op uu____73828  in
                FStar_All.pipe_right uu____73827 box
              else mk_default ()  in
            let mk_nl box unbox nm op ts =
              let uu____73886 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____73886
              then
                let uu____73889 = binary unbox ts  in
                match uu____73889 with
                | (t1,t2) ->
                    let uu____73896 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____73896 box
              else
                (let uu____73902 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____73902
                 then
                   let uu____73905 =
                     let uu____73906 = binary unbox ts  in op uu____73906  in
                   FStar_All.pipe_right uu____73905 box
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
            let uu____74341 =
              let uu____74351 =
                FStar_List.tryFind
                  (fun uu____74375  ->
                     match uu____74375 with
                     | (l,uu____74386) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____74351 FStar_Util.must  in
            (match uu____74341 with
             | (uu____74430,op) ->
                 let uu____74442 = op arg_tms  in (uu____74442, decls))

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
        let uu____74458 = FStar_List.hd args_e  in
        match uu____74458 with
        | (tm_sz,uu____74474) ->
            let uu____74483 = uu____74458  in
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let t_decls1 = FStar_SMTEncoding_Term.mkBvConstructor sz  in
              FStar_SMTEncoding_Term.mk_decls "" sz_key t_decls1 []  in
            let uu____74494 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____74520::(sz_arg,uu____74522)::uu____74523::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____74590 =
                    let uu____74591 = FStar_List.tail args_e  in
                    FStar_List.tail uu____74591  in
                  let uu____74618 =
                    let uu____74622 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____74622  in
                  (uu____74590, uu____74618)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____74629::(sz_arg,uu____74631)::uu____74632::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____74699 =
                    let uu____74701 =
                      FStar_Syntax_Print.term_to_string sz_arg  in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____74701
                     in
                  failwith uu____74699
              | uu____74711 ->
                  let uu____74726 = FStar_List.tail args_e  in
                  (uu____74726, FStar_Pervasives_Native.None)
               in
            (match uu____74494 with
             | (arg_tms,ext_sz) ->
                 let uu____74753 = encode_args arg_tms env  in
                 (match uu____74753 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____74774 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____74786 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____74786  in
                      let unary_arith arg_tms2 =
                        let uu____74797 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____74797  in
                      let binary arg_tms2 =
                        let uu____74812 =
                          let uu____74813 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____74813
                           in
                        let uu____74814 =
                          let uu____74815 =
                            let uu____74816 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____74816  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____74815
                           in
                        (uu____74812, uu____74814)  in
                      let binary_arith arg_tms2 =
                        let uu____74833 =
                          let uu____74834 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____74834
                           in
                        let uu____74835 =
                          let uu____74836 =
                            let uu____74837 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____74837  in
                          FStar_SMTEncoding_Term.unboxInt uu____74836  in
                        (uu____74833, uu____74835)  in
                      let mk_bv op mk_args resBox ts =
                        let uu____74895 =
                          let uu____74896 = mk_args ts  in op uu____74896  in
                        FStar_All.pipe_right uu____74895 resBox  in
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
                        let uu____75028 =
                          let uu____75033 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____75033  in
                        let uu____75042 =
                          let uu____75047 =
                            let uu____75049 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____75049  in
                          FStar_SMTEncoding_Term.boxBitVec uu____75047  in
                        mk_bv uu____75028 unary uu____75042 arg_tms2  in
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
                      let uu____75289 =
                        let uu____75299 =
                          FStar_List.tryFind
                            (fun uu____75323  ->
                               match uu____75323 with
                               | (l,uu____75334) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____75299 FStar_Util.must  in
                      (match uu____75289 with
                       | (uu____75380,op) ->
                           let uu____75392 = op arg_tms1  in
                           (uu____75392, (FStar_List.append sz_decls decls)))))

and (encode_deeply_embedded_quantifier :
  FStar_Syntax_Syntax.term ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let env1 =
        let uu___1170_75402 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___1170_75402.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___1170_75402.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___1170_75402.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___1170_75402.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___1170_75402.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___1170_75402.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name =
            (uu___1170_75402.FStar_SMTEncoding_Env.use_zfuel_name);
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___1170_75402.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___1170_75402.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier = true;
          FStar_SMTEncoding_Env.global_cache =
            (uu___1170_75402.FStar_SMTEncoding_Env.global_cache)
        }  in
      let uu____75404 = encode_term t env1  in
      match uu____75404 with
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
               (uu____75430,{
                              FStar_SMTEncoding_Term.tm =
                                FStar_SMTEncoding_Term.FreeV uu____75431;
                              FStar_SMTEncoding_Term.freevars = uu____75432;
                              FStar_SMTEncoding_Term.rng = uu____75433;_}::
                {
                  FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV
                    uu____75434;
                  FStar_SMTEncoding_Term.freevars = uu____75435;
                  FStar_SMTEncoding_Term.rng = uu____75436;_}::[])
               ->
               (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                  (FStar_Errors.Warning_QuantifierWithoutPattern,
                    "Not encoding deeply embedded, unguarded quantifier to SMT");
                (tm, decls))
           | uu____75482 ->
               let uu____75483 = encode_formula t env1  in
               (match uu____75483 with
                | (phi,decls') ->
                    let interp =
                      match vars with
                      | [] ->
                          let uu____75503 =
                            let uu____75508 =
                              FStar_SMTEncoding_Term.mk_Valid tm  in
                            (uu____75508, phi)  in
                          FStar_SMTEncoding_Util.mkIff uu____75503
                      | uu____75509 ->
                          let uu____75510 =
                            let uu____75521 =
                              let uu____75522 =
                                let uu____75527 =
                                  FStar_SMTEncoding_Term.mk_Valid tm  in
                                (uu____75527, phi)  in
                              FStar_SMTEncoding_Util.mkIff uu____75522  in
                            ([[valid_tm]], vars, uu____75521)  in
                          FStar_SMTEncoding_Term.mkForall
                            t.FStar_Syntax_Syntax.pos uu____75510
                       in
                    let ax =
                      let uu____75537 =
                        let uu____75545 =
                          let uu____75547 =
                            FStar_Util.digest_of_string tkey_hash  in
                          Prims.op_Hat "l_quant_interp_" uu____75547  in
                        (interp,
                          (FStar_Pervasives_Native.Some
                             "Interpretation of deeply embedded quantifier"),
                          uu____75545)
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____75537  in
                    let uu____75553 =
                      let uu____75554 =
                        let uu____75557 =
                          FStar_SMTEncoding_Term.mk_decls "" tkey_hash 
                            [ax] (FStar_List.append decls decls')
                           in
                        FStar_List.append decls' uu____75557  in
                      FStar_List.append decls uu____75554  in
                    (tm, uu____75553)))

and (encode_term :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____75569 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____75569
       then
         let uu____75574 = FStar_Syntax_Print.tag_of_term t  in
         let uu____75576 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____75578 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____75574 uu____75576
           uu____75578
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____75587 ->
           let uu____75610 =
             let uu____75612 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____75615 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____75617 = FStar_Syntax_Print.term_to_string t0  in
             let uu____75619 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____75612
               uu____75615 uu____75617 uu____75619
              in
           failwith uu____75610
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____75626 =
             let uu____75628 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____75631 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____75633 = FStar_Syntax_Print.term_to_string t0  in
             let uu____75635 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____75628
               uu____75631 uu____75633 uu____75635
              in
           failwith uu____75626
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let e = FStar_Syntax_Util.unfold_lazy i  in
           ((let uu____75645 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____75645
             then
               let uu____75650 = FStar_Syntax_Print.term_to_string t0  in
               let uu____75652 = FStar_Syntax_Print.term_to_string e  in
               FStar_Util.print2 ">> Unfolded (%s) ~> (%s)\n" uu____75650
                 uu____75652
             else ());
            encode_term e env)
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____75658 =
             let uu____75660 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____75660
              in
           failwith uu____75658
       | FStar_Syntax_Syntax.Tm_ascribed (t1,(k,uu____75669),uu____75670) ->
           let uu____75719 =
             match k with
             | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
             | uu____75729 -> false  in
           if uu____75719
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t1 env
       | FStar_Syntax_Syntax.Tm_quoted (qt,uu____75747) ->
           let tv =
             let uu____75753 =
               let uu____75760 = FStar_Reflection_Basic.inspect_ln qt  in
               FStar_Syntax_Embeddings.embed
                 FStar_Reflection_Embeddings.e_term_view uu____75760
                in
             uu____75753 t.FStar_Syntax_Syntax.pos
               FStar_Pervasives_Native.None
               FStar_Syntax_Embeddings.id_norm_cb
              in
           ((let uu____75787 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____75787
             then
               let uu____75792 = FStar_Syntax_Print.term_to_string t0  in
               let uu____75794 = FStar_Syntax_Print.term_to_string tv  in
               FStar_Util.print2 ">> Inspected (%s) ~> (%s)\n" uu____75792
                 uu____75794
             else ());
            (let t1 =
               let uu____75802 =
                 let uu____75813 = FStar_Syntax_Syntax.as_arg tv  in
                 [uu____75813]  in
               FStar_Syntax_Util.mk_app
                 (FStar_Reflection_Data.refl_constant_term
                    FStar_Reflection_Data.fstar_refl_pack_ln) uu____75802
                in
             encode_term t1 env))
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_pattern uu____75839) ->
           encode_term t1
             (let uu___1242_75857 = env  in
              {
                FStar_SMTEncoding_Env.bvar_bindings =
                  (uu___1242_75857.FStar_SMTEncoding_Env.bvar_bindings);
                FStar_SMTEncoding_Env.fvar_bindings =
                  (uu___1242_75857.FStar_SMTEncoding_Env.fvar_bindings);
                FStar_SMTEncoding_Env.depth =
                  (uu___1242_75857.FStar_SMTEncoding_Env.depth);
                FStar_SMTEncoding_Env.tcenv =
                  (uu___1242_75857.FStar_SMTEncoding_Env.tcenv);
                FStar_SMTEncoding_Env.warn =
                  (uu___1242_75857.FStar_SMTEncoding_Env.warn);
                FStar_SMTEncoding_Env.nolabels =
                  (uu___1242_75857.FStar_SMTEncoding_Env.nolabels);
                FStar_SMTEncoding_Env.use_zfuel_name =
                  (uu___1242_75857.FStar_SMTEncoding_Env.use_zfuel_name);
                FStar_SMTEncoding_Env.encode_non_total_function_typ =
                  (uu___1242_75857.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                FStar_SMTEncoding_Env.current_module_name =
                  (uu___1242_75857.FStar_SMTEncoding_Env.current_module_name);
                FStar_SMTEncoding_Env.encoding_quantifier = false;
                FStar_SMTEncoding_Env.global_cache =
                  (uu___1242_75857.FStar_SMTEncoding_Env.global_cache)
              })
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____75860) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = FStar_SMTEncoding_Env.lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____75868 = head_redex env t  in
           if uu____75868
           then let uu____75875 = whnf env t  in encode_term uu____75875 env
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
              let uu____75882 =
                if
                  fvb.FStar_SMTEncoding_Env.smt_arity > (Prims.parse_int "0")
                then
                  match tok.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.FreeV uu____75906 ->
                      let sym_name =
                        let uu____75917 =
                          FStar_Util.digest_of_string tkey_hash  in
                        Prims.op_Hat "@kick_partial_app_" uu____75917  in
                      let uu____75920 =
                        let uu____75923 =
                          let uu____75924 =
                            let uu____75932 =
                              FStar_SMTEncoding_Term.kick_partial_app tok  in
                            (uu____75932,
                              (FStar_Pervasives_Native.Some
                                 "kick_partial_app"), sym_name)
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____75924  in
                        [uu____75923]  in
                      (uu____75920, sym_name)
                  | FStar_SMTEncoding_Term.App (uu____75939,[]) ->
                      let sym_name =
                        let uu____75944 =
                          FStar_Util.digest_of_string tkey_hash  in
                        Prims.op_Hat "@kick_partial_app_" uu____75944  in
                      let uu____75947 =
                        let uu____75950 =
                          let uu____75951 =
                            let uu____75959 =
                              FStar_SMTEncoding_Term.kick_partial_app tok  in
                            (uu____75959,
                              (FStar_Pervasives_Native.Some
                                 "kick_partial_app"), sym_name)
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____75951  in
                        [uu____75950]  in
                      (uu____75947, sym_name)
                  | uu____75966 -> ([], "")
                else ([], "")  in
              match uu____75882 with
              | (aux_decls,sym_name) ->
                  let uu____75989 =
                    if aux_decls = []
                    then
                      FStar_All.pipe_right []
                        FStar_SMTEncoding_Term.mk_decls_trivial
                    else
                      FStar_SMTEncoding_Term.mk_decls sym_name tkey_hash
                        aux_decls []
                     in
                  (tok, uu____75989))
       | FStar_Syntax_Syntax.Tm_type uu____75997 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____75999) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.FStar_SMTEncoding_Env.current_module_name
              in
           let uu____76029 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____76029 with
            | (binders1,res) ->
                let uu____76040 =
                  (env.FStar_SMTEncoding_Env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____76040
                then
                  let uu____76047 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____76047 with
                   | (vars,guards,env',decls,uu____76072) ->
                       let fsym =
                         let uu____76086 =
                           let uu____76092 =
                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                               module_name "f"
                              in
                           (uu____76092, FStar_SMTEncoding_Term.Term_sort)
                            in
                         FStar_SMTEncoding_Term.mk_fv uu____76086  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____76098 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___1296_76107 =
                              env.FStar_SMTEncoding_Env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___1296_76107.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___1296_76107.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___1296_76107.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___1296_76107.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___1296_76107.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___1296_76107.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___1296_76107.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___1296_76107.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___1296_76107.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___1296_76107.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___1296_76107.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___1296_76107.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___1296_76107.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___1296_76107.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___1296_76107.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___1296_76107.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___1296_76107.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___1296_76107.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___1296_76107.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___1296_76107.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___1296_76107.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___1296_76107.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___1296_76107.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___1296_76107.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___1296_76107.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___1296_76107.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___1296_76107.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___1296_76107.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___1296_76107.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___1296_76107.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___1296_76107.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___1296_76107.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___1296_76107.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___1296_76107.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___1296_76107.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___1296_76107.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___1296_76107.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___1296_76107.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___1296_76107.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___1296_76107.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___1296_76107.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___1296_76107.FStar_TypeChecker_Env.nbe)
                            }) res
                          in
                       (match uu____76098 with
                        | (pre_opt,res_t) ->
                            let uu____76119 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____76119 with
                             | (res_pred,decls') ->
                                 let uu____76130 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____76143 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____76143, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____76147 =
                                         encode_formula pre env'  in
                                       (match uu____76147 with
                                        | (guard,decls0) ->
                                            let uu____76160 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____76160, decls0))
                                    in
                                 (match uu____76130 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____76174 =
                                          let uu____76185 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____76185)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t.FStar_Syntax_Syntax.pos
                                          uu____76174
                                         in
                                      let cvars =
                                        let uu____76205 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____76205
                                          (FStar_List.filter
                                             (fun x  ->
                                                let uu____76224 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    x
                                                   in
                                                let uu____76226 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    fsym
                                                   in
                                                uu____76224 <> uu____76226))
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
                                        let uu____76248 =
                                          FStar_Util.digest_of_string
                                            tkey_hash
                                           in
                                        Prims.op_Hat "Tm_arrow_" uu____76248
                                         in
                                      let cvar_sorts =
                                        FStar_List.map
                                          FStar_SMTEncoding_Term.fv_sort
                                          cvars
                                         in
                                      let caption =
                                        let uu____76263 =
                                          FStar_Options.log_queries ()  in
                                        if uu____76263
                                        then
                                          let uu____76266 =
                                            let uu____76268 =
                                              FStar_TypeChecker_Normalize.term_to_string
                                                env.FStar_SMTEncoding_Env.tcenv
                                                t0
                                               in
                                            FStar_Util.replace_char
                                              uu____76268 10 32
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____76266
                                        else FStar_Pervasives_Native.None  in
                                      let tdecl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (tsym, cvar_sorts,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            caption)
                                         in
                                      let t1 =
                                        let uu____76281 =
                                          let uu____76289 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              cvars
                                             in
                                          (tsym, uu____76289)  in
                                        FStar_SMTEncoding_Util.mkApp
                                          uu____76281
                                         in
                                      let t_has_kind =
                                        FStar_SMTEncoding_Term.mk_HasType t1
                                          FStar_SMTEncoding_Term.mk_Term_type
                                         in
                                      let k_assumption =
                                        let a_name =
                                          Prims.op_Hat "kinding_" tsym  in
                                        let uu____76308 =
                                          let uu____76316 =
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              ([[t_has_kind]], cvars,
                                                t_has_kind)
                                             in
                                          (uu____76316,
                                            (FStar_Pervasives_Native.Some
                                               a_name), a_name)
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____76308
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
                                        let uu____76333 =
                                          let uu____76341 =
                                            let uu____76342 =
                                              let uu____76353 =
                                                let uu____76354 =
                                                  let uu____76359 =
                                                    let uu____76360 =
                                                      FStar_SMTEncoding_Term.mk_PreType
                                                        f
                                                       in
                                                    FStar_SMTEncoding_Term.mk_tester
                                                      "Tm_arrow" uu____76360
                                                     in
                                                  (f_has_t, uu____76359)  in
                                                FStar_SMTEncoding_Util.mkImp
                                                  uu____76354
                                                 in
                                              ([[f_has_t]], (fsym :: cvars),
                                                uu____76353)
                                               in
                                            let uu____76378 =
                                              mkForall_fuel module_name
                                                t0.FStar_Syntax_Syntax.pos
                                               in
                                            uu____76378 uu____76342  in
                                          (uu____76341,
                                            (FStar_Pervasives_Native.Some
                                               "pre-typing for functions"),
                                            (Prims.op_Hat module_name
                                               (Prims.op_Hat "_" a_name)))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____76333
                                         in
                                      let t_interp1 =
                                        let a_name =
                                          Prims.op_Hat "interpretation_" tsym
                                           in
                                        let uu____76401 =
                                          let uu____76409 =
                                            let uu____76410 =
                                              let uu____76421 =
                                                FStar_SMTEncoding_Util.mkIff
                                                  (f_has_t_z, t_interp)
                                                 in
                                              ([[f_has_t_z]], (fsym ::
                                                cvars), uu____76421)
                                               in
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              uu____76410
                                             in
                                          (uu____76409,
                                            (FStar_Pervasives_Native.Some
                                               a_name),
                                            (Prims.op_Hat module_name
                                               (Prims.op_Hat "_" a_name)))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____76401
                                         in
                                      let t_decls1 =
                                        [tdecl;
                                        k_assumption;
                                        pre_typing;
                                        t_interp1]  in
                                      let uu____76444 =
                                        let uu____76445 =
                                          let uu____76448 =
                                            let uu____76451 =
                                              FStar_SMTEncoding_Term.mk_decls
                                                tsym tkey_hash t_decls1
                                                (FStar_List.append decls
                                                   (FStar_List.append decls'
                                                      guard_decls))
                                               in
                                            FStar_List.append guard_decls
                                              uu____76451
                                             in
                                          FStar_List.append decls'
                                            uu____76448
                                           in
                                        FStar_List.append decls uu____76445
                                         in
                                      (t1, uu____76444)))))
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
                     let uu____76472 =
                       let uu____76480 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____76480,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"), a_name)
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____76472  in
                   let fsym =
                     FStar_SMTEncoding_Term.mk_fv
                       ("f", FStar_SMTEncoding_Term.Term_sort)
                      in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.op_Hat "pre_typing_" tsym  in
                     let uu____76493 =
                       let uu____76501 =
                         let uu____76502 =
                           let uu____76513 =
                             let uu____76514 =
                               let uu____76519 =
                                 let uu____76520 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____76520
                                  in
                               (f_has_t, uu____76519)  in
                             FStar_SMTEncoding_Util.mkImp uu____76514  in
                           ([[f_has_t]], [fsym], uu____76513)  in
                         let uu____76546 =
                           mkForall_fuel module_name
                             t0.FStar_Syntax_Syntax.pos
                            in
                         uu____76546 uu____76502  in
                       (uu____76501, (FStar_Pervasives_Native.Some a_name),
                         a_name)
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____76493  in
                   let uu____76563 =
                     FStar_All.pipe_right [tdecl; t_kinding; t_interp]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                      in
                   (t1, uu____76563)))
       | FStar_Syntax_Syntax.Tm_refine uu____76566 ->
           let uu____76573 =
             let uu____76578 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Env.Weak;
                 FStar_TypeChecker_Env.HNF;
                 FStar_TypeChecker_Env.EraseUniverses]
                 env.FStar_SMTEncoding_Env.tcenv t0
                in
             match uu____76578 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____76585;
                 FStar_Syntax_Syntax.vars = uu____76586;_} ->
                 let uu____76593 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____76593 with
                  | (b,f1) ->
                      let uu____76618 =
                        let uu____76619 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____76619  in
                      (uu____76618, f1))
             | uu____76634 -> failwith "impossible"  in
           (match uu____76573 with
            | (x,f) ->
                let uu____76646 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____76646 with
                 | (base_t,decls) ->
                     let uu____76657 =
                       FStar_SMTEncoding_Env.gen_term_var env x  in
                     (match uu____76657 with
                      | (x1,xtm,env') ->
                          let uu____76674 = encode_formula f env'  in
                          (match uu____76674 with
                           | (refinement,decls') ->
                               let uu____76685 =
                                 FStar_SMTEncoding_Env.fresh_fvar
                                   env.FStar_SMTEncoding_Env.current_module_name
                                   "f" FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____76685 with
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
                                      let uu____76713 =
                                        let uu____76724 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____76735 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____76724
                                          uu____76735
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____76713
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun y  ->
                                              (let uu____76789 =
                                                 FStar_SMTEncoding_Term.fv_name
                                                   y
                                                  in
                                               uu____76789 <> x1) &&
                                                (let uu____76793 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     y
                                                    in
                                                 uu____76793 <> fsym)))
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
                                      let uu____76829 =
                                        FStar_Util.digest_of_string tkey_hash
                                         in
                                      Prims.op_Hat "Tm_refine_" uu____76829
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
                                      let uu____76849 =
                                        let uu____76857 =
                                          FStar_List.map
                                            FStar_SMTEncoding_Util.mkFreeV
                                            cvars1
                                           in
                                        (tsym, uu____76857)  in
                                      FStar_SMTEncoding_Util.mkApp
                                        uu____76849
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
                                      let uu____76877 =
                                        let uu____76885 =
                                          let uu____76886 =
                                            let uu____76897 =
                                              FStar_SMTEncoding_Util.mkIff
                                                (t_haseq_ref, t_haseq_base)
                                               in
                                            ([[t_haseq_ref]], cvars1,
                                              uu____76897)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            t0.FStar_Syntax_Syntax.pos
                                            uu____76886
                                           in
                                        (uu____76885,
                                          (FStar_Pervasives_Native.Some
                                             (Prims.op_Hat "haseq for " tsym)),
                                          (Prims.op_Hat "haseq" tsym))
                                         in
                                      FStar_SMTEncoding_Util.mkAssume
                                        uu____76877
                                       in
                                    let t_kinding =
                                      let uu____76911 =
                                        let uu____76919 =
                                          FStar_SMTEncoding_Term.mkForall
                                            t0.FStar_Syntax_Syntax.pos
                                            ([[t_has_kind]], cvars1,
                                              t_has_kind)
                                           in
                                        (uu____76919,
                                          (FStar_Pervasives_Native.Some
                                             "refinement kinding"),
                                          (Prims.op_Hat "refinement_kinding_"
                                             tsym))
                                         in
                                      FStar_SMTEncoding_Util.mkAssume
                                        uu____76911
                                       in
                                    let t_interp =
                                      let uu____76933 =
                                        let uu____76941 =
                                          let uu____76942 =
                                            let uu____76953 =
                                              FStar_SMTEncoding_Util.mkIff
                                                (x_has_t, encoding)
                                               in
                                            ([[x_has_t]], (ffv :: xfv ::
                                              cvars1), uu____76953)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            t0.FStar_Syntax_Syntax.pos
                                            uu____76942
                                           in
                                        (uu____76941,
                                          (FStar_Pervasives_Native.Some
                                             "refinement_interpretation"),
                                          (Prims.op_Hat
                                             "refinement_interpretation_"
                                             tsym))
                                         in
                                      FStar_SMTEncoding_Util.mkAssume
                                        uu____76933
                                       in
                                    let t_decls1 =
                                      [tdecl; t_kinding; t_interp; t_haseq1]
                                       in
                                    let uu____76985 =
                                      let uu____76986 =
                                        let uu____76989 =
                                          FStar_SMTEncoding_Term.mk_decls
                                            tsym tkey_hash t_decls1
                                            (FStar_List.append decls decls')
                                           in
                                        FStar_List.append decls' uu____76989
                                         in
                                      FStar_List.append decls uu____76986  in
                                    (t1, uu____76985))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,uu____76993) ->
           let ttm =
             let uu____77011 =
               FStar_Syntax_Unionfind.uvar_id
                 uv.FStar_Syntax_Syntax.ctx_uvar_head
                in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____77011  in
           let uu____77013 =
             encode_term_pred FStar_Pervasives_Native.None
               uv.FStar_Syntax_Syntax.ctx_uvar_typ env ttm
              in
           (match uu____77013 with
            | (t_has_k,decls) ->
                let d =
                  let uu____77025 =
                    let uu____77033 =
                      let uu____77035 =
                        let uu____77037 =
                          let uu____77039 =
                            FStar_Syntax_Unionfind.uvar_id
                              uv.FStar_Syntax_Syntax.ctx_uvar_head
                             in
                          FStar_Util.string_of_int uu____77039  in
                        FStar_Util.format1 "uvar_typing_%s" uu____77037  in
                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                        uu____77035
                       in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____77033)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____77025  in
                let uu____77045 =
                  let uu____77046 =
                    FStar_All.pipe_right [d]
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append decls uu____77046  in
                (ttm, uu____77045))
       | FStar_Syntax_Syntax.Tm_app uu____77053 ->
           let uu____77070 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____77070 with
            | (head1,args_e) ->
                let uu____77117 =
                  let uu____77132 =
                    let uu____77133 = FStar_Syntax_Subst.compress head1  in
                    uu____77133.FStar_Syntax_Syntax.n  in
                  (uu____77132, args_e)  in
                (match uu____77117 with
                 | uu____77150 when head_redex env head1 ->
                     let uu____77165 = whnf env t  in
                     encode_term uu____77165 env
                 | uu____77166 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____77189 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_fvar fv,uu____77207) when
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
                       FStar_Syntax_Syntax.pos = uu____77229;
                       FStar_Syntax_Syntax.vars = uu____77230;_},uu____77231),uu____77232)
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
                       FStar_Syntax_Syntax.pos = uu____77258;
                       FStar_Syntax_Syntax.vars = uu____77259;_},uu____77260),
                    (v0,uu____77262)::(v1,uu____77264)::(v2,uu____77266)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____77337 = encode_term v0 env  in
                     (match uu____77337 with
                      | (v01,decls0) ->
                          let uu____77348 = encode_term v1 env  in
                          (match uu____77348 with
                           | (v11,decls1) ->
                               let uu____77359 = encode_term v2 env  in
                               (match uu____77359 with
                                | (v21,decls2) ->
                                    let uu____77370 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____77370,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(v0,uu____77373)::(v1,uu____77375)::(v2,uu____77377)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____77444 = encode_term v0 env  in
                     (match uu____77444 with
                      | (v01,decls0) ->
                          let uu____77455 = encode_term v1 env  in
                          (match uu____77455 with
                           | (v11,decls1) ->
                               let uu____77466 = encode_term v2 env  in
                               (match uu____77466 with
                                | (v21,decls2) ->
                                    let uu____77477 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____77477,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____77479)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____77515)::(rng,uu____77517)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____77568) ->
                     let e0 =
                       let uu____77590 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg
                         env.FStar_SMTEncoding_Env.tcenv head1 uu____77590
                        in
                     ((let uu____77600 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug
                              env.FStar_SMTEncoding_Env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____77600
                       then
                         let uu____77605 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____77605
                       else ());
                      (let e =
                         let uu____77613 =
                           let uu____77618 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____77619 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____77618
                             uu____77619
                            in
                         uu____77613 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____77630),(arg,uu____77632)::[]) ->
                     encode_term arg env
                 | uu____77667 ->
                     let uu____77682 = encode_args args_e env  in
                     (match uu____77682 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____77743 = encode_term head1 env  in
                            match uu____77743 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____77815 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____77815 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____77913  ->
                                                 fun uu____77914  ->
                                                   match (uu____77913,
                                                           uu____77914)
                                                   with
                                                   | ((bv,uu____77944),
                                                      (a,uu____77946)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____77976 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____77976
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____77977 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm
                                             in
                                          (match uu____77977 with
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
                                                 let uu____77994 =
                                                   let uu____78002 =
                                                     FStar_SMTEncoding_Term.mkForall
                                                       t0.FStar_Syntax_Syntax.pos
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____78011 =
                                                     let uu____78013 =
                                                       let uu____78015 =
                                                         FStar_SMTEncoding_Term.hash_of_term
                                                           app_tm
                                                          in
                                                       FStar_Util.digest_of_string
                                                         uu____78015
                                                        in
                                                     Prims.op_Hat
                                                       "partial_app_typing_"
                                                       uu____78013
                                                      in
                                                   (uu____78002,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____78011)
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____77994
                                                  in
                                               let uu____78021 =
                                                 let uu____78024 =
                                                   let uu____78027 =
                                                     let uu____78030 =
                                                       FStar_SMTEncoding_Term.mk_decls
                                                         "" tkey_hash
                                                         [e_typing]
                                                         (FStar_List.append
                                                            decls
                                                            (FStar_List.append
                                                               decls' decls''))
                                                        in
                                                     FStar_List.append
                                                       decls'' uu____78030
                                                      in
                                                   FStar_List.append decls'
                                                     uu____78027
                                                    in
                                                 FStar_List.append decls
                                                   uu____78024
                                                  in
                                               (app_tm, uu____78021))))
                             in
                          let encode_full_app fv =
                            let uu____78050 =
                              FStar_SMTEncoding_Env.lookup_free_var_sym env
                                fv
                               in
                            match uu____78050 with
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
                                   FStar_Syntax_Syntax.pos = uu____78093;
                                   FStar_Syntax_Syntax.vars = uu____78094;_},uu____78095)
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
                                   FStar_Syntax_Syntax.pos = uu____78102;
                                   FStar_Syntax_Syntax.vars = uu____78103;_},uu____78104)
                                ->
                                let uu____78109 =
                                  let uu____78110 =
                                    let uu____78115 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____78115
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____78110
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____78109
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____78145 =
                                  let uu____78146 =
                                    let uu____78151 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____78151
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____78146
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____78145
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____78180,(FStar_Util.Inl t1,uu____78182),uu____78183)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____78230,(FStar_Util.Inr c,uu____78232),uu____78233)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____78280 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____78301 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Env.Weak;
                                     FStar_TypeChecker_Env.HNF;
                                     FStar_TypeChecker_Env.EraseUniverses]
                                     env.FStar_SMTEncoding_Env.tcenv
                                     head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____78301
                                  in
                               let uu____78302 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____78302 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____78318;
                                            FStar_Syntax_Syntax.vars =
                                              uu____78319;_},uu____78320)
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
                                     | uu____78338 ->
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
           let uu____78417 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____78417 with
            | (bs1,body1,opening) ->
                let fallback uu____78440 =
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
                  let uu____78450 =
                    let uu____78451 =
                      FStar_SMTEncoding_Term.mk_fv
                        (f, FStar_SMTEncoding_Term.Term_sort)
                       in
                    FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV
                      uu____78451
                     in
                  let uu____78453 =
                    FStar_All.pipe_right [decl]
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  (uu____78450, uu____78453)  in
                let is_impure rc =
                  let uu____78463 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                      env.FStar_SMTEncoding_Env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____78463 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____78478 =
                          let uu____78491 =
                            FStar_TypeChecker_Env.get_range
                              env.FStar_SMTEncoding_Env.tcenv
                             in
                          FStar_TypeChecker_Util.new_implicit_var
                            "SMTEncoding codomain" uu____78491
                            env.FStar_SMTEncoding_Env.tcenv
                            FStar_Syntax_Util.ktype0
                           in
                        (match uu____78478 with
                         | (t1,uu____78494,uu____78495) -> t1)
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  let uu____78513 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                     in
                  if uu____78513
                  then
                    let uu____78518 = FStar_Syntax_Syntax.mk_Total res_typ
                       in
                    FStar_Pervasives_Native.Some uu____78518
                  else
                    (let uu____78521 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid
                        in
                     if uu____78521
                     then
                       let uu____78526 =
                         FStar_Syntax_Syntax.mk_GTotal res_typ  in
                       FStar_Pervasives_Native.Some uu____78526
                     else FStar_Pervasives_Native.None)
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____78534 =
                         let uu____78540 =
                           let uu____78542 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____78542
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____78540)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____78534);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____78547 =
                       (is_impure rc) &&
                         (let uu____78550 =
                            FStar_TypeChecker_Env.is_reifiable_rc
                              env.FStar_SMTEncoding_Env.tcenv rc
                             in
                          Prims.op_Negation uu____78550)
                        in
                     if uu____78547
                     then fallback ()
                     else
                       (let uu____78559 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____78559 with
                        | (vars,guards,envbody,decls,uu____78584) ->
                            let body2 =
                              let uu____78598 =
                                FStar_TypeChecker_Env.is_reifiable_rc
                                  env.FStar_SMTEncoding_Env.tcenv rc
                                 in
                              if uu____78598
                              then
                                FStar_TypeChecker_Util.reify_body
                                  env.FStar_SMTEncoding_Env.tcenv body1
                              else body1  in
                            let uu____78603 = encode_term body2 envbody  in
                            (match uu____78603 with
                             | (body3,decls') ->
                                 let uu____78614 =
                                   let uu____78623 = codomain_eff rc  in
                                   match uu____78623 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____78642 = encode_term tfun env
                                          in
                                       (match uu____78642 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____78614 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____78676 =
                                          let uu____78687 =
                                            let uu____78688 =
                                              let uu____78693 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____78693, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____78688
                                             in
                                          ([], vars, uu____78687)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t0.FStar_Syntax_Syntax.pos
                                          uu____78676
                                         in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body
                                         in
                                      let uu____78701 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            (cvars, key_body)
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____78717 =
                                              let uu____78720 =
                                                let uu____78731 =
                                                  FStar_SMTEncoding_Term.free_variables
                                                    t1
                                                   in
                                                FStar_List.append uu____78731
                                                  cvars
                                                 in
                                              FStar_Util.remove_dups
                                                FStar_SMTEncoding_Term.fv_eq
                                                uu____78720
                                               in
                                            let uu____78758 =
                                              FStar_SMTEncoding_Util.mkAnd
                                                (key_body, t1)
                                               in
                                            (uu____78717, uu____78758)
                                         in
                                      (match uu____78701 with
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
                                           let uu____78780 =
                                             is_an_eta_expansion env vars
                                               body3
                                              in
                                           (match uu____78780 with
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
                                                  let uu____78796 =
                                                    FStar_Util.digest_of_string
                                                      tkey_hash
                                                     in
                                                  Prims.op_Hat "Tm_abs_"
                                                    uu____78796
                                                   in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None)
                                                   in
                                                let f =
                                                  let uu____78805 =
                                                    let uu____78813 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    (fsym, uu____78813)  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____78805
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
                                                      let uu____78830 =
                                                        let uu____78831 =
                                                          let uu____78839 =
                                                            FStar_SMTEncoding_Term.mkForall
                                                              t0.FStar_Syntax_Syntax.pos
                                                              ([[f]], cvars1,
                                                                f_has_t)
                                                             in
                                                          (uu____78839,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name)
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____78831
                                                         in
                                                      [uu____78830]
                                                   in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.op_Hat
                                                      "interpretation_" fsym
                                                     in
                                                  let uu____78854 =
                                                    let uu____78862 =
                                                      let uu____78863 =
                                                        let uu____78874 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3)
                                                           in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____78874)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        t0.FStar_Syntax_Syntax.pos
                                                        uu____78863
                                                       in
                                                    (uu____78862,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____78854
                                                   in
                                                let f_decls =
                                                  FStar_List.append (fdecl ::
                                                    typing_f) [interp_f]
                                                   in
                                                let uu____78888 =
                                                  let uu____78889 =
                                                    let uu____78892 =
                                                      let uu____78895 =
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
                                                        decls'' uu____78895
                                                       in
                                                    FStar_List.append decls'
                                                      uu____78892
                                                     in
                                                  FStar_List.append decls
                                                    uu____78889
                                                   in
                                                (f, uu____78888))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____78898,{
                           FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                             uu____78899;
                           FStar_Syntax_Syntax.lbunivs = uu____78900;
                           FStar_Syntax_Syntax.lbtyp = uu____78901;
                           FStar_Syntax_Syntax.lbeff = uu____78902;
                           FStar_Syntax_Syntax.lbdef = uu____78903;
                           FStar_Syntax_Syntax.lbattrs = uu____78904;
                           FStar_Syntax_Syntax.lbpos = uu____78905;_}::uu____78906),uu____78907)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____78941;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____78943;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____78945;
                FStar_Syntax_Syntax.lbpos = uu____78946;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____78973 ->
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
              let uu____79045 =
                let uu____79050 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____79050 env  in
              match uu____79045 with
              | (ee1,decls1) ->
                  let uu____79075 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____79075 with
                   | (xs,e21) ->
                       let uu____79100 = FStar_List.hd xs  in
                       (match uu____79100 with
                        | (x1,uu____79118) ->
                            let env' =
                              FStar_SMTEncoding_Env.push_term_var env x1 ee1
                               in
                            let uu____79124 = encode_body e21 env'  in
                            (match uu____79124 with
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
            let uu____79154 =
              let uu____79162 =
                let uu____79163 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____79163  in
              FStar_SMTEncoding_Env.gen_term_var env uu____79162  in
            match uu____79154 with
            | (scrsym,scr',env1) ->
                let uu____79173 = encode_term e env1  in
                (match uu____79173 with
                 | (scr,decls) ->
                     let uu____79184 =
                       let encode_branch b uu____79213 =
                         match uu____79213 with
                         | (else_case,decls1) ->
                             let uu____79232 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____79232 with
                              | (p,w,br) ->
                                  let uu____79258 = encode_pat env1 p  in
                                  (match uu____79258 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____79295  ->
                                                   match uu____79295 with
                                                   | (x,t) ->
                                                       FStar_SMTEncoding_Env.push_term_var
                                                         env2 x t) env1)
                                          in
                                       let uu____79302 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____79324 =
                                               encode_term w1 env2  in
                                             (match uu____79324 with
                                              | (w2,decls2) ->
                                                  let uu____79337 =
                                                    let uu____79338 =
                                                      let uu____79343 =
                                                        let uu____79344 =
                                                          let uu____79349 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____79349)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____79344
                                                         in
                                                      (guard, uu____79343)
                                                       in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____79338
                                                     in
                                                  (uu____79337, decls2))
                                          in
                                       (match uu____79302 with
                                        | (guard1,decls2) ->
                                            let uu____79364 =
                                              encode_br br env2  in
                                            (match uu____79364 with
                                             | (br1,decls3) ->
                                                 let uu____79377 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____79377,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____79184 with
                      | (match_tm,decls1) ->
                          let uu____79398 =
                            let uu____79399 =
                              let uu____79410 =
                                let uu____79417 =
                                  let uu____79422 =
                                    FStar_SMTEncoding_Term.mk_fv
                                      (scrsym,
                                        FStar_SMTEncoding_Term.Term_sort)
                                     in
                                  (uu____79422, scr)  in
                                [uu____79417]  in
                              (uu____79410, match_tm)  in
                            FStar_SMTEncoding_Term.mkLet' uu____79399
                              FStar_Range.dummyRange
                             in
                          (uu____79398, decls1)))

and (encode_pat :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.pat -> (FStar_SMTEncoding_Env.env_t * pattern))
  =
  fun env  ->
    fun pat  ->
      (let uu____79445 =
         FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
           FStar_Options.Medium
          in
       if uu____79445
       then
         let uu____79448 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____79448
       else ());
      (let uu____79453 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____79453 with
       | (vars,pat_term) ->
           let uu____79470 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____79512  ->
                     fun v1  ->
                       match uu____79512 with
                       | (env1,vars1) ->
                           let uu____79548 =
                             FStar_SMTEncoding_Env.gen_term_var env1 v1  in
                           (match uu____79548 with
                            | (xx,uu____79567,env2) ->
                                let uu____79571 =
                                  let uu____79578 =
                                    let uu____79583 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xx,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    (v1, uu____79583)  in
                                  uu____79578 :: vars1  in
                                (env2, uu____79571))) (env, []))
              in
           (match uu____79470 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____79638 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____79639 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____79640 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____79648 = encode_const c env1  in
                      (match uu____79648 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____79656::uu____79657 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____79661 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon
                            env1.FStar_SMTEncoding_Env.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____79684 =
                          FStar_TypeChecker_Env.datacons_of_typ
                            env1.FStar_SMTEncoding_Env.tcenv tc_name
                           in
                        match uu____79684 with
                        | (uu____79692,uu____79693::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____79698 ->
                            FStar_SMTEncoding_Env.mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____79734  ->
                                  match uu____79734 with
                                  | (arg,uu____79744) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____79753 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____79753))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____79785) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____79816 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____79841 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____79887  ->
                                  match uu____79887 with
                                  | (arg,uu____79903) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____79912 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____79912))
                         in
                      FStar_All.pipe_right uu____79841 FStar_List.flatten
                   in
                let pat_term1 uu____79943 = encode_term pat_term env1  in
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
      let uu____79953 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____80001  ->
                fun uu____80002  ->
                  match (uu____80001, uu____80002) with
                  | ((tms,decls),(t,uu____80042)) ->
                      let uu____80069 = encode_term t env  in
                      (match uu____80069 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____79953 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____80126 = FStar_Syntax_Util.list_elements e  in
        match uu____80126 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____80157 =
          let uu____80174 = FStar_Syntax_Util.unmeta p  in
          FStar_All.pipe_right uu____80174 FStar_Syntax_Util.head_and_args
           in
        match uu____80157 with
        | (head1,args) ->
            let uu____80225 =
              let uu____80240 =
                let uu____80241 = FStar_Syntax_Util.un_uinst head1  in
                uu____80241.FStar_Syntax_Syntax.n  in
              (uu____80240, args)  in
            (match uu____80225 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____80263,uu____80264)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____80316 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or1 t1 =
          let uu____80371 =
            let uu____80388 = FStar_Syntax_Util.unmeta t1  in
            FStar_All.pipe_right uu____80388 FStar_Syntax_Util.head_and_args
             in
          match uu____80371 with
          | (head1,args) ->
              let uu____80435 =
                let uu____80450 =
                  let uu____80451 = FStar_Syntax_Util.un_uinst head1  in
                  uu____80451.FStar_Syntax_Syntax.n  in
                (uu____80450, args)  in
              (match uu____80435 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____80470)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____80507 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____80537 = smt_pat_or1 t1  in
            (match uu____80537 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____80559 = list_elements1 e  in
                 FStar_All.pipe_right uu____80559
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____80589 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____80589
                           (FStar_List.map one_pat)))
             | uu____80612 ->
                 let uu____80617 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____80617])
        | uu____80668 ->
            let uu____80671 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____80671]
         in
      let uu____80722 =
        let uu____80737 =
          let uu____80738 = FStar_Syntax_Subst.compress t  in
          uu____80738.FStar_Syntax_Syntax.n  in
        match uu____80737 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____80777 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____80777 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____80812;
                        FStar_Syntax_Syntax.effect_name = uu____80813;
                        FStar_Syntax_Syntax.result_typ = uu____80814;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____80816)::(post,uu____80818)::(pats,uu____80820)::[];
                        FStar_Syntax_Syntax.flags = uu____80821;_}
                      ->
                      let uu____80882 = lemma_pats pats  in
                      (binders1, pre, post, uu____80882)
                  | uu____80893 -> failwith "impos"))
        | uu____80909 -> failwith "Impos"  in
      match uu____80722 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___1940_80946 = env  in
            {
              FStar_SMTEncoding_Env.bvar_bindings =
                (uu___1940_80946.FStar_SMTEncoding_Env.bvar_bindings);
              FStar_SMTEncoding_Env.fvar_bindings =
                (uu___1940_80946.FStar_SMTEncoding_Env.fvar_bindings);
              FStar_SMTEncoding_Env.depth =
                (uu___1940_80946.FStar_SMTEncoding_Env.depth);
              FStar_SMTEncoding_Env.tcenv =
                (uu___1940_80946.FStar_SMTEncoding_Env.tcenv);
              FStar_SMTEncoding_Env.warn =
                (uu___1940_80946.FStar_SMTEncoding_Env.warn);
              FStar_SMTEncoding_Env.nolabels =
                (uu___1940_80946.FStar_SMTEncoding_Env.nolabels);
              FStar_SMTEncoding_Env.use_zfuel_name = true;
              FStar_SMTEncoding_Env.encode_non_total_function_typ =
                (uu___1940_80946.FStar_SMTEncoding_Env.encode_non_total_function_typ);
              FStar_SMTEncoding_Env.current_module_name =
                (uu___1940_80946.FStar_SMTEncoding_Env.current_module_name);
              FStar_SMTEncoding_Env.encoding_quantifier =
                (uu___1940_80946.FStar_SMTEncoding_Env.encoding_quantifier);
              FStar_SMTEncoding_Env.global_cache =
                (uu___1940_80946.FStar_SMTEncoding_Env.global_cache)
            }  in
          let uu____80948 =
            encode_binders FStar_Pervasives_Native.None binders env1  in
          (match uu____80948 with
           | (vars,guards,env2,decls,uu____80973) ->
               let uu____80986 = encode_smt_patterns patterns env2  in
               (match uu____80986 with
                | (pats,decls') ->
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
                    let env3 =
                      let uu___1953_81013 = env2  in
                      {
                        FStar_SMTEncoding_Env.bvar_bindings =
                          (uu___1953_81013.FStar_SMTEncoding_Env.bvar_bindings);
                        FStar_SMTEncoding_Env.fvar_bindings =
                          (uu___1953_81013.FStar_SMTEncoding_Env.fvar_bindings);
                        FStar_SMTEncoding_Env.depth =
                          (uu___1953_81013.FStar_SMTEncoding_Env.depth);
                        FStar_SMTEncoding_Env.tcenv =
                          (uu___1953_81013.FStar_SMTEncoding_Env.tcenv);
                        FStar_SMTEncoding_Env.warn =
                          (uu___1953_81013.FStar_SMTEncoding_Env.warn);
                        FStar_SMTEncoding_Env.nolabels = true;
                        FStar_SMTEncoding_Env.use_zfuel_name =
                          (uu___1953_81013.FStar_SMTEncoding_Env.use_zfuel_name);
                        FStar_SMTEncoding_Env.encode_non_total_function_typ =
                          (uu___1953_81013.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                        FStar_SMTEncoding_Env.current_module_name =
                          (uu___1953_81013.FStar_SMTEncoding_Env.current_module_name);
                        FStar_SMTEncoding_Env.encoding_quantifier =
                          (uu___1953_81013.FStar_SMTEncoding_Env.encoding_quantifier);
                        FStar_SMTEncoding_Env.global_cache =
                          (uu___1953_81013.FStar_SMTEncoding_Env.global_cache)
                      }  in
                    let uu____81015 =
                      let uu____81020 = FStar_Syntax_Util.unmeta pre  in
                      encode_formula uu____81020 env3  in
                    (match uu____81015 with
                     | (pre1,decls'') ->
                         let uu____81027 =
                           let uu____81032 = FStar_Syntax_Util.unmeta post1
                              in
                           encode_formula uu____81032 env3  in
                         (match uu____81027 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append decls'
                                     (FStar_List.append decls'' decls'''))
                                 in
                              let uu____81042 =
                                let uu____81043 =
                                  let uu____81054 =
                                    let uu____81055 =
                                      let uu____81060 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards)
                                         in
                                      (uu____81060, post2)  in
                                    FStar_SMTEncoding_Util.mkImp uu____81055
                                     in
                                  (pats, vars, uu____81054)  in
                                FStar_SMTEncoding_Term.mkForall
                                  t.FStar_Syntax_Syntax.pos uu____81043
                                 in
                              (uu____81042, decls1)))))

and (encode_smt_patterns :
  FStar_Syntax_Syntax.arg Prims.list Prims.list ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term Prims.list Prims.list *
        FStar_SMTEncoding_Term.decls_t))
  =
  fun pats_l  ->
    fun env  ->
      let env1 =
        let uu___1965_81080 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___1965_81080.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___1965_81080.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___1965_81080.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___1965_81080.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___1965_81080.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___1965_81080.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___1965_81080.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___1965_81080.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___1965_81080.FStar_SMTEncoding_Env.encoding_quantifier);
          FStar_SMTEncoding_Env.global_cache =
            (uu___1965_81080.FStar_SMTEncoding_Env.global_cache)
        }  in
      let encode_smt_pattern t =
        let uu____81096 = FStar_Syntax_Util.head_and_args t  in
        match uu____81096 with
        | (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____81159::(x,uu____81161)::(t1,uu____81163)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____81230 = encode_term x env1  in
                 (match uu____81230 with
                  | (x1,decls) ->
                      let uu____81241 = encode_term t1 env1  in
                      (match uu____81241 with
                       | (t2,decls') ->
                           let uu____81252 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                           (uu____81252, (FStar_List.append decls decls'))))
             | uu____81253 -> encode_term t env1)
         in
      FStar_List.fold_right
        (fun pats  ->
           fun uu____81296  ->
             match uu____81296 with
             | (pats_l1,decls) ->
                 let uu____81341 =
                   FStar_List.fold_right
                     (fun uu____81376  ->
                        fun uu____81377  ->
                          match (uu____81376, uu____81377) with
                          | ((p,uu____81419),(pats1,decls1)) ->
                              let uu____81454 = encode_smt_pattern p  in
                              (match uu____81454 with
                               | (t,d) ->
                                   let uu____81469 =
                                     FStar_SMTEncoding_Term.check_pattern_ok
                                       t
                                      in
                                   (match uu____81469 with
                                    | FStar_Pervasives_Native.None  ->
                                        ((t :: pats1),
                                          (FStar_List.append d decls1))
                                    | FStar_Pervasives_Native.Some
                                        illegal_subterm ->
                                        ((let uu____81486 =
                                            let uu____81492 =
                                              let uu____81494 =
                                                FStar_Syntax_Print.term_to_string
                                                  p
                                                 in
                                              let uu____81496 =
                                                FStar_SMTEncoding_Term.print_smt_term
                                                  illegal_subterm
                                                 in
                                              FStar_Util.format2
                                                "Pattern %s contains illegal sub-term (%s); dropping it"
                                                uu____81494 uu____81496
                                               in
                                            (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                                              uu____81492)
                                             in
                                          FStar_Errors.log_issue
                                            p.FStar_Syntax_Syntax.pos
                                            uu____81486);
                                         (pats1,
                                           (FStar_List.append d decls1))))))
                     pats ([], decls)
                    in
                 (match uu____81341 with
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
        let uu____81556 =
          FStar_All.pipe_left
            (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____81556
        then
          let uu____81561 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____81563 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____81561 uu____81563
        else ()  in
      let enc f r l =
        let uu____81605 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____81637 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____81637 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____81605 with
        | (decls,args) ->
            let uu____81668 =
              let uu___2029_81669 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___2029_81669.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___2029_81669.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____81668, decls)
         in
      let const_op f r uu____81704 =
        let uu____81717 = f r  in (uu____81717, [])  in
      let un_op f l =
        let uu____81740 = FStar_List.hd l  in
        FStar_All.pipe_left f uu____81740  in
      let bin_op f uu___632_81760 =
        match uu___632_81760 with
        | t1::t2::[] -> f (t1, t2)
        | uu____81771 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____81812 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____81837  ->
                 match uu____81837 with
                 | (t,uu____81853) ->
                     let uu____81858 = encode_formula t env  in
                     (match uu____81858 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____81812 with
        | (decls,phis) ->
            let uu____81887 =
              let uu___2059_81888 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___2059_81888.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___2059_81888.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____81887, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____81951  ->
               match uu____81951 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____81972) -> false
                    | uu____81975 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____81994 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____81994
        else
          (let uu____82011 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____82011 r rf)
         in
      let eq3_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____82083 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::t1::v0::v1::[] ->
                     let uu____82115 =
                       let uu____82120 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____82121 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____82120, uu____82121)  in
                     FStar_SMTEncoding_Util.mkAnd uu____82115
                 | uu____82122 -> failwith "Impossible")
             in
          uu____82083 r args
        else
          (let uu____82128 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____82128)
         in
      let h_equals_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____82200 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::v0::t1::v1::[] ->
                     let uu____82232 =
                       let uu____82237 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____82238 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____82237, uu____82238)  in
                     FStar_SMTEncoding_Util.mkAnd uu____82232
                 | uu____82239 -> failwith "Impossible")
             in
          uu____82200 r args
        else
          (let uu____82245 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____82245)
         in
      let mk_imp1 r uu___633_82280 =
        match uu___633_82280 with
        | (lhs,uu____82286)::(rhs,uu____82288)::[] ->
            let uu____82329 = encode_formula rhs env  in
            (match uu____82329 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____82344) ->
                      (l1, decls1)
                  | uu____82349 ->
                      let uu____82350 = encode_formula lhs env  in
                      (match uu____82350 with
                       | (l2,decls2) ->
                           let uu____82361 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____82361, (FStar_List.append decls1 decls2)))))
        | uu____82362 -> failwith "impossible"  in
      let mk_ite r uu___634_82390 =
        match uu___634_82390 with
        | (guard,uu____82396)::(_then,uu____82398)::(_else,uu____82400)::[]
            ->
            let uu____82457 = encode_formula guard env  in
            (match uu____82457 with
             | (g,decls1) ->
                 let uu____82468 = encode_formula _then env  in
                 (match uu____82468 with
                  | (t,decls2) ->
                      let uu____82479 = encode_formula _else env  in
                      (match uu____82479 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____82491 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____82521 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l
           in
        f uu____82521  in
      let connectives =
        let uu____82551 =
          let uu____82576 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____82576)  in
        let uu____82619 =
          let uu____82646 =
            let uu____82671 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____82671)  in
          let uu____82714 =
            let uu____82741 =
              let uu____82768 =
                let uu____82793 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____82793)  in
              let uu____82836 =
                let uu____82863 =
                  let uu____82890 =
                    let uu____82915 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____82915)  in
                  [uu____82890;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.c_eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq3_op);
                  (FStar_Parser_Const.c_eq3_lid, h_equals_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____82863  in
              uu____82768 :: uu____82836  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____82741  in
          uu____82646 :: uu____82714  in
        uu____82551 :: uu____82619  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____83460 = encode_formula phi' env  in
            (match uu____83460 with
             | (phi2,decls) ->
                 let uu____83471 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____83471, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____83473 ->
            let uu____83480 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____83480 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____83519 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____83519 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____83531;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____83533;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____83535;
                 FStar_Syntax_Syntax.lbpos = uu____83536;_}::[]),e2)
            ->
            let uu____83563 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____83563 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____83616::(x,uu____83618)::(t,uu____83620)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____83687 = encode_term x env  in
                 (match uu____83687 with
                  | (x1,decls) ->
                      let uu____83698 = encode_term t env  in
                      (match uu____83698 with
                       | (t1,decls') ->
                           let uu____83709 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____83709, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____83712)::(msg,uu____83714)::(phi2,uu____83716)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____83783 =
                   let uu____83788 =
                     let uu____83789 = FStar_Syntax_Subst.compress r  in
                     uu____83789.FStar_Syntax_Syntax.n  in
                   let uu____83792 =
                     let uu____83793 = FStar_Syntax_Subst.compress msg  in
                     uu____83793.FStar_Syntax_Syntax.n  in
                   (uu____83788, uu____83792)  in
                 (match uu____83783 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____83802))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____83813 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____83820)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____83855 when head_redex env head2 ->
                 let uu____83870 = whnf env phi1  in
                 encode_formula uu____83870 env
             | uu____83871 ->
                 let uu____83886 = encode_term phi1 env  in
                 (match uu____83886 with
                  | (tt,decls) ->
                      let tt1 =
                        let uu____83898 =
                          let uu____83900 =
                            FStar_Range.use_range
                              tt.FStar_SMTEncoding_Term.rng
                             in
                          let uu____83901 =
                            FStar_Range.use_range
                              phi1.FStar_Syntax_Syntax.pos
                             in
                          FStar_Range.rng_included uu____83900 uu____83901
                           in
                        if uu____83898
                        then tt
                        else
                          (let uu___2246_83905 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___2246_83905.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___2246_83905.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      let uu____83906 = FStar_SMTEncoding_Term.mk_Valid tt1
                         in
                      (uu____83906, decls)))
        | uu____83907 ->
            let uu____83908 = encode_term phi1 env  in
            (match uu____83908 with
             | (tt,decls) ->
                 let tt1 =
                   let uu____83920 =
                     let uu____83922 =
                       FStar_Range.use_range tt.FStar_SMTEncoding_Term.rng
                        in
                     let uu____83923 =
                       FStar_Range.use_range phi1.FStar_Syntax_Syntax.pos  in
                     FStar_Range.rng_included uu____83922 uu____83923  in
                   if uu____83920
                   then tt
                   else
                     (let uu___2254_83927 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___2254_83927.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___2254_83927.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 let uu____83928 = FStar_SMTEncoding_Term.mk_Valid tt1  in
                 (uu____83928, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____83972 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____83972 with
        | (vars,guards,env2,decls,uu____84011) ->
            let uu____84024 = encode_smt_patterns ps env2  in
            (match uu____84024 with
             | (pats,decls') ->
                 let uu____84061 = encode_formula body env2  in
                 (match uu____84061 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____84093;
                             FStar_SMTEncoding_Term.rng = uu____84094;_}::[])::[]
                            when
                            let uu____84114 =
                              FStar_Ident.text_of_lid
                                FStar_Parser_Const.guard_free
                               in
                            uu____84114 = gf -> []
                        | uu____84117 -> guards  in
                      let uu____84122 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____84122, body1,
                        (FStar_List.append decls
                           (FStar_List.append decls' decls'')))))
         in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi  in
       let uu____84133 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____84133 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____84142 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____84248  ->
                     match uu____84248 with
                     | (l,uu____84273) -> FStar_Ident.lid_equals op l))
              in
           (match uu____84142 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____84342,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____84434 = encode_q_body env vars pats body  in
             match uu____84434 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____84479 =
                     let uu____84490 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____84490)  in
                   FStar_SMTEncoding_Term.mkForall
                     phi1.FStar_Syntax_Syntax.pos uu____84479
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____84521 = encode_q_body env vars pats body  in
             match uu____84521 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____84565 =
                   let uu____84566 =
                     let uu____84577 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____84577)  in
                   FStar_SMTEncoding_Term.mkExists
                     phi1.FStar_Syntax_Syntax.pos uu____84566
                    in
                 (uu____84565, decls))))
