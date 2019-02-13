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
               (fun uu___360_382  ->
                  match uu___360_382 with
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
                    (if s <> FStar_SMTEncoding_Term.Term_sort
                     then failwith "mk_Apply with non Term_sort"
                     else ();
                     (let uu____491 = FStar_SMTEncoding_Util.mkFreeV var  in
                      FStar_SMTEncoding_Util.mk_ApplyTT out uu____491))) e)
  
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
          let uu____547 =
            let uu____553 =
              let uu____555 = FStar_Util.string_of_int arity  in
              let uu____557 = FStar_Util.string_of_int n_args  in
              FStar_Util.format3
                "Head symbol %s expects at least %s arguments; got only %s"
                head1 uu____555 uu____557
               in
            (FStar_Errors.Fatal_SMTEncodingArityMismatch, uu____553)  in
          FStar_Errors.raise_error uu____547 rng
  
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
                  (let uu____616 = FStar_Util.first_N arity args  in
                   match uu____616 with
                   | (args1,rest) ->
                       let head3 =
                         FStar_SMTEncoding_Util.mkApp' (head2, args1)  in
                       mk_Apply_args head3 rest)
                else
                  (let uu____640 = FStar_SMTEncoding_Term.op_to_string head2
                      in
                   raise_arity_mismatch uu____640 arity n_args rng)
  
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
          let uu____667 = FStar_SMTEncoding_Env.force_thunk fvb  in
          mk_Apply_args uu____667 args
        else
          maybe_curry_app rng
            (FStar_Util.Inl
               (FStar_SMTEncoding_Term.Var (fvb.FStar_SMTEncoding_Env.smt_id)))
            fvb.FStar_SMTEncoding_Env.smt_arity args
  
let (is_app : FStar_SMTEncoding_Term.op -> Prims.bool) =
  fun uu___361_676  ->
    match uu___361_676 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____682 -> false
  
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
                       FStar_SMTEncoding_Term.freevars = uu____730;
                       FStar_SMTEncoding_Term.rng = uu____731;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____762) ->
              let uu____772 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____789 -> false) args (FStar_List.rev xs))
                 in
              if uu____772
              then FStar_SMTEncoding_Env.tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____796,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t  in
              let uu____800 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____808 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars
                           in
                        Prims.op_Negation uu____808))
                 in
              if uu____800
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____815 -> FStar_Pervasives_Native.None  in
        check_partial_applications body (FStar_List.rev vars)
  
let check_pattern_vars :
  'Auu____833 'Auu____834 .
    FStar_SMTEncoding_Env.env_t ->
      (FStar_Syntax_Syntax.bv * 'Auu____833) Prims.list ->
        (FStar_Syntax_Syntax.term * 'Auu____834) Prims.list -> unit
  =
  fun env  ->
    fun vars  ->
      fun pats  ->
        let pats1 =
          FStar_All.pipe_right pats
            (FStar_List.map
               (fun uu____892  ->
                  match uu____892 with
                  | (x,uu____898) ->
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
              let uu____906 = FStar_Syntax_Free.names hd1  in
              FStar_List.fold_left
                (fun out  ->
                   fun x  ->
                     let uu____918 = FStar_Syntax_Free.names x  in
                     FStar_Util.set_union out uu____918) uu____906 tl1
               in
            let uu____921 =
              FStar_All.pipe_right vars
                (FStar_Util.find_opt
                   (fun uu____948  ->
                      match uu____948 with
                      | (b,uu____955) ->
                          let uu____956 = FStar_Util.set_mem b pat_vars  in
                          Prims.op_Negation uu____956))
               in
            (match uu____921 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some (x,uu____963) ->
                 let pos =
                   FStar_List.fold_left
                     (fun out  ->
                        fun t  ->
                          FStar_Range.union_ranges out
                            t.FStar_Syntax_Syntax.pos)
                     hd1.FStar_Syntax_Syntax.pos tl1
                    in
                 let uu____977 =
                   let uu____983 =
                     let uu____985 = FStar_Syntax_Print.bv_to_string x  in
                     FStar_Util.format1
                       "SMT pattern misses at least one bound variable: %s"
                       uu____985
                      in
                   (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                     uu____983)
                    in
                 FStar_Errors.log_issue pos uu____977)
  
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
        | FStar_Syntax_Syntax.Tm_arrow uu____1271 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____1286 ->
            let uu____1293 = FStar_Syntax_Util.unrefine t1  in
            aux true uu____1293
        | uu____1295 ->
            if norm1
            then let uu____1297 = whnf env t1  in aux false uu____1297
            else
              (let uu____1301 =
                 let uu____1303 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let uu____1305 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____1303 uu____1305
                  in
               failwith uu____1301)
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
    | FStar_Syntax_Syntax.Tm_refine (bv,uu____1347) ->
        let uu____1352 =
          curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort  in
        (match uu____1352 with
         | (args,res) ->
             (match args with
              | [] ->
                  let uu____1373 = FStar_Syntax_Syntax.mk_Total k1  in
                  ([], uu____1373)
              | uu____1380 -> (args, res)))
    | uu____1381 ->
        let uu____1382 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____1382)
  
let is_arithmetic_primitive :
  'Auu____1396 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____1396 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1419::uu____1420::[]) ->
          ((((FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.op_Addition_lid)
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1424::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____1427 -> false
  
let (isInteger : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____1458 -> false
  
let (getInteger : FStar_Syntax_Syntax.term' -> Prims.int) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____1481 -> failwith "Expected an Integer term"
  
let is_BitVector_primitive :
  'Auu____1491 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____1491)
        Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____1533)::uu____1534::uu____1535::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____1586)::uu____1587::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____1624 -> false
  
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
          let uu____1942 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue  in
          (uu____1942, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____1944 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse  in
          (uu____1944, [])
      | FStar_Const.Const_char c1 ->
          let uu____1947 =
            let uu____1948 =
              let uu____1956 =
                let uu____1959 =
                  let uu____1960 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1)
                     in
                  FStar_SMTEncoding_Term.boxInt uu____1960  in
                [uu____1959]  in
              ("FStar.Char.__char_of_int", uu____1956)  in
            FStar_SMTEncoding_Util.mkApp uu____1948  in
          (uu____1947, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____1978 =
            let uu____1979 = FStar_SMTEncoding_Util.mkInteger i  in
            FStar_SMTEncoding_Term.boxInt uu____1979  in
          (uu____1978, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.FStar_SMTEncoding_Env.tcenv).FStar_TypeChecker_Env.dsenv
              repr sw FStar_Range.dummyRange
             in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____2000) ->
          let uu____2003 =
            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.string_const s
             in
          (uu____2003, [])
      | FStar_Const.Const_range uu____2004 ->
          let uu____2005 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          (uu____2005, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
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
            let unary arg_tms1 =
              let uu____2431 = FStar_List.hd arg_tms1  in
              FStar_SMTEncoding_Term.unboxInt uu____2431  in
            let binary arg_tms1 =
              let uu____2446 =
                let uu____2447 = FStar_List.hd arg_tms1  in
                FStar_SMTEncoding_Term.unboxInt uu____2447  in
              let uu____2448 =
                let uu____2449 =
                  let uu____2450 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____2450  in
                FStar_SMTEncoding_Term.unboxInt uu____2449  in
              (uu____2446, uu____2448)  in
            let mk_default uu____2458 =
              let uu____2459 =
                FStar_SMTEncoding_Env.lookup_free_var_sym env
                  head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____2459 with
              | (fname,fuel_args,arity) ->
                  let args = FStar_List.append fuel_args arg_tms  in
                  maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity
                    args
               in
            let mk_l op mk_args ts =
              let uu____2536 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____2536
              then
                let uu____2539 =
                  let uu____2540 = mk_args ts  in op uu____2540  in
                FStar_All.pipe_right uu____2539 FStar_SMTEncoding_Term.boxInt
              else mk_default ()  in
            let mk_nl nm op ts =
              let uu____2578 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____2578
              then
                let uu____2581 = binary ts  in
                match uu____2581 with
                | (t1,t2) ->
                    let uu____2588 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____2588
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____2594 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____2594
                 then
                   let uu____2597 =
                     let uu____2598 = binary ts  in op uu____2598  in
                   FStar_All.pipe_right uu____2597
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
              [(FStar_Parser_Const.op_Addition_lid, add1);
              (FStar_Parser_Const.op_Subtraction, sub1);
              (FStar_Parser_Const.op_Multiply, mul1);
              (FStar_Parser_Const.op_Division, div1);
              (FStar_Parser_Const.op_Modulus, modulus);
              (FStar_Parser_Const.op_Minus, minus1)]  in
            let uu____2763 =
              let uu____2773 =
                FStar_List.tryFind
                  (fun uu____2797  ->
                     match uu____2797 with
                     | (l,uu____2808) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____2773 FStar_Util.must  in
            (match uu____2763 with
             | (uu____2852,op) ->
                 let uu____2864 = op arg_tms  in (uu____2864, decls))

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
        let uu____2872 = FStar_List.hd args_e  in
        match uu____2872 with
        | (tm_sz,uu____2880) ->
            let uu____2889 = uu____2872  in
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let uu____2898 =
                FStar_Util.smap_try_find env.FStar_SMTEncoding_Env.cache
                  sz_key
                 in
              match uu____2898 with
              | FStar_Pervasives_Native.Some cache_entry ->
                  FStar_SMTEncoding_Env.use_cache_entry cache_entry
              | FStar_Pervasives_Native.None  ->
                  let t_decls1 = FStar_SMTEncoding_Term.mkBvConstructor sz
                     in
                  ((let uu____2906 =
                      FStar_SMTEncoding_Env.mk_cache_entry env "" [] t_decls1
                       in
                    FStar_Util.smap_add env.FStar_SMTEncoding_Env.cache
                      sz_key uu____2906);
                   t_decls1)
               in
            let uu____2908 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____2934::(sz_arg,uu____2936)::uu____2937::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____3004 =
                    let uu____3005 = FStar_List.tail args_e  in
                    FStar_List.tail uu____3005  in
                  let uu____3008 =
                    let uu____3012 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____3012  in
                  (uu____3004, uu____3008)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____3019::(sz_arg,uu____3021)::uu____3022::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____3089 =
                    let uu____3091 = FStar_Syntax_Print.term_to_string sz_arg
                       in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____3091
                     in
                  failwith uu____3089
              | uu____3101 ->
                  let uu____3116 = FStar_List.tail args_e  in
                  (uu____3116, FStar_Pervasives_Native.None)
               in
            (match uu____2908 with
             | (arg_tms,ext_sz) ->
                 let uu____3135 = encode_args arg_tms env  in
                 (match uu____3135 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____3156 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____3168 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____3168  in
                      let unary_arith arg_tms2 =
                        let uu____3179 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____3179  in
                      let binary arg_tms2 =
                        let uu____3194 =
                          let uu____3195 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3195
                           in
                        let uu____3196 =
                          let uu____3197 =
                            let uu____3198 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____3198  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3197
                           in
                        (uu____3194, uu____3196)  in
                      let binary_arith arg_tms2 =
                        let uu____3215 =
                          let uu____3216 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3216
                           in
                        let uu____3217 =
                          let uu____3218 =
                            let uu____3219 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____3219  in
                          FStar_SMTEncoding_Term.unboxInt uu____3218  in
                        (uu____3215, uu____3217)  in
                      let mk_bv op mk_args resBox ts =
                        let uu____3277 =
                          let uu____3278 = mk_args ts  in op uu____3278  in
                        FStar_All.pipe_right uu____3277 resBox  in
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
                        let uu____3410 =
                          let uu____3415 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____3415  in
                        let uu____3424 =
                          let uu____3429 =
                            let uu____3431 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____3431  in
                          FStar_SMTEncoding_Term.boxBitVec uu____3429  in
                        mk_bv uu____3410 unary uu____3424 arg_tms2  in
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
                      let uu____3671 =
                        let uu____3681 =
                          FStar_List.tryFind
                            (fun uu____3705  ->
                               match uu____3705 with
                               | (l,uu____3716) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____3681 FStar_Util.must  in
                      (match uu____3671 with
                       | (uu____3762,op) ->
                           let uu____3774 = op arg_tms1  in
                           (uu____3774, (FStar_List.append sz_decls decls)))))

and (encode_deeply_embedded_quantifier :
  FStar_Syntax_Syntax.term ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let env1 =
        let uu___365_3784 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___365_3784.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___365_3784.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___365_3784.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___365_3784.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___365_3784.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.cache =
            (uu___365_3784.FStar_SMTEncoding_Env.cache);
          FStar_SMTEncoding_Env.nolabels =
            (uu___365_3784.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name =
            (uu___365_3784.FStar_SMTEncoding_Env.use_zfuel_name);
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___365_3784.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___365_3784.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier = true
        }  in
      let uu____3786 = encode_term t env1  in
      match uu____3786 with
      | (tm,decls) ->
          let vars = FStar_SMTEncoding_Term.free_variables tm  in
          let valid_tm = FStar_SMTEncoding_Term.mk_Valid tm  in
          let key =
            FStar_SMTEncoding_Term.mkForall t.FStar_Syntax_Syntax.pos
              ([], vars, valid_tm)
             in
          let tkey_hash = FStar_SMTEncoding_Term.hash_of_term key  in
          let uu____3808 =
            FStar_Util.smap_try_find env1.FStar_SMTEncoding_Env.cache
              tkey_hash
             in
          (match uu____3808 with
           | FStar_Pervasives_Native.Some cache_entry ->
               (tm,
                 (FStar_List.append decls
                    (FStar_SMTEncoding_Env.use_cache_entry cache_entry)))
           | uu____3816 ->
               (match tm.FStar_SMTEncoding_Term.tm with
                | FStar_SMTEncoding_Term.App
                    (uu____3823,{
                                  FStar_SMTEncoding_Term.tm =
                                    FStar_SMTEncoding_Term.FreeV uu____3824;
                                  FStar_SMTEncoding_Term.freevars =
                                    uu____3825;
                                  FStar_SMTEncoding_Term.rng = uu____3826;_}::
                     {
                       FStar_SMTEncoding_Term.tm =
                         FStar_SMTEncoding_Term.FreeV uu____3827;
                       FStar_SMTEncoding_Term.freevars = uu____3828;
                       FStar_SMTEncoding_Term.rng = uu____3829;_}::[])
                    ->
                    (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                       (FStar_Errors.Warning_QuantifierWithoutPattern,
                         "Not encoding deeply embedded, unguarded quantifier to SMT");
                     (tm, decls))
                | uu____3875 ->
                    let uu____3876 = encode_formula t env1  in
                    (match uu____3876 with
                     | (phi,decls') ->
                         let interp =
                           match vars with
                           | [] ->
                               let uu____3896 =
                                 let uu____3901 =
                                   FStar_SMTEncoding_Term.mk_Valid tm  in
                                 (uu____3901, phi)  in
                               FStar_SMTEncoding_Util.mkIff uu____3896
                           | uu____3902 ->
                               let uu____3903 =
                                 let uu____3914 =
                                   let uu____3915 =
                                     let uu____3920 =
                                       FStar_SMTEncoding_Term.mk_Valid tm  in
                                     (uu____3920, phi)  in
                                   FStar_SMTEncoding_Util.mkIff uu____3915
                                    in
                                 ([[valid_tm]], vars, uu____3914)  in
                               FStar_SMTEncoding_Term.mkForall
                                 t.FStar_Syntax_Syntax.pos uu____3903
                            in
                         let ax =
                           let uu____3930 =
                             let uu____3938 =
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 "l_quant_interp"
                                in
                             (interp,
                               (FStar_Pervasives_Native.Some
                                  "Interpretation of deeply embedded quantifier"),
                               uu____3938)
                              in
                           FStar_SMTEncoding_Util.mkAssume uu____3930  in
                         let decls1 =
                           FStar_List.append decls
                             (FStar_List.append decls' [ax])
                            in
                         ((let uu____3948 =
                             FStar_SMTEncoding_Env.mk_cache_entry env1 "" []
                               decls1
                              in
                           FStar_Util.smap_add
                             env1.FStar_SMTEncoding_Env.cache tkey_hash
                             uu____3948);
                          (tm, decls1)))))

and (encode_term :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____3958 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____3958
       then
         let uu____3963 = FStar_Syntax_Print.tag_of_term t  in
         let uu____3965 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____3967 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____3963 uu____3965
           uu____3967
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____3976 ->
           let uu____3999 =
             let uu____4001 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____4004 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____4006 = FStar_Syntax_Print.term_to_string t0  in
             let uu____4008 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____4001
               uu____4004 uu____4006 uu____4008
              in
           failwith uu____3999
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____4015 =
             let uu____4017 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____4020 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____4022 = FStar_Syntax_Print.term_to_string t0  in
             let uu____4024 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____4017
               uu____4020 uu____4022 uu____4024
              in
           failwith uu____4015
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let e = FStar_Syntax_Util.unfold_lazy i  in
           ((let uu____4034 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____4034
             then
               let uu____4039 = FStar_Syntax_Print.term_to_string t0  in
               let uu____4041 = FStar_Syntax_Print.term_to_string e  in
               FStar_Util.print2 ">> Unfolded (%s) ~> (%s)\n" uu____4039
                 uu____4041
             else ());
            encode_term e env)
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____4047 =
             let uu____4049 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____4049
              in
           failwith uu____4047
       | FStar_Syntax_Syntax.Tm_ascribed (t1,(k,uu____4058),uu____4059) ->
           let uu____4108 =
             match k with
             | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
             | uu____4118 -> false  in
           if uu____4108
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t1 env
       | FStar_Syntax_Syntax.Tm_quoted (qt,uu____4136) ->
           let tv =
             let uu____4142 =
               let uu____4149 = FStar_Reflection_Basic.inspect_ln qt  in
               FStar_Syntax_Embeddings.embed
                 FStar_Reflection_Embeddings.e_term_view uu____4149
                in
             uu____4142 t.FStar_Syntax_Syntax.pos
               FStar_Pervasives_Native.None
               FStar_Syntax_Embeddings.id_norm_cb
              in
           ((let uu____4176 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____4176
             then
               let uu____4181 = FStar_Syntax_Print.term_to_string t0  in
               let uu____4183 = FStar_Syntax_Print.term_to_string tv  in
               FStar_Util.print2 ">> Inspected (%s) ~> (%s)\n" uu____4181
                 uu____4183
             else ());
            (let t1 =
               let uu____4191 =
                 let uu____4202 = FStar_Syntax_Syntax.as_arg tv  in
                 [uu____4202]  in
               FStar_Syntax_Util.mk_app
                 (FStar_Reflection_Data.refl_constant_term
                    FStar_Reflection_Data.fstar_refl_pack_ln) uu____4191
                in
             encode_term t1 env))
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_pattern uu____4228) ->
           encode_term t1
             (let uu___366_4246 = env  in
              {
                FStar_SMTEncoding_Env.bvar_bindings =
                  (uu___366_4246.FStar_SMTEncoding_Env.bvar_bindings);
                FStar_SMTEncoding_Env.fvar_bindings =
                  (uu___366_4246.FStar_SMTEncoding_Env.fvar_bindings);
                FStar_SMTEncoding_Env.depth =
                  (uu___366_4246.FStar_SMTEncoding_Env.depth);
                FStar_SMTEncoding_Env.tcenv =
                  (uu___366_4246.FStar_SMTEncoding_Env.tcenv);
                FStar_SMTEncoding_Env.warn =
                  (uu___366_4246.FStar_SMTEncoding_Env.warn);
                FStar_SMTEncoding_Env.cache =
                  (uu___366_4246.FStar_SMTEncoding_Env.cache);
                FStar_SMTEncoding_Env.nolabels =
                  (uu___366_4246.FStar_SMTEncoding_Env.nolabels);
                FStar_SMTEncoding_Env.use_zfuel_name =
                  (uu___366_4246.FStar_SMTEncoding_Env.use_zfuel_name);
                FStar_SMTEncoding_Env.encode_non_total_function_typ =
                  (uu___366_4246.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                FStar_SMTEncoding_Env.current_module_name =
                  (uu___366_4246.FStar_SMTEncoding_Env.current_module_name);
                FStar_SMTEncoding_Env.encoding_quantifier = false
              })
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____4249) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = FStar_SMTEncoding_Env.lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____4257 = head_redex env t  in
           if uu____4257
           then let uu____4264 = whnf env t  in encode_term uu____4264 env
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
                  | FStar_SMTEncoding_Term.FreeV uu____4272 ->
                      let uu____4281 =
                        let uu____4282 =
                          let uu____4290 =
                            FStar_SMTEncoding_Term.kick_partial_app tok  in
                          let uu____4291 =
                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                              "@kick_partial_app"
                             in
                          (uu____4290,
                            (FStar_Pervasives_Native.Some "kick_partial_app"),
                            uu____4291)
                           in
                        FStar_SMTEncoding_Util.mkAssume uu____4282  in
                      [uu____4281]
                  | FStar_SMTEncoding_Term.App (uu____4297,[]) ->
                      let uu____4300 =
                        let uu____4301 =
                          let uu____4309 =
                            FStar_SMTEncoding_Term.kick_partial_app tok  in
                          let uu____4310 =
                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                              "@kick_partial_app"
                             in
                          (uu____4309,
                            (FStar_Pervasives_Native.Some "kick_partial_app"),
                            uu____4310)
                           in
                        FStar_SMTEncoding_Util.mkAssume uu____4301  in
                      [uu____4300]
                  | uu____4316 -> []
                else []  in
              (tok, aux_decls))
       | FStar_Syntax_Syntax.Tm_type uu____4319 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4321) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.FStar_SMTEncoding_Env.current_module_name
              in
           let uu____4351 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____4351 with
            | (binders1,res) ->
                let uu____4362 =
                  (env.FStar_SMTEncoding_Env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____4362
                then
                  let uu____4369 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____4369 with
                   | (vars,guards,env',decls,uu____4394) ->
                       let fsym =
                         let uu____4408 =
                           let uu____4414 =
                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                               "f"
                              in
                           (uu____4414, FStar_SMTEncoding_Term.Term_sort)  in
                         FStar_SMTEncoding_Term.mk_fv uu____4408  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____4420 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___367_4429 =
                              env.FStar_SMTEncoding_Env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___367_4429.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___367_4429.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___367_4429.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___367_4429.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___367_4429.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___367_4429.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___367_4429.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___367_4429.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___367_4429.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___367_4429.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___367_4429.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___367_4429.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___367_4429.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___367_4429.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___367_4429.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___367_4429.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___367_4429.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___367_4429.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___367_4429.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___367_4429.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___367_4429.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___367_4429.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___367_4429.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___367_4429.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___367_4429.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___367_4429.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___367_4429.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___367_4429.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___367_4429.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___367_4429.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___367_4429.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___367_4429.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___367_4429.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___367_4429.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___367_4429.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___367_4429.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___367_4429.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___367_4429.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___367_4429.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___367_4429.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___367_4429.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___367_4429.FStar_TypeChecker_Env.nbe)
                            }) res
                          in
                       (match uu____4420 with
                        | (pre_opt,res_t) ->
                            let uu____4441 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____4441 with
                             | (res_pred,decls') ->
                                 let uu____4452 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____4465 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____4465, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____4469 =
                                         encode_formula pre env'  in
                                       (match uu____4469 with
                                        | (guard,decls0) ->
                                            let uu____4482 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____4482, decls0))
                                    in
                                 (match uu____4452 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____4496 =
                                          let uu____4507 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____4507)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t.FStar_Syntax_Syntax.pos
                                          uu____4496
                                         in
                                      let cvars =
                                        let uu____4527 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____4527
                                          (FStar_List.filter
                                             (fun x  ->
                                                let uu____4546 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    x
                                                   in
                                                let uu____4548 =
                                                  FStar_SMTEncoding_Term.fv_name
                                                    fsym
                                                   in
                                                uu____4546 <> uu____4548))
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
                                      let uu____4568 =
                                        FStar_Util.smap_try_find
                                          env.FStar_SMTEncoding_Env.cache
                                          tkey_hash
                                         in
                                      (match uu____4568 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____4576 =
                                             let uu____4577 =
                                               let uu____4585 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV)
                                                  in
                                               ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                                 uu____4585)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4577
                                              in
                                           (uu____4576,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (FStar_SMTEncoding_Env.use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____4597 =
                                               let uu____4599 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____4599
                                                in
                                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                               uu____4597
                                              in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_SMTEncoding_Term.fv_sort
                                               cvars
                                              in
                                           let caption =
                                             let uu____4614 =
                                               FStar_Options.log_queries ()
                                                in
                                             if uu____4614
                                             then
                                               let uu____4617 =
                                                 let uu____4619 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env.FStar_SMTEncoding_Env.tcenv
                                                     t0
                                                    in
                                                 FStar_Util.replace_char
                                                   uu____4619 10 32
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____4617
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
                                             let uu____4632 =
                                               let uu____4640 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars
                                                  in
                                               (tsym, uu____4640)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4632
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
                                             let uu____4659 =
                                               let uu____4667 =
                                                 FStar_SMTEncoding_Term.mkForall
                                                   t0.FStar_Syntax_Syntax.pos
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind)
                                                  in
                                               (uu____4667,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name)
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4659
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
                                             let uu____4684 =
                                               let uu____4692 =
                                                 let uu____4693 =
                                                   let uu____4704 =
                                                     let uu____4705 =
                                                       let uu____4710 =
                                                         let uu____4711 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f
                                                            in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____4711
                                                          in
                                                       (f_has_t, uu____4710)
                                                        in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____4705
                                                      in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____4704)
                                                    in
                                                 let uu____4729 =
                                                   mkForall_fuel
                                                     t0.FStar_Syntax_Syntax.pos
                                                    in
                                                 uu____4729 uu____4693  in
                                               (uu____4692,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4684
                                              in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym
                                                in
                                             let uu____4752 =
                                               let uu____4760 =
                                                 let uu____4761 =
                                                   let uu____4772 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp)
                                                      in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____4772)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   t0.FStar_Syntax_Syntax.pos
                                                   uu____4761
                                                  in
                                               (uu____4760,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4752
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
                                           ((let uu____4796 =
                                               FStar_SMTEncoding_Env.mk_cache_entry
                                                 env tsym cvar_sorts t_decls1
                                                in
                                             FStar_Util.smap_add
                                               env.FStar_SMTEncoding_Env.cache
                                               tkey_hash uu____4796);
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
                     let uu____4815 =
                       let uu____4823 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____4823,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____4815  in
                   let fsym =
                     FStar_SMTEncoding_Term.mk_fv
                       ("f", FStar_SMTEncoding_Term.Term_sort)
                      in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym  in
                     let uu____4837 =
                       let uu____4845 =
                         let uu____4846 =
                           let uu____4857 =
                             let uu____4858 =
                               let uu____4863 =
                                 let uu____4864 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____4864
                                  in
                               (f_has_t, uu____4863)  in
                             FStar_SMTEncoding_Util.mkImp uu____4858  in
                           ([[f_has_t]], [fsym], uu____4857)  in
                         let uu____4890 =
                           mkForall_fuel t0.FStar_Syntax_Syntax.pos  in
                         uu____4890 uu____4846  in
                       (uu____4845, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____4837  in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____4908 ->
           let uu____4915 =
             let uu____4920 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Env.Weak;
                 FStar_TypeChecker_Env.HNF;
                 FStar_TypeChecker_Env.EraseUniverses]
                 env.FStar_SMTEncoding_Env.tcenv t0
                in
             match uu____4920 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____4927;
                 FStar_Syntax_Syntax.vars = uu____4928;_} ->
                 let uu____4935 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____4935 with
                  | (b,f1) ->
                      let uu____4960 =
                        let uu____4961 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____4961  in
                      (uu____4960, f1))
             | uu____4976 -> failwith "impossible"  in
           (match uu____4915 with
            | (x,f) ->
                let uu____4988 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____4988 with
                 | (base_t,decls) ->
                     let uu____4999 =
                       FStar_SMTEncoding_Env.gen_term_var env x  in
                     (match uu____4999 with
                      | (x1,xtm,env') ->
                          let uu____5016 = encode_formula f env'  in
                          (match uu____5016 with
                           | (refinement,decls') ->
                               let uu____5027 =
                                 FStar_SMTEncoding_Env.fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____5027 with
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
                                      let uu____5055 =
                                        let uu____5066 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____5077 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____5066
                                          uu____5077
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____5055
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun y  ->
                                              (let uu____5131 =
                                                 FStar_SMTEncoding_Term.fv_name
                                                   y
                                                  in
                                               uu____5131 <> x1) &&
                                                (let uu____5135 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     y
                                                    in
                                                 uu____5135 <> fsym)))
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
                                    let uu____5167 =
                                      FStar_Util.smap_try_find
                                        env.FStar_SMTEncoding_Env.cache
                                        tkey_hash
                                       in
                                    (match uu____5167 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____5175 =
                                           let uu____5176 =
                                             let uu____5184 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV)
                                                in
                                             ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                               uu____5184)
                                              in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____5176
                                            in
                                         (uu____5175,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (FStar_SMTEncoding_Env.use_cache_entry
                                                    cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.FStar_SMTEncoding_Env.current_module_name
                                            in
                                         let tsym =
                                           let uu____5198 =
                                             let uu____5200 =
                                               let uu____5202 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____5202
                                                in
                                             Prims.strcat module_name
                                               uu____5200
                                              in
                                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                             uu____5198
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
                                           let uu____5222 =
                                             let uu____5230 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1
                                                in
                                             (tsym, uu____5230)  in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____5222
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
                                           let uu____5250 =
                                             let uu____5258 =
                                               let uu____5259 =
                                                 let uu____5270 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base)
                                                    in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____5270)
                                                  in
                                               FStar_SMTEncoding_Term.mkForall
                                                 t0.FStar_Syntax_Syntax.pos
                                                 uu____5259
                                                in
                                             (uu____5258,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____5250
                                            in
                                         let t_kinding =
                                           let uu____5284 =
                                             let uu____5292 =
                                               FStar_SMTEncoding_Term.mkForall
                                                 t0.FStar_Syntax_Syntax.pos
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind)
                                                in
                                             (uu____5292,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____5284
                                            in
                                         let t_interp =
                                           let uu____5306 =
                                             let uu____5314 =
                                               let uu____5315 =
                                                 let uu____5326 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding)
                                                    in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____5326)
                                                  in
                                               FStar_SMTEncoding_Term.mkForall
                                                 t0.FStar_Syntax_Syntax.pos
                                                 uu____5315
                                                in
                                             (uu____5314,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement_interpretation"),
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____5306
                                            in
                                         let t_decls1 =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1])
                                            in
                                         ((let uu____5359 =
                                             FStar_SMTEncoding_Env.mk_cache_entry
                                               env tsym cvar_sorts t_decls1
                                              in
                                           FStar_Util.smap_add
                                             env.FStar_SMTEncoding_Env.cache
                                             tkey_hash uu____5359);
                                          (t1, t_decls1))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,uu____5361) ->
           let ttm =
             let uu____5379 =
               FStar_Syntax_Unionfind.uvar_id
                 uv.FStar_Syntax_Syntax.ctx_uvar_head
                in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____5379  in
           let uu____5381 =
             encode_term_pred FStar_Pervasives_Native.None
               uv.FStar_Syntax_Syntax.ctx_uvar_typ env ttm
              in
           (match uu____5381 with
            | (t_has_k,decls) ->
                let d =
                  let uu____5393 =
                    let uu____5401 =
                      let uu____5403 =
                        let uu____5405 =
                          let uu____5407 =
                            FStar_Syntax_Unionfind.uvar_id
                              uv.FStar_Syntax_Syntax.ctx_uvar_head
                             in
                          FStar_Util.string_of_int uu____5407  in
                        FStar_Util.format1 "uvar_typing_%s" uu____5405  in
                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                        uu____5403
                       in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____5401)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____5393  in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____5413 ->
           let uu____5430 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____5430 with
            | (head1,args_e) ->
                let uu____5477 =
                  let uu____5492 =
                    let uu____5493 = FStar_Syntax_Subst.compress head1  in
                    uu____5493.FStar_Syntax_Syntax.n  in
                  (uu____5492, args_e)  in
                (match uu____5477 with
                 | uu____5510 when head_redex env head1 ->
                     let uu____5525 = whnf env t  in
                     encode_term uu____5525 env
                 | uu____5526 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____5549 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5567) when
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
                       FStar_Syntax_Syntax.pos = uu____5589;
                       FStar_Syntax_Syntax.vars = uu____5590;_},uu____5591),uu____5592)
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
                       FStar_Syntax_Syntax.pos = uu____5618;
                       FStar_Syntax_Syntax.vars = uu____5619;_},uu____5620),
                    (v0,uu____5622)::(v1,uu____5624)::(v2,uu____5626)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____5697 = encode_term v0 env  in
                     (match uu____5697 with
                      | (v01,decls0) ->
                          let uu____5708 = encode_term v1 env  in
                          (match uu____5708 with
                           | (v11,decls1) ->
                               let uu____5719 = encode_term v2 env  in
                               (match uu____5719 with
                                | (v21,decls2) ->
                                    let uu____5730 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____5730,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(v0,uu____5733)::(v1,uu____5735)::(v2,uu____5737)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____5804 = encode_term v0 env  in
                     (match uu____5804 with
                      | (v01,decls0) ->
                          let uu____5815 = encode_term v1 env  in
                          (match uu____5815 with
                           | (v11,decls1) ->
                               let uu____5826 = encode_term v2 env  in
                               (match uu____5826 with
                                | (v21,decls2) ->
                                    let uu____5837 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____5837,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____5839)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____5875)::(rng,uu____5877)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____5928) ->
                     let e0 =
                       let uu____5950 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg
                         env.FStar_SMTEncoding_Env.tcenv head1 uu____5950
                        in
                     ((let uu____5960 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug
                              env.FStar_SMTEncoding_Env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____5960
                       then
                         let uu____5965 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____5965
                       else ());
                      (let e =
                         let uu____5973 =
                           let uu____5978 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____5979 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____5978
                             uu____5979
                            in
                         uu____5973 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____5990),(arg,uu____5992)::[]) -> encode_term arg env
                 | uu____6027 ->
                     let uu____6042 = encode_args args_e env  in
                     (match uu____6042 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____6103 = encode_term head1 env  in
                            match uu____6103 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____6175 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____6175 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____6273  ->
                                                 fun uu____6274  ->
                                                   match (uu____6273,
                                                           uu____6274)
                                                   with
                                                   | ((bv,uu____6304),
                                                      (a,uu____6306)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____6336 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____6336
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____6337 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm
                                             in
                                          (match uu____6337 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type
                                                  in
                                               let e_typing =
                                                 let uu____6352 =
                                                   let uu____6360 =
                                                     FStar_SMTEncoding_Term.mkForall
                                                       t0.FStar_Syntax_Syntax.pos
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____6369 =
                                                     let uu____6371 =
                                                       let uu____6373 =
                                                         let uu____6375 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm
                                                            in
                                                         FStar_Util.digest_of_string
                                                           uu____6375
                                                          in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____6373
                                                        in
                                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                       uu____6371
                                                      in
                                                   (uu____6360,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____6369)
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____6352
                                                  in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing])))))))
                             in
                          let encode_full_app fv =
                            let uu____6397 =
                              FStar_SMTEncoding_Env.lookup_free_var_sym env
                                fv
                               in
                            match uu____6397 with
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
                                   FStar_Syntax_Syntax.pos = uu____6440;
                                   FStar_Syntax_Syntax.vars = uu____6441;_},uu____6442)
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
                                   FStar_Syntax_Syntax.pos = uu____6449;
                                   FStar_Syntax_Syntax.vars = uu____6450;_},uu____6451)
                                ->
                                let uu____6456 =
                                  let uu____6457 =
                                    let uu____6462 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____6462
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____6457
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____6456
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____6492 =
                                  let uu____6493 =
                                    let uu____6498 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____6498
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____6493
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____6492
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____6527,(FStar_Util.Inl t1,uu____6529),uu____6530)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____6577,(FStar_Util.Inr c,uu____6579),uu____6580)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____6627 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____6648 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Env.Weak;
                                     FStar_TypeChecker_Env.HNF;
                                     FStar_TypeChecker_Env.EraseUniverses]
                                     env.FStar_SMTEncoding_Env.tcenv
                                     head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____6648
                                  in
                               let uu____6649 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____6649 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____6665;
                                            FStar_Syntax_Syntax.vars =
                                              uu____6666;_},uu____6667)
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
                                     | uu____6685 ->
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
           let uu____6764 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____6764 with
            | (bs1,body1,opening) ->
                let fallback uu____6789 =
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
                  let uu____6799 =
                    let uu____6800 =
                      FStar_SMTEncoding_Term.mk_fv
                        (f, FStar_SMTEncoding_Term.Term_sort)
                       in
                    FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV
                      uu____6800
                     in
                  (uu____6799, [decl])  in
                let is_impure rc =
                  let uu____6811 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                      env.FStar_SMTEncoding_Env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____6811 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____6826 =
                          let uu____6839 =
                            FStar_TypeChecker_Env.get_range
                              env.FStar_SMTEncoding_Env.tcenv
                             in
                          FStar_TypeChecker_Util.new_implicit_var
                            "SMTEncoding codomain" uu____6839
                            env.FStar_SMTEncoding_Env.tcenv
                            FStar_Syntax_Util.ktype0
                           in
                        (match uu____6826 with
                         | (t1,uu____6842,uu____6843) -> t1)
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  let uu____6861 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                     in
                  if uu____6861
                  then
                    let uu____6866 = FStar_Syntax_Syntax.mk_Total res_typ  in
                    FStar_Pervasives_Native.Some uu____6866
                  else
                    (let uu____6869 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid
                        in
                     if uu____6869
                     then
                       let uu____6874 = FStar_Syntax_Syntax.mk_GTotal res_typ
                          in
                       FStar_Pervasives_Native.Some uu____6874
                     else FStar_Pervasives_Native.None)
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____6882 =
                         let uu____6888 =
                           let uu____6890 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____6890
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____6888)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____6882);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____6895 =
                       (is_impure rc) &&
                         (let uu____6898 =
                            FStar_TypeChecker_Env.is_reifiable_rc
                              env.FStar_SMTEncoding_Env.tcenv rc
                             in
                          Prims.op_Negation uu____6898)
                        in
                     if uu____6895
                     then fallback ()
                     else
                       (let cache_size =
                          FStar_Util.smap_size
                            env.FStar_SMTEncoding_Env.cache
                           in
                        let uu____6909 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____6909 with
                        | (vars,guards,envbody,decls,uu____6934) ->
                            let body2 =
                              let uu____6948 =
                                FStar_TypeChecker_Env.is_reifiable_rc
                                  env.FStar_SMTEncoding_Env.tcenv rc
                                 in
                              if uu____6948
                              then
                                FStar_TypeChecker_Util.reify_body
                                  env.FStar_SMTEncoding_Env.tcenv body1
                              else body1  in
                            let uu____6953 = encode_term body2 envbody  in
                            (match uu____6953 with
                             | (body3,decls') ->
                                 let uu____6964 =
                                   let uu____6973 = codomain_eff rc  in
                                   match uu____6973 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____6992 = encode_term tfun env
                                          in
                                       (match uu____6992 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____6964 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____7026 =
                                          let uu____7037 =
                                            let uu____7038 =
                                              let uu____7043 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____7043, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____7038
                                             in
                                          ([], vars, uu____7037)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t0.FStar_Syntax_Syntax.pos
                                          uu____7026
                                         in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body
                                         in
                                      let uu____7051 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            (cvars, key_body)
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____7067 =
                                              let uu____7070 =
                                                let uu____7081 =
                                                  FStar_SMTEncoding_Term.free_variables
                                                    t1
                                                   in
                                                FStar_List.append uu____7081
                                                  cvars
                                                 in
                                              FStar_Util.remove_dups
                                                FStar_SMTEncoding_Term.fv_eq
                                                uu____7070
                                               in
                                            let uu____7108 =
                                              FStar_SMTEncoding_Util.mkAnd
                                                (key_body, t1)
                                               in
                                            (uu____7067, uu____7108)
                                         in
                                      (match uu____7051 with
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
                                           let uu____7130 =
                                             FStar_Util.smap_try_find
                                               env.FStar_SMTEncoding_Env.cache
                                               tkey_hash
                                              in
                                           (match uu____7130 with
                                            | FStar_Pervasives_Native.Some
                                                cache_entry ->
                                                let uu____7138 =
                                                  let uu____7139 =
                                                    let uu____7147 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                                      uu____7147)
                                                     in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____7139
                                                   in
                                                (uu____7138,
                                                  (FStar_List.append decls
                                                     (FStar_List.append
                                                        decls'
                                                        (FStar_List.append
                                                           decls''
                                                           (FStar_SMTEncoding_Env.use_cache_entry
                                                              cache_entry)))))
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                let uu____7153 =
                                                  is_an_eta_expansion env
                                                    vars body3
                                                   in
                                                (match uu____7153 with
                                                 | FStar_Pervasives_Native.Some
                                                     t1 ->
                                                     let decls1 =
                                                       let uu____7162 =
                                                         let uu____7164 =
                                                           FStar_Util.smap_size
                                                             env.FStar_SMTEncoding_Env.cache
                                                            in
                                                         uu____7164 =
                                                           cache_size
                                                          in
                                                       if uu____7162
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
                                                         let uu____7179 =
                                                           let uu____7181 =
                                                             FStar_Util.digest_of_string
                                                               tkey_hash
                                                              in
                                                           Prims.strcat
                                                             "Tm_abs_"
                                                             uu____7181
                                                            in
                                                         FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                           uu____7179
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
                                                       let uu____7191 =
                                                         let uu____7199 =
                                                           FStar_List.map
                                                             FStar_SMTEncoding_Util.mkFreeV
                                                             cvars1
                                                            in
                                                         (fsym, uu____7199)
                                                          in
                                                       FStar_SMTEncoding_Util.mkApp
                                                         uu____7191
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
                                                           let uu____7216 =
                                                             let uu____7217 =
                                                               let uu____7225
                                                                 =
                                                                 FStar_SMTEncoding_Term.mkForall
                                                                   t0.FStar_Syntax_Syntax.pos
                                                                   ([[f]],
                                                                    cvars1,
                                                                    f_has_t)
                                                                  in
                                                               (uu____7225,
                                                                 (FStar_Pervasives_Native.Some
                                                                    a_name),
                                                                 a_name)
                                                                in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____7217
                                                              in
                                                           [uu____7216]
                                                        in
                                                     let interp_f =
                                                       let a_name =
                                                         Prims.strcat
                                                           "interpretation_"
                                                           fsym
                                                          in
                                                       let uu____7240 =
                                                         let uu____7248 =
                                                           let uu____7249 =
                                                             let uu____7260 =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (app, body3)
                                                                in
                                                             ([[app]],
                                                               (FStar_List.append
                                                                  vars cvars1),
                                                               uu____7260)
                                                              in
                                                           FStar_SMTEncoding_Term.mkForall
                                                             t0.FStar_Syntax_Syntax.pos
                                                             uu____7249
                                                            in
                                                         (uu____7248,
                                                           (FStar_Pervasives_Native.Some
                                                              a_name),
                                                           a_name)
                                                          in
                                                       FStar_SMTEncoding_Util.mkAssume
                                                         uu____7240
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
                                                     ((let uu____7275 =
                                                         FStar_SMTEncoding_Env.mk_cache_entry
                                                           env fsym
                                                           cvar_sorts f_decls
                                                          in
                                                       FStar_Util.smap_add
                                                         env.FStar_SMTEncoding_Env.cache
                                                         tkey_hash uu____7275);
                                                      (f, f_decls))))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____7276,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____7277;
                          FStar_Syntax_Syntax.lbunivs = uu____7278;
                          FStar_Syntax_Syntax.lbtyp = uu____7279;
                          FStar_Syntax_Syntax.lbeff = uu____7280;
                          FStar_Syntax_Syntax.lbdef = uu____7281;
                          FStar_Syntax_Syntax.lbattrs = uu____7282;
                          FStar_Syntax_Syntax.lbpos = uu____7283;_}::uu____7284),uu____7285)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____7319;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____7321;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____7323;
                FStar_Syntax_Syntax.lbpos = uu____7324;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____7351 ->
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
              let uu____7423 =
                let uu____7428 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____7428 env  in
              match uu____7423 with
              | (ee1,decls1) ->
                  let uu____7453 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____7453 with
                   | (xs,e21) ->
                       let uu____7478 = FStar_List.hd xs  in
                       (match uu____7478 with
                        | (x1,uu____7496) ->
                            let env' =
                              FStar_SMTEncoding_Env.push_term_var env x1 ee1
                               in
                            let uu____7502 = encode_body e21 env'  in
                            (match uu____7502 with
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
            let uu____7532 =
              let uu____7540 =
                let uu____7541 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____7541  in
              FStar_SMTEncoding_Env.gen_term_var env uu____7540  in
            match uu____7532 with
            | (scrsym,scr',env1) ->
                let uu____7551 = encode_term e env1  in
                (match uu____7551 with
                 | (scr,decls) ->
                     let uu____7562 =
                       let encode_branch b uu____7591 =
                         match uu____7591 with
                         | (else_case,decls1) ->
                             let uu____7610 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____7610 with
                              | (p,w,br) ->
                                  let uu____7636 = encode_pat env1 p  in
                                  (match uu____7636 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____7673  ->
                                                   match uu____7673 with
                                                   | (x,t) ->
                                                       FStar_SMTEncoding_Env.push_term_var
                                                         env2 x t) env1)
                                          in
                                       let uu____7680 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____7702 =
                                               encode_term w1 env2  in
                                             (match uu____7702 with
                                              | (w2,decls2) ->
                                                  let uu____7715 =
                                                    let uu____7716 =
                                                      let uu____7721 =
                                                        let uu____7722 =
                                                          let uu____7727 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____7727)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____7722
                                                         in
                                                      (guard, uu____7721)  in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____7716
                                                     in
                                                  (uu____7715, decls2))
                                          in
                                       (match uu____7680 with
                                        | (guard1,decls2) ->
                                            let uu____7742 =
                                              encode_br br env2  in
                                            (match uu____7742 with
                                             | (br1,decls3) ->
                                                 let uu____7755 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____7755,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____7562 with
                      | (match_tm,decls1) ->
                          let uu____7776 =
                            let uu____7777 =
                              let uu____7788 =
                                let uu____7795 =
                                  let uu____7800 =
                                    FStar_SMTEncoding_Term.mk_fv
                                      (scrsym,
                                        FStar_SMTEncoding_Term.Term_sort)
                                     in
                                  (uu____7800, scr)  in
                                [uu____7795]  in
                              (uu____7788, match_tm)  in
                            FStar_SMTEncoding_Term.mkLet' uu____7777
                              FStar_Range.dummyRange
                             in
                          (uu____7776, decls1)))

and (encode_pat :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.pat -> (FStar_SMTEncoding_Env.env_t * pattern))
  =
  fun env  ->
    fun pat  ->
      (let uu____7823 =
         FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
           FStar_Options.Medium
          in
       if uu____7823
       then
         let uu____7826 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____7826
       else ());
      (let uu____7831 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____7831 with
       | (vars,pat_term) ->
           let uu____7848 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____7890  ->
                     fun v1  ->
                       match uu____7890 with
                       | (env1,vars1) ->
                           let uu____7926 =
                             FStar_SMTEncoding_Env.gen_term_var env1 v1  in
                           (match uu____7926 with
                            | (xx,uu____7945,env2) ->
                                let uu____7949 =
                                  let uu____7956 =
                                    let uu____7961 =
                                      FStar_SMTEncoding_Term.mk_fv
                                        (xx,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    (v1, uu____7961)  in
                                  uu____7956 :: vars1  in
                                (env2, uu____7949))) (env, []))
              in
           (match uu____7848 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____8016 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____8017 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____8018 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____8026 = encode_const c env1  in
                      (match uu____8026 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____8034::uu____8035 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____8039 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon
                            env1.FStar_SMTEncoding_Env.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____8062 =
                          FStar_TypeChecker_Env.datacons_of_typ
                            env1.FStar_SMTEncoding_Env.tcenv tc_name
                           in
                        match uu____8062 with
                        | (uu____8070,uu____8071::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____8076 ->
                            FStar_SMTEncoding_Env.mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____8112  ->
                                  match uu____8112 with
                                  | (arg,uu____8122) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____8131 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____8131))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____8163) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____8194 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____8219 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____8265  ->
                                  match uu____8265 with
                                  | (arg,uu____8281) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____8290 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____8290))
                         in
                      FStar_All.pipe_right uu____8219 FStar_List.flatten
                   in
                let pat_term1 uu____8321 = encode_term pat_term env1  in
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
      let uu____8331 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____8379  ->
                fun uu____8380  ->
                  match (uu____8379, uu____8380) with
                  | ((tms,decls),(t,uu____8420)) ->
                      let uu____8447 = encode_term t env  in
                      (match uu____8447 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____8331 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____8504 = FStar_Syntax_Util.list_elements e  in
        match uu____8504 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____8535 =
          let uu____8552 = FStar_Syntax_Util.unmeta p  in
          FStar_All.pipe_right uu____8552 FStar_Syntax_Util.head_and_args  in
        match uu____8535 with
        | (head1,args) ->
            let uu____8603 =
              let uu____8618 =
                let uu____8619 = FStar_Syntax_Util.un_uinst head1  in
                uu____8619.FStar_Syntax_Syntax.n  in
              (uu____8618, args)  in
            (match uu____8603 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____8641,uu____8642)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____8694 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or1 t1 =
          let uu____8749 =
            let uu____8766 = FStar_Syntax_Util.unmeta t1  in
            FStar_All.pipe_right uu____8766 FStar_Syntax_Util.head_and_args
             in
          match uu____8749 with
          | (head1,args) ->
              let uu____8813 =
                let uu____8828 =
                  let uu____8829 = FStar_Syntax_Util.un_uinst head1  in
                  uu____8829.FStar_Syntax_Syntax.n  in
                (uu____8828, args)  in
              (match uu____8813 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____8848)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____8885 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____8915 = smt_pat_or1 t1  in
            (match uu____8915 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____8937 = list_elements1 e  in
                 FStar_All.pipe_right uu____8937
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____8967 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____8967
                           (FStar_List.map one_pat)))
             | uu____8990 ->
                 let uu____8995 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____8995])
        | uu____9046 ->
            let uu____9049 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____9049]
         in
      let uu____9100 =
        let uu____9115 =
          let uu____9116 = FStar_Syntax_Subst.compress t  in
          uu____9116.FStar_Syntax_Syntax.n  in
        match uu____9115 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____9155 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____9155 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____9190;
                        FStar_Syntax_Syntax.effect_name = uu____9191;
                        FStar_Syntax_Syntax.result_typ = uu____9192;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____9194)::(post,uu____9196)::(pats,uu____9198)::[];
                        FStar_Syntax_Syntax.flags = uu____9199;_}
                      ->
                      let uu____9260 = lemma_pats pats  in
                      (binders1, pre, post, uu____9260)
                  | uu____9271 -> failwith "impos"))
        | uu____9287 -> failwith "Impos"  in
      match uu____9100 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___368_9324 = env  in
            {
              FStar_SMTEncoding_Env.bvar_bindings =
                (uu___368_9324.FStar_SMTEncoding_Env.bvar_bindings);
              FStar_SMTEncoding_Env.fvar_bindings =
                (uu___368_9324.FStar_SMTEncoding_Env.fvar_bindings);
              FStar_SMTEncoding_Env.depth =
                (uu___368_9324.FStar_SMTEncoding_Env.depth);
              FStar_SMTEncoding_Env.tcenv =
                (uu___368_9324.FStar_SMTEncoding_Env.tcenv);
              FStar_SMTEncoding_Env.warn =
                (uu___368_9324.FStar_SMTEncoding_Env.warn);
              FStar_SMTEncoding_Env.cache =
                (uu___368_9324.FStar_SMTEncoding_Env.cache);
              FStar_SMTEncoding_Env.nolabels =
                (uu___368_9324.FStar_SMTEncoding_Env.nolabels);
              FStar_SMTEncoding_Env.use_zfuel_name = true;
              FStar_SMTEncoding_Env.encode_non_total_function_typ =
                (uu___368_9324.FStar_SMTEncoding_Env.encode_non_total_function_typ);
              FStar_SMTEncoding_Env.current_module_name =
                (uu___368_9324.FStar_SMTEncoding_Env.current_module_name);
              FStar_SMTEncoding_Env.encoding_quantifier =
                (uu___368_9324.FStar_SMTEncoding_Env.encoding_quantifier)
            }  in
          let uu____9326 =
            encode_binders FStar_Pervasives_Native.None binders env1  in
          (match uu____9326 with
           | (vars,guards,env2,decls,uu____9351) ->
               let uu____9364 = encode_smt_patterns patterns env2  in
               (match uu____9364 with
                | (pats,decls') ->
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
                    let env3 =
                      let uu___369_9397 = env2  in
                      {
                        FStar_SMTEncoding_Env.bvar_bindings =
                          (uu___369_9397.FStar_SMTEncoding_Env.bvar_bindings);
                        FStar_SMTEncoding_Env.fvar_bindings =
                          (uu___369_9397.FStar_SMTEncoding_Env.fvar_bindings);
                        FStar_SMTEncoding_Env.depth =
                          (uu___369_9397.FStar_SMTEncoding_Env.depth);
                        FStar_SMTEncoding_Env.tcenv =
                          (uu___369_9397.FStar_SMTEncoding_Env.tcenv);
                        FStar_SMTEncoding_Env.warn =
                          (uu___369_9397.FStar_SMTEncoding_Env.warn);
                        FStar_SMTEncoding_Env.cache =
                          (uu___369_9397.FStar_SMTEncoding_Env.cache);
                        FStar_SMTEncoding_Env.nolabels = true;
                        FStar_SMTEncoding_Env.use_zfuel_name =
                          (uu___369_9397.FStar_SMTEncoding_Env.use_zfuel_name);
                        FStar_SMTEncoding_Env.encode_non_total_function_typ =
                          (uu___369_9397.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                        FStar_SMTEncoding_Env.current_module_name =
                          (uu___369_9397.FStar_SMTEncoding_Env.current_module_name);
                        FStar_SMTEncoding_Env.encoding_quantifier =
                          (uu___369_9397.FStar_SMTEncoding_Env.encoding_quantifier)
                      }  in
                    let uu____9399 =
                      let uu____9404 = FStar_Syntax_Util.unmeta pre  in
                      encode_formula uu____9404 env3  in
                    (match uu____9399 with
                     | (pre1,decls'') ->
                         let uu____9411 =
                           let uu____9416 = FStar_Syntax_Util.unmeta post1
                              in
                           encode_formula uu____9416 env3  in
                         (match uu____9411 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append decls'
                                     (FStar_List.append decls'' decls'''))
                                 in
                              let uu____9426 =
                                let uu____9427 =
                                  let uu____9438 =
                                    let uu____9439 =
                                      let uu____9444 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards)
                                         in
                                      (uu____9444, post2)  in
                                    FStar_SMTEncoding_Util.mkImp uu____9439
                                     in
                                  (pats, vars, uu____9438)  in
                                FStar_SMTEncoding_Term.mkForall
                                  t.FStar_Syntax_Syntax.pos uu____9427
                                 in
                              (uu____9426, decls1)))))

and (encode_smt_patterns :
  FStar_Syntax_Syntax.arg Prims.list Prims.list ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term Prims.list Prims.list *
        FStar_SMTEncoding_Term.decl Prims.list))
  =
  fun pats_l  ->
    fun env  ->
      let env1 =
        let uu___370_9466 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___370_9466.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___370_9466.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___370_9466.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___370_9466.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___370_9466.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.cache =
            (uu___370_9466.FStar_SMTEncoding_Env.cache);
          FStar_SMTEncoding_Env.nolabels =
            (uu___370_9466.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___370_9466.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___370_9466.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___370_9466.FStar_SMTEncoding_Env.encoding_quantifier)
        }  in
      let encode_smt_pattern t =
        let uu____9482 = FStar_Syntax_Util.head_and_args t  in
        match uu____9482 with
        | (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____9545::(x,uu____9547)::(t1,uu____9549)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____9616 = encode_term x env1  in
                 (match uu____9616 with
                  | (x1,decls) ->
                      let uu____9627 = encode_term t1 env1  in
                      (match uu____9627 with
                       | (t2,decls') ->
                           let uu____9638 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                           (uu____9638, (FStar_List.append decls decls'))))
             | uu____9639 -> encode_term t env1)
         in
      FStar_List.fold_right
        (fun pats  ->
           fun uu____9682  ->
             match uu____9682 with
             | (pats_l1,decls) ->
                 let uu____9727 =
                   FStar_List.fold_right
                     (fun uu____9762  ->
                        fun uu____9763  ->
                          match (uu____9762, uu____9763) with
                          | ((p,uu____9805),(pats1,decls1)) ->
                              let uu____9840 = encode_smt_pattern p  in
                              (match uu____9840 with
                               | (t,d) ->
                                   let uu____9855 =
                                     FStar_SMTEncoding_Term.check_pattern_ok
                                       t
                                      in
                                   (match uu____9855 with
                                    | FStar_Pervasives_Native.None  ->
                                        ((t :: pats1),
                                          (FStar_List.append d decls1))
                                    | FStar_Pervasives_Native.Some
                                        illegal_subterm ->
                                        ((let uu____9872 =
                                            let uu____9878 =
                                              let uu____9880 =
                                                FStar_Syntax_Print.term_to_string
                                                  p
                                                 in
                                              let uu____9882 =
                                                FStar_SMTEncoding_Term.print_smt_term
                                                  illegal_subterm
                                                 in
                                              FStar_Util.format2
                                                "Pattern %s contains illegal sub-term (%s); dropping it"
                                                uu____9880 uu____9882
                                               in
                                            (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                                              uu____9878)
                                             in
                                          FStar_Errors.log_issue
                                            p.FStar_Syntax_Syntax.pos
                                            uu____9872);
                                         (pats1,
                                           (FStar_List.append d decls1))))))
                     pats ([], decls)
                    in
                 (match uu____9727 with
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
        let uu____9942 =
          FStar_All.pipe_left
            (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____9942
        then
          let uu____9947 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____9949 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____9947 uu____9949
        else ()  in
      let enc f r l =
        let uu____9991 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10023 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____10023 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____9991 with
        | (decls,args) ->
            let uu____10054 =
              let uu___371_10055 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___371_10055.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___371_10055.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10054, decls)
         in
      let const_op f r uu____10090 =
        let uu____10103 = f r  in (uu____10103, [])  in
      let un_op f l =
        let uu____10126 = FStar_List.hd l  in
        FStar_All.pipe_left f uu____10126  in
      let bin_op f uu___362_10146 =
        match uu___362_10146 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10157 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____10198 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____10223  ->
                 match uu____10223 with
                 | (t,uu____10239) ->
                     let uu____10244 = encode_formula t env  in
                     (match uu____10244 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____10198 with
        | (decls,phis) ->
            let uu____10273 =
              let uu___372_10274 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___372_10274.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___372_10274.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10273, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____10337  ->
               match uu____10337 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____10358) -> false
                    | uu____10361 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____10380 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____10380
        else
          (let uu____10397 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____10397 r rf)
         in
      let eq3_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____10469 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::t1::v0::v1::[] ->
                     let uu____10501 =
                       let uu____10506 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____10507 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____10506, uu____10507)  in
                     FStar_SMTEncoding_Util.mkAnd uu____10501
                 | uu____10508 -> failwith "Impossible")
             in
          uu____10469 r args
        else
          (let uu____10514 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____10514)
         in
      let h_equals_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____10586 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::v0::t1::v1::[] ->
                     let uu____10618 =
                       let uu____10623 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____10624 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____10623, uu____10624)  in
                     FStar_SMTEncoding_Util.mkAnd uu____10618
                 | uu____10625 -> failwith "Impossible")
             in
          uu____10586 r args
        else
          (let uu____10631 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____10631)
         in
      let mk_imp1 r uu___363_10666 =
        match uu___363_10666 with
        | (lhs,uu____10672)::(rhs,uu____10674)::[] ->
            let uu____10715 = encode_formula rhs env  in
            (match uu____10715 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____10730) ->
                      (l1, decls1)
                  | uu____10735 ->
                      let uu____10736 = encode_formula lhs env  in
                      (match uu____10736 with
                       | (l2,decls2) ->
                           let uu____10747 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____10747, (FStar_List.append decls1 decls2)))))
        | uu____10748 -> failwith "impossible"  in
      let mk_ite r uu___364_10776 =
        match uu___364_10776 with
        | (guard,uu____10782)::(_then,uu____10784)::(_else,uu____10786)::[]
            ->
            let uu____10843 = encode_formula guard env  in
            (match uu____10843 with
             | (g,decls1) ->
                 let uu____10854 = encode_formula _then env  in
                 (match uu____10854 with
                  | (t,decls2) ->
                      let uu____10865 = encode_formula _else env  in
                      (match uu____10865 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____10877 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____10907 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l
           in
        f uu____10907  in
      let connectives =
        let uu____10937 =
          let uu____10962 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____10962)  in
        let uu____11005 =
          let uu____11032 =
            let uu____11057 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____11057)  in
          let uu____11100 =
            let uu____11127 =
              let uu____11154 =
                let uu____11179 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____11179)  in
              let uu____11222 =
                let uu____11249 =
                  let uu____11276 =
                    let uu____11301 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____11301)  in
                  [uu____11276;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.c_eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq3_op);
                  (FStar_Parser_Const.c_eq3_lid, h_equals_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11249  in
              uu____11154 :: uu____11222  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11127  in
          uu____11032 :: uu____11100  in
        uu____10937 :: uu____11005  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____11846 = encode_formula phi' env  in
            (match uu____11846 with
             | (phi2,decls) ->
                 let uu____11857 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____11857, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____11859 ->
            let uu____11866 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____11866 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____11905 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____11905 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____11917;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____11919;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____11921;
                 FStar_Syntax_Syntax.lbpos = uu____11922;_}::[]),e2)
            ->
            let uu____11949 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____11949 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____12002::(x,uu____12004)::(t,uu____12006)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12073 = encode_term x env  in
                 (match uu____12073 with
                  | (x1,decls) ->
                      let uu____12084 = encode_term t env  in
                      (match uu____12084 with
                       | (t1,decls') ->
                           let uu____12095 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____12095, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12098)::(msg,uu____12100)::(phi2,uu____12102)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12169 =
                   let uu____12174 =
                     let uu____12175 = FStar_Syntax_Subst.compress r  in
                     uu____12175.FStar_Syntax_Syntax.n  in
                   let uu____12178 =
                     let uu____12179 = FStar_Syntax_Subst.compress msg  in
                     uu____12179.FStar_Syntax_Syntax.n  in
                   (uu____12174, uu____12178)  in
                 (match uu____12169 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12188))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____12199 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____12206)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____12241 when head_redex env head2 ->
                 let uu____12256 = whnf env phi1  in
                 encode_formula uu____12256 env
             | uu____12257 ->
                 let uu____12272 = encode_term phi1 env  in
                 (match uu____12272 with
                  | (tt,decls) ->
                      let tt1 =
                        let uu____12284 =
                          let uu____12286 =
                            FStar_Range.use_range
                              tt.FStar_SMTEncoding_Term.rng
                             in
                          let uu____12287 =
                            FStar_Range.use_range
                              phi1.FStar_Syntax_Syntax.pos
                             in
                          FStar_Range.rng_included uu____12286 uu____12287
                           in
                        if uu____12284
                        then tt
                        else
                          (let uu___373_12291 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___373_12291.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___373_12291.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      let uu____12292 = FStar_SMTEncoding_Term.mk_Valid tt1
                         in
                      (uu____12292, decls)))
        | uu____12293 ->
            let uu____12294 = encode_term phi1 env  in
            (match uu____12294 with
             | (tt,decls) ->
                 let tt1 =
                   let uu____12306 =
                     let uu____12308 =
                       FStar_Range.use_range tt.FStar_SMTEncoding_Term.rng
                        in
                     let uu____12309 =
                       FStar_Range.use_range phi1.FStar_Syntax_Syntax.pos  in
                     FStar_Range.rng_included uu____12308 uu____12309  in
                   if uu____12306
                   then tt
                   else
                     (let uu___374_12313 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___374_12313.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___374_12313.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 let uu____12314 = FStar_SMTEncoding_Term.mk_Valid tt1  in
                 (uu____12314, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____12358 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____12358 with
        | (vars,guards,env2,decls,uu____12397) ->
            let uu____12410 = encode_smt_patterns ps env2  in
            (match uu____12410 with
             | (pats,decls') ->
                 let uu____12453 = encode_formula body env2  in
                 (match uu____12453 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12485;
                             FStar_SMTEncoding_Term.rng = uu____12486;_}::[])::[]
                            when
                            let uu____12506 =
                              FStar_Ident.text_of_lid
                                FStar_Parser_Const.guard_free
                               in
                            uu____12506 = gf -> []
                        | uu____12509 -> guards  in
                      let uu____12514 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____12514, body1,
                        (FStar_List.append decls
                           (FStar_List.append decls' decls'')))))
         in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi  in
       let uu____12525 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____12525 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12534 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____12640  ->
                     match uu____12640 with
                     | (l,uu____12665) -> FStar_Ident.lid_equals op l))
              in
           (match uu____12534 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____12734,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____12826 = encode_q_body env vars pats body  in
             match uu____12826 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____12871 =
                     let uu____12882 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____12882)  in
                   FStar_SMTEncoding_Term.mkForall
                     phi1.FStar_Syntax_Syntax.pos uu____12871
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____12913 = encode_q_body env vars pats body  in
             match uu____12913 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____12957 =
                   let uu____12958 =
                     let uu____12969 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____12969)  in
                   FStar_SMTEncoding_Term.mkExists
                     phi1.FStar_Syntax_Syntax.pos uu____12958
                    in
                 (uu____12957, decls))))
