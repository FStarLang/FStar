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
                   let vars1 = (fsym, FStar_SMTEncoding_Term.Fuel_sort) ::
                     vars  in
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
      | FStar_Syntax_Syntax.Tm_arrow uu____195 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____211 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____219 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____221 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____235 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____255 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____258 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____258 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____277;
             FStar_Syntax_Syntax.vars = uu____278;_},uu____279)
          ->
          let uu____304 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____304 FStar_Option.isNone
      | uu____322 -> false
  
let (head_redex :
  FStar_SMTEncoding_Env.env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____336 =
        let uu____337 = FStar_Syntax_Util.un_uinst t  in
        uu____337.FStar_Syntax_Syntax.n  in
      match uu____336 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____341,uu____342,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___359_367  ->
                  match uu___359_367 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____370 -> false) rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____373 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only]
              env.FStar_SMTEncoding_Env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____373 FStar_Option.isSome
      | uu____391 -> false
  
let (whnf :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____404 = head_normal env t  in
      if uu____404
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
    let uu____426 =
      let uu____427 = FStar_Syntax_Syntax.null_binder t  in [uu____427]  in
    let uu____446 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    FStar_Syntax_Util.abs uu____426 uu____446 FStar_Pervasives_Native.None
  
let (mk_Apply :
  FStar_SMTEncoding_Term.term ->
    (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list ->
      FStar_SMTEncoding_Term.term)
  =
  fun e  ->
    fun vars  ->
      FStar_All.pipe_right vars
        (FStar_List.fold_left
           (fun out  ->
              fun var  ->
                match FStar_Pervasives_Native.snd var with
                | FStar_SMTEncoding_Term.Fuel_sort  ->
                    let uu____497 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____497
                | s ->
                    let uu____500 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____500) e)
  
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
          let uu____556 =
            let uu____562 =
              let uu____564 = FStar_Util.string_of_int arity  in
              let uu____566 = FStar_Util.string_of_int n_args  in
              FStar_Util.format3
                "Head symbol %s expects at least %s arguments; got only %s"
                head1 uu____564 uu____566
               in
            (FStar_Errors.Fatal_SMTEncodingArityMismatch, uu____562)  in
          FStar_Errors.raise_error uu____556 rng
  
let (maybe_curry_app :
  FStar_Range.range ->
    FStar_SMTEncoding_Term.op ->
      Prims.int ->
        FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term)
  =
  fun rng  ->
    fun head1  ->
      fun arity  ->
        fun args  ->
          let n_args = FStar_List.length args  in
          if n_args = arity
          then FStar_SMTEncoding_Util.mkApp' (head1, args)
          else
            if n_args > arity
            then
              (let uu____615 = FStar_Util.first_N arity args  in
               match uu____615 with
               | (args1,rest) ->
                   let head2 = FStar_SMTEncoding_Util.mkApp' (head1, args1)
                      in
                   mk_Apply_args head2 rest)
            else
              (let uu____639 = FStar_SMTEncoding_Term.op_to_string head1  in
               raise_arity_mismatch uu____639 arity n_args rng)
  
let (maybe_curry_fvb :
  FStar_Range.range ->
    FStar_SMTEncoding_Env.fvar_binding ->
      FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term)
  =
  fun rng  ->
    fun fvb  ->
      fun args  ->
        maybe_curry_app rng
          (FStar_SMTEncoding_Term.Var (fvb.FStar_SMTEncoding_Env.smt_id))
          fvb.FStar_SMTEncoding_Env.smt_arity args
  
let (is_app : FStar_SMTEncoding_Term.op -> Prims.bool) =
  fun uu___360_671  ->
    match uu___360_671 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____677 -> false
  
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
                       FStar_SMTEncoding_Term.freevars = uu____725;
                       FStar_SMTEncoding_Term.rng = uu____726;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____751) ->
              let uu____761 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____775 -> false) args (FStar_List.rev xs))
                 in
              if uu____761
              then FStar_SMTEncoding_Env.tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____782,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t  in
              let uu____786 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____794 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars
                           in
                        Prims.op_Negation uu____794))
                 in
              if uu____786
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____801 -> FStar_Pervasives_Native.None  in
        check_partial_applications body (FStar_List.rev vars)
  
let check_pattern_vars :
  'Auu____819 'Auu____820 .
    FStar_SMTEncoding_Env.env_t ->
      (FStar_Syntax_Syntax.bv * 'Auu____819) Prims.list ->
        (FStar_Syntax_Syntax.term * 'Auu____820) Prims.list -> unit
  =
  fun env  ->
    fun vars  ->
      fun pats  ->
        let pats1 =
          FStar_All.pipe_right pats
            (FStar_List.map
               (fun uu____878  ->
                  match uu____878 with
                  | (x,uu____884) ->
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
              let uu____892 = FStar_Syntax_Free.names hd1  in
              FStar_List.fold_left
                (fun out  ->
                   fun x  ->
                     let uu____904 = FStar_Syntax_Free.names x  in
                     FStar_Util.set_union out uu____904) uu____892 tl1
               in
            let uu____907 =
              FStar_All.pipe_right vars
                (FStar_Util.find_opt
                   (fun uu____934  ->
                      match uu____934 with
                      | (b,uu____941) ->
                          let uu____942 = FStar_Util.set_mem b pat_vars  in
                          Prims.op_Negation uu____942))
               in
            (match uu____907 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some (x,uu____949) ->
                 let pos =
                   FStar_List.fold_left
                     (fun out  ->
                        fun t  ->
                          FStar_Range.union_ranges out
                            t.FStar_Syntax_Syntax.pos)
                     hd1.FStar_Syntax_Syntax.pos tl1
                    in
                 let uu____963 =
                   let uu____969 =
                     let uu____971 = FStar_Syntax_Print.bv_to_string x  in
                     FStar_Util.format1
                       "SMT pattern misses at least one bound variable: %s"
                       uu____971
                      in
                   (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                     uu____969)
                    in
                 FStar_Errors.log_issue pos uu____963)
  
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
        | FStar_Syntax_Syntax.Tm_arrow uu____1257 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____1272 ->
            let uu____1279 = FStar_Syntax_Util.unrefine t1  in
            aux true uu____1279
        | uu____1281 ->
            if norm1
            then let uu____1283 = whnf env t1  in aux false uu____1283
            else
              (let uu____1287 =
                 let uu____1289 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let uu____1291 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____1289 uu____1291
                  in
               failwith uu____1287)
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
    | FStar_Syntax_Syntax.Tm_refine (bv,uu____1333) ->
        curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort
    | uu____1338 ->
        let uu____1339 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____1339)
  
let is_arithmetic_primitive :
  'Auu____1353 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____1353 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1376::uu____1377::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1381::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____1384 -> false
  
let (isInteger : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____1415 -> false
  
let (getInteger : FStar_Syntax_Syntax.term' -> Prims.int) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____1438 -> failwith "Expected an Integer term"
  
let is_BitVector_primitive :
  'Auu____1448 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____1448)
        Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____1490)::uu____1491::uu____1492::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____1543)::uu____1544::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____1581 -> false
  
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
          let uu____1905 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue  in
          (uu____1905, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____1907 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse  in
          (uu____1907, [])
      | FStar_Const.Const_char c1 ->
          let uu____1910 =
            let uu____1911 =
              let uu____1919 =
                let uu____1922 =
                  let uu____1923 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1)
                     in
                  FStar_SMTEncoding_Term.boxInt uu____1923  in
                [uu____1922]  in
              ("FStar.Char.__char_of_int", uu____1919)  in
            FStar_SMTEncoding_Util.mkApp uu____1911  in
          (uu____1910, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____1941 =
            let uu____1942 = FStar_SMTEncoding_Util.mkInteger i  in
            FStar_SMTEncoding_Term.boxInt uu____1942  in
          (uu____1941, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.FStar_SMTEncoding_Env.tcenv).FStar_TypeChecker_Env.dsenv
              repr sw FStar_Range.dummyRange
             in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____1963) ->
          let uu____1966 =
            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.string_const s
             in
          (uu____1966, [])
      | FStar_Const.Const_range uu____1967 ->
          let uu____1968 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          (uu____1968, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | c1 ->
          let uu____1970 =
            let uu____1972 = FStar_Syntax_Print.const_to_string c1  in
            FStar_Util.format1 "Unhandled constant: %s" uu____1972  in
          failwith uu____1970

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
        (let uu____2001 =
           FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
             FStar_Options.Medium
            in
         if uu____2001
         then
           let uu____2004 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____2004
         else ());
        (let uu____2010 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2107  ->
                   fun b  ->
                     match uu____2107 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2192 =
                           let x = FStar_Pervasives_Native.fst b  in
                           let uu____2213 =
                             FStar_SMTEncoding_Env.gen_term_var env1 x  in
                           match uu____2213 with
                           | (xxsym,xx,env') ->
                               let uu____2243 =
                                 let uu____2248 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____2248 env1 xx
                                  in
                               (match uu____2243 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x))
                            in
                         (match uu____2192 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____2010 with
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
          let uu____2422 = encode_term t env  in
          match uu____2422 with
          | (t1,decls) ->
              let uu____2433 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____2433, decls)

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
          let uu____2444 = encode_term t env  in
          match uu____2444 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____2459 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____2459, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____2461 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____2461, decls))

and (encode_arith_term :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____2467 = encode_args args_e env  in
        match uu____2467 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____2486 -> failwith "Impossible"  in
            let unary arg_tms1 =
              let uu____2498 = FStar_List.hd arg_tms1  in
              FStar_SMTEncoding_Term.unboxInt uu____2498  in
            let binary arg_tms1 =
              let uu____2513 =
                let uu____2514 = FStar_List.hd arg_tms1  in
                FStar_SMTEncoding_Term.unboxInt uu____2514  in
              let uu____2515 =
                let uu____2516 =
                  let uu____2517 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____2517  in
                FStar_SMTEncoding_Term.unboxInt uu____2516  in
              (uu____2513, uu____2515)  in
            let mk_default uu____2525 =
              let uu____2526 =
                FStar_SMTEncoding_Env.lookup_free_var_sym env
                  head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____2526 with
              | (fname,fuel_args,arity) ->
                  let args = FStar_List.append fuel_args arg_tms  in
                  maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity
                    args
               in
            let mk_l op mk_args ts =
              let uu____2591 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____2591
              then
                let uu____2594 =
                  let uu____2595 = mk_args ts  in op uu____2595  in
                FStar_All.pipe_right uu____2594 FStar_SMTEncoding_Term.boxInt
              else mk_default ()  in
            let mk_nl nm op ts =
              let uu____2633 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____2633
              then
                let uu____2636 = binary ts  in
                match uu____2636 with
                | (t1,t2) ->
                    let uu____2643 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____2643
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____2649 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____2649
                 then
                   let uu____2652 =
                     let uu____2653 = binary ts  in op uu____2653  in
                   FStar_All.pipe_right uu____2652
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
            let uu____2818 =
              let uu____2828 =
                FStar_List.tryFind
                  (fun uu____2852  ->
                     match uu____2852 with
                     | (l,uu____2863) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____2828 FStar_Util.must  in
            (match uu____2818 with
             | (uu____2907,op) ->
                 let uu____2919 = op arg_tms  in (uu____2919, decls))

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
        let uu____2935 = FStar_List.hd args_e  in
        match uu____2935 with
        | (tm_sz,uu____2951) ->
            let uu____2960 = uu____2935  in
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let t_decls1 = FStar_SMTEncoding_Term.mkBvConstructor sz  in
              FStar_SMTEncoding_Term.mk_decls "" sz_key t_decls1 []  in
            let uu____2971 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____2997::(sz_arg,uu____2999)::uu____3000::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____3067 =
                    let uu____3068 = FStar_List.tail args_e  in
                    FStar_List.tail uu____3068  in
                  let uu____3095 =
                    let uu____3099 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____3099  in
                  (uu____3067, uu____3095)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____3106::(sz_arg,uu____3108)::uu____3109::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____3176 =
                    let uu____3178 = FStar_Syntax_Print.term_to_string sz_arg
                       in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____3178
                     in
                  failwith uu____3176
              | uu____3188 ->
                  let uu____3203 = FStar_List.tail args_e  in
                  (uu____3203, FStar_Pervasives_Native.None)
               in
            (match uu____2971 with
             | (arg_tms,ext_sz) ->
                 let uu____3230 = encode_args arg_tms env  in
                 (match uu____3230 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____3251 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____3263 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____3263  in
                      let unary_arith arg_tms2 =
                        let uu____3274 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____3274  in
                      let binary arg_tms2 =
                        let uu____3289 =
                          let uu____3290 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3290
                           in
                        let uu____3291 =
                          let uu____3292 =
                            let uu____3293 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____3293  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3292
                           in
                        (uu____3289, uu____3291)  in
                      let binary_arith arg_tms2 =
                        let uu____3310 =
                          let uu____3311 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3311
                           in
                        let uu____3312 =
                          let uu____3313 =
                            let uu____3314 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____3314  in
                          FStar_SMTEncoding_Term.unboxInt uu____3313  in
                        (uu____3310, uu____3312)  in
                      let mk_bv op mk_args resBox ts =
                        let uu____3372 =
                          let uu____3373 = mk_args ts  in op uu____3373  in
                        FStar_All.pipe_right uu____3372 resBox  in
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
                        let uu____3505 =
                          let uu____3510 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____3510  in
                        let uu____3519 =
                          let uu____3524 =
                            let uu____3526 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____3526  in
                          FStar_SMTEncoding_Term.boxBitVec uu____3524  in
                        mk_bv uu____3505 unary uu____3519 arg_tms2  in
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
                      let uu____3766 =
                        let uu____3776 =
                          FStar_List.tryFind
                            (fun uu____3800  ->
                               match uu____3800 with
                               | (l,uu____3811) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____3776 FStar_Util.must  in
                      (match uu____3766 with
                       | (uu____3857,op) ->
                           let uu____3869 = op arg_tms1  in
                           (uu____3869, (FStar_List.append sz_decls decls)))))

and (encode_deeply_embedded_quantifier :
  FStar_Syntax_Syntax.term ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let env1 =
        let uu___364_3879 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___364_3879.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___364_3879.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___364_3879.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___364_3879.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___364_3879.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___364_3879.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name =
            (uu___364_3879.FStar_SMTEncoding_Env.use_zfuel_name);
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___364_3879.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___364_3879.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier = true;
          FStar_SMTEncoding_Env.global_cache =
            (uu___364_3879.FStar_SMTEncoding_Env.global_cache)
        }  in
      let uu____3881 = encode_term t env1  in
      match uu____3881 with
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
               (uu____3907,{
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.FreeV uu____3908;
                             FStar_SMTEncoding_Term.freevars = uu____3909;
                             FStar_SMTEncoding_Term.rng = uu____3910;_}::
                {
                  FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV
                    uu____3911;
                  FStar_SMTEncoding_Term.freevars = uu____3912;
                  FStar_SMTEncoding_Term.rng = uu____3913;_}::[])
               ->
               (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                  (FStar_Errors.Warning_QuantifierWithoutPattern,
                    "Not encoding deeply embedded, unguarded quantifier to SMT");
                (tm, decls))
           | uu____3947 ->
               let uu____3948 = encode_formula t env1  in
               (match uu____3948 with
                | (phi,decls') ->
                    let interp =
                      match vars with
                      | [] ->
                          let uu____3965 =
                            let uu____3970 =
                              FStar_SMTEncoding_Term.mk_Valid tm  in
                            (uu____3970, phi)  in
                          FStar_SMTEncoding_Util.mkIff uu____3965
                      | uu____3971 ->
                          let uu____3972 =
                            let uu____3983 =
                              let uu____3984 =
                                let uu____3989 =
                                  FStar_SMTEncoding_Term.mk_Valid tm  in
                                (uu____3989, phi)  in
                              FStar_SMTEncoding_Util.mkIff uu____3984  in
                            ([[valid_tm]], vars, uu____3983)  in
                          FStar_SMTEncoding_Term.mkForall
                            t.FStar_Syntax_Syntax.pos uu____3972
                       in
                    let ax =
                      let uu____3999 =
                        let uu____4007 =
                          let uu____4009 =
                            FStar_Util.digest_of_string tkey_hash  in
                          Prims.strcat "l_quant_interp_" uu____4009  in
                        (interp,
                          (FStar_Pervasives_Native.Some
                             "Interpretation of deeply embedded quantifier"),
                          uu____4007)
                         in
                      FStar_SMTEncoding_Util.mkAssume uu____3999  in
                    let uu____4015 =
                      let uu____4016 =
                        let uu____4019 =
                          let uu____4022 =
                            FStar_SMTEncoding_Term.mk_decls "" tkey_hash 
                              [ax] decls
                             in
                          FStar_List.append uu____4022 decls'  in
                        FStar_List.append decls' uu____4019  in
                      FStar_List.append decls uu____4016  in
                    (tm, uu____4015)))

and (encode_term :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____4034 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____4034
       then
         let uu____4039 = FStar_Syntax_Print.tag_of_term t  in
         let uu____4041 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____4043 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____4039 uu____4041
           uu____4043
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____4052 ->
           let uu____4075 =
             let uu____4077 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____4080 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____4082 = FStar_Syntax_Print.term_to_string t0  in
             let uu____4084 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____4077
               uu____4080 uu____4082 uu____4084
              in
           failwith uu____4075
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____4091 =
             let uu____4093 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____4096 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____4098 = FStar_Syntax_Print.term_to_string t0  in
             let uu____4100 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____4093
               uu____4096 uu____4098 uu____4100
              in
           failwith uu____4091
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let e = FStar_Syntax_Util.unfold_lazy i  in
           ((let uu____4110 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____4110
             then
               let uu____4115 = FStar_Syntax_Print.term_to_string t0  in
               let uu____4117 = FStar_Syntax_Print.term_to_string e  in
               FStar_Util.print2 ">> Unfolded (%s) ~> (%s)\n" uu____4115
                 uu____4117
             else ());
            encode_term e env)
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____4123 =
             let uu____4125 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____4125
              in
           failwith uu____4123
       | FStar_Syntax_Syntax.Tm_ascribed (t1,(k,uu____4134),uu____4135) ->
           let uu____4184 =
             match k with
             | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
             | uu____4194 -> false  in
           if uu____4184
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t1 env
       | FStar_Syntax_Syntax.Tm_quoted (qt,uu____4212) ->
           let tv =
             let uu____4218 =
               let uu____4225 = FStar_Reflection_Basic.inspect_ln qt  in
               FStar_Syntax_Embeddings.embed
                 FStar_Reflection_Embeddings.e_term_view uu____4225
                in
             uu____4218 t.FStar_Syntax_Syntax.pos
               FStar_Pervasives_Native.None
               FStar_Syntax_Embeddings.id_norm_cb
              in
           ((let uu____4252 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____4252
             then
               let uu____4257 = FStar_Syntax_Print.term_to_string t0  in
               let uu____4259 = FStar_Syntax_Print.term_to_string tv  in
               FStar_Util.print2 ">> Inspected (%s) ~> (%s)\n" uu____4257
                 uu____4259
             else ());
            (let t1 =
               let uu____4267 =
                 let uu____4278 = FStar_Syntax_Syntax.as_arg tv  in
                 [uu____4278]  in
               FStar_Syntax_Util.mk_app
                 (FStar_Reflection_Data.refl_constant_term
                    FStar_Reflection_Data.fstar_refl_pack_ln) uu____4267
                in
             encode_term t1 env))
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_pattern uu____4304) ->
           encode_term t1
             (let uu___365_4322 = env  in
              {
                FStar_SMTEncoding_Env.bvar_bindings =
                  (uu___365_4322.FStar_SMTEncoding_Env.bvar_bindings);
                FStar_SMTEncoding_Env.fvar_bindings =
                  (uu___365_4322.FStar_SMTEncoding_Env.fvar_bindings);
                FStar_SMTEncoding_Env.depth =
                  (uu___365_4322.FStar_SMTEncoding_Env.depth);
                FStar_SMTEncoding_Env.tcenv =
                  (uu___365_4322.FStar_SMTEncoding_Env.tcenv);
                FStar_SMTEncoding_Env.warn =
                  (uu___365_4322.FStar_SMTEncoding_Env.warn);
                FStar_SMTEncoding_Env.nolabels =
                  (uu___365_4322.FStar_SMTEncoding_Env.nolabels);
                FStar_SMTEncoding_Env.use_zfuel_name =
                  (uu___365_4322.FStar_SMTEncoding_Env.use_zfuel_name);
                FStar_SMTEncoding_Env.encode_non_total_function_typ =
                  (uu___365_4322.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                FStar_SMTEncoding_Env.current_module_name =
                  (uu___365_4322.FStar_SMTEncoding_Env.current_module_name);
                FStar_SMTEncoding_Env.encoding_quantifier = false;
                FStar_SMTEncoding_Env.global_cache =
                  (uu___365_4322.FStar_SMTEncoding_Env.global_cache)
              })
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____4325) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = FStar_SMTEncoding_Env.lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____4333 = head_redex env t  in
           if uu____4333
           then let uu____4340 = whnf env t  in encode_term uu____4340 env
           else
             (let uu____4343 =
                FStar_SMTEncoding_Env.lookup_free_var_name env
                  v1.FStar_Syntax_Syntax.fv_name
                 in
              match uu____4343 with
              | (uu____4354,arity) ->
                  let tok =
                    FStar_SMTEncoding_Env.lookup_free_var env
                      v1.FStar_Syntax_Syntax.fv_name
                     in
                  let tkey_hash = FStar_SMTEncoding_Term.hash_of_term tok  in
                  let uu____4363 =
                    if arity > (Prims.parse_int "0")
                    then
                      match tok.FStar_SMTEncoding_Term.tm with
                      | FStar_SMTEncoding_Term.FreeV uu____4387 ->
                          let sym_name =
                            let uu____4395 =
                              FStar_Util.digest_of_string tkey_hash  in
                            Prims.strcat "@kick_partial_app_" uu____4395  in
                          let uu____4398 =
                            let uu____4401 =
                              let uu____4402 =
                                let uu____4410 =
                                  FStar_SMTEncoding_Term.kick_partial_app tok
                                   in
                                (uu____4410,
                                  (FStar_Pervasives_Native.Some
                                     "kick_partial_app"), sym_name)
                                 in
                              FStar_SMTEncoding_Util.mkAssume uu____4402  in
                            [uu____4401]  in
                          (uu____4398, sym_name)
                      | FStar_SMTEncoding_Term.App (uu____4417,[]) ->
                          let sym_name =
                            let uu____4422 =
                              FStar_Util.digest_of_string tkey_hash  in
                            Prims.strcat "@kick_partial_app_" uu____4422  in
                          let uu____4425 =
                            let uu____4428 =
                              let uu____4429 =
                                let uu____4437 =
                                  FStar_SMTEncoding_Term.kick_partial_app tok
                                   in
                                (uu____4437,
                                  (FStar_Pervasives_Native.Some
                                     "kick_partial_app"), sym_name)
                                 in
                              FStar_SMTEncoding_Util.mkAssume uu____4429  in
                            [uu____4428]  in
                          (uu____4425, sym_name)
                      | uu____4444 -> ([], "")
                    else ([], "")  in
                  (match uu____4363 with
                   | (aux_decls,sym_name) ->
                       let uu____4467 =
                         if aux_decls = []
                         then
                           FStar_All.pipe_right []
                             FStar_SMTEncoding_Term.mk_decls_trivial
                         else
                           FStar_SMTEncoding_Term.mk_decls sym_name tkey_hash
                             aux_decls []
                          in
                       (tok, uu____4467)))
       | FStar_Syntax_Syntax.Tm_type uu____4475 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4477) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.FStar_SMTEncoding_Env.current_module_name
              in
           let uu____4507 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____4507 with
            | (binders1,res) ->
                let uu____4518 =
                  (env.FStar_SMTEncoding_Env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____4518
                then
                  let uu____4525 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____4525 with
                   | (vars,guards,env',decls,uu____4550) ->
                       let fsym =
                         let uu____4569 =
                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                             "f"
                            in
                         (uu____4569, FStar_SMTEncoding_Term.Term_sort)  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____4575 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___366_4584 =
                              env.FStar_SMTEncoding_Env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___366_4584.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___366_4584.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___366_4584.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___366_4584.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___366_4584.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___366_4584.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___366_4584.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___366_4584.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___366_4584.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___366_4584.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___366_4584.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___366_4584.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___366_4584.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___366_4584.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___366_4584.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___366_4584.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___366_4584.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___366_4584.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___366_4584.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___366_4584.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___366_4584.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___366_4584.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___366_4584.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___366_4584.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___366_4584.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___366_4584.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___366_4584.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___366_4584.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___366_4584.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___366_4584.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___366_4584.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___366_4584.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___366_4584.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___366_4584.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___366_4584.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___366_4584.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___366_4584.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___366_4584.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___366_4584.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___366_4584.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___366_4584.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___366_4584.FStar_TypeChecker_Env.nbe)
                            }) res
                          in
                       (match uu____4575 with
                        | (pre_opt,res_t) ->
                            let uu____4596 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____4596 with
                             | (res_pred,decls') ->
                                 let uu____4607 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____4620 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____4620, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____4624 =
                                         encode_formula pre env'  in
                                       (match uu____4624 with
                                        | (guard,decls0) ->
                                            let uu____4637 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____4637, decls0))
                                    in
                                 (match uu____4607 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____4651 =
                                          let uu____4662 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____4662)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t.FStar_Syntax_Syntax.pos
                                          uu____4651
                                         in
                                      let cvars =
                                        let uu____4679 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____4679
                                          (FStar_List.filter
                                             (fun uu____4709  ->
                                                match uu____4709 with
                                                | (x,uu____4717) ->
                                                    x <>
                                                      (FStar_Pervasives_Native.fst
                                                         fsym)))
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
                                        let uu____4738 =
                                          FStar_Util.digest_of_string
                                            tkey_hash
                                           in
                                        Prims.strcat "Tm_arrow_" uu____4738
                                         in
                                      let cvar_sorts =
                                        FStar_List.map
                                          FStar_Pervasives_Native.snd cvars
                                         in
                                      let caption =
                                        let uu____4751 =
                                          FStar_Options.log_queries ()  in
                                        if uu____4751
                                        then
                                          let uu____4754 =
                                            let uu____4756 =
                                              FStar_TypeChecker_Normalize.term_to_string
                                                env.FStar_SMTEncoding_Env.tcenv
                                                t0
                                               in
                                            FStar_Util.replace_char
                                              uu____4756 10 32
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____4754
                                        else FStar_Pervasives_Native.None  in
                                      let tdecl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (tsym, cvar_sorts,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            caption)
                                         in
                                      let t1 =
                                        let uu____4769 =
                                          let uu____4777 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              cvars
                                             in
                                          (tsym, uu____4777)  in
                                        FStar_SMTEncoding_Util.mkApp
                                          uu____4769
                                         in
                                      let t_has_kind =
                                        FStar_SMTEncoding_Term.mk_HasType t1
                                          FStar_SMTEncoding_Term.mk_Term_type
                                         in
                                      let k_assumption =
                                        let a_name =
                                          Prims.strcat "kinding_" tsym  in
                                        let uu____4793 =
                                          let uu____4801 =
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              ([[t_has_kind]], cvars,
                                                t_has_kind)
                                             in
                                          (uu____4801,
                                            (FStar_Pervasives_Native.Some
                                               a_name), a_name)
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____4793
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
                                        let uu____4818 =
                                          let uu____4826 =
                                            let uu____4827 =
                                              let uu____4838 =
                                                let uu____4839 =
                                                  let uu____4844 =
                                                    let uu____4845 =
                                                      FStar_SMTEncoding_Term.mk_PreType
                                                        f
                                                       in
                                                    FStar_SMTEncoding_Term.mk_tester
                                                      "Tm_arrow" uu____4845
                                                     in
                                                  (f_has_t, uu____4844)  in
                                                FStar_SMTEncoding_Util.mkImp
                                                  uu____4839
                                                 in
                                              ([[f_has_t]], (fsym :: cvars),
                                                uu____4838)
                                               in
                                            let uu____4860 =
                                              mkForall_fuel
                                                t0.FStar_Syntax_Syntax.pos
                                               in
                                            uu____4860 uu____4827  in
                                          (uu____4826,
                                            (FStar_Pervasives_Native.Some
                                               "pre-typing for functions"),
                                            (Prims.strcat module_name
                                               (Prims.strcat "_" a_name)))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____4818
                                         in
                                      let t_interp1 =
                                        let a_name =
                                          Prims.strcat "interpretation_" tsym
                                           in
                                        let uu____4883 =
                                          let uu____4891 =
                                            let uu____4892 =
                                              let uu____4903 =
                                                FStar_SMTEncoding_Util.mkIff
                                                  (f_has_t_z, t_interp)
                                                 in
                                              ([[f_has_t_z]], (fsym ::
                                                cvars), uu____4903)
                                               in
                                            FStar_SMTEncoding_Term.mkForall
                                              t0.FStar_Syntax_Syntax.pos
                                              uu____4892
                                             in
                                          (uu____4891,
                                            (FStar_Pervasives_Native.Some
                                               a_name),
                                            (Prims.strcat module_name
                                               (Prims.strcat "_" a_name)))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____4883
                                         in
                                      let t_decls1 =
                                        [tdecl;
                                        k_assumption;
                                        pre_typing;
                                        t_interp1]  in
                                      let uu____4923 =
                                        let uu____4924 =
                                          let uu____4927 =
                                            let uu____4930 =
                                              FStar_SMTEncoding_Term.mk_decls
                                                tsym tkey_hash t_decls1
                                                (FStar_List.append decls
                                                   (FStar_List.append decls'
                                                      guard_decls))
                                               in
                                            FStar_List.append guard_decls
                                              uu____4930
                                             in
                                          FStar_List.append decls' uu____4927
                                           in
                                        FStar_List.append decls uu____4924
                                         in
                                      (t1, uu____4923)))))
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
                     let uu____4951 =
                       let uu____4959 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____4959,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____4951  in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)  in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym  in
                     let uu____4978 =
                       let uu____4986 =
                         let uu____4987 =
                           let uu____4998 =
                             let uu____4999 =
                               let uu____5004 =
                                 let uu____5005 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____5005
                                  in
                               (f_has_t, uu____5004)  in
                             FStar_SMTEncoding_Util.mkImp uu____4999  in
                           ([[f_has_t]], [fsym], uu____4998)  in
                         let uu____5025 =
                           mkForall_fuel t0.FStar_Syntax_Syntax.pos  in
                         uu____5025 uu____4987  in
                       (uu____4986, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____4978  in
                   let uu____5043 =
                     FStar_All.pipe_right [tdecl; t_kinding; t_interp]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                      in
                   (t1, uu____5043)))
       | FStar_Syntax_Syntax.Tm_refine uu____5046 ->
           let uu____5053 =
             let uu____5058 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Env.Weak;
                 FStar_TypeChecker_Env.HNF;
                 FStar_TypeChecker_Env.EraseUniverses]
                 env.FStar_SMTEncoding_Env.tcenv t0
                in
             match uu____5058 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____5065;
                 FStar_Syntax_Syntax.vars = uu____5066;_} ->
                 let uu____5073 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____5073 with
                  | (b,f1) ->
                      let uu____5098 =
                        let uu____5099 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____5099  in
                      (uu____5098, f1))
             | uu____5114 -> failwith "impossible"  in
           (match uu____5053 with
            | (x,f) ->
                let uu____5126 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____5126 with
                 | (base_t,decls) ->
                     let uu____5137 =
                       FStar_SMTEncoding_Env.gen_term_var env x  in
                     (match uu____5137 with
                      | (x1,xtm,env') ->
                          let uu____5154 = encode_formula f env'  in
                          (match uu____5154 with
                           | (refinement,decls') ->
                               let uu____5165 =
                                 FStar_SMTEncoding_Env.fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____5165 with
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
                                      let uu____5190 =
                                        let uu____5198 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____5206 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____5198
                                          uu____5206
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____5190
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____5254  ->
                                              match uu____5254 with
                                              | (y,uu____5262) ->
                                                  (y <> x1) && (y <> fsym)))
                                       in
                                    let xfv =
                                      (x1, FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    let ffv =
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
                                      let uu____5304 =
                                        FStar_Util.digest_of_string tkey_hash
                                         in
                                      Prims.strcat "Tm_refine_" uu____5304
                                       in
                                    let cvar_sorts =
                                      FStar_List.map
                                        FStar_Pervasives_Native.snd cvars1
                                       in
                                    let tdecl =
                                      FStar_SMTEncoding_Term.DeclFun
                                        (tsym, cvar_sorts,
                                          FStar_SMTEncoding_Term.Term_sort,
                                          FStar_Pervasives_Native.None)
                                       in
                                    let t1 =
                                      let uu____5322 =
                                        let uu____5330 =
                                          FStar_List.map
                                            FStar_SMTEncoding_Util.mkFreeV
                                            cvars1
                                           in
                                        (tsym, uu____5330)  in
                                      FStar_SMTEncoding_Util.mkApp uu____5322
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
                                      let uu____5347 =
                                        let uu____5355 =
                                          let uu____5356 =
                                            let uu____5367 =
                                              FStar_SMTEncoding_Util.mkIff
                                                (t_haseq_ref, t_haseq_base)
                                               in
                                            ([[t_haseq_ref]], cvars1,
                                              uu____5367)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            t0.FStar_Syntax_Syntax.pos
                                            uu____5356
                                           in
                                        (uu____5355,
                                          (FStar_Pervasives_Native.Some
                                             (Prims.strcat "haseq for " tsym)),
                                          (Prims.strcat "haseq" tsym))
                                         in
                                      FStar_SMTEncoding_Util.mkAssume
                                        uu____5347
                                       in
                                    let t_kinding =
                                      let uu____5381 =
                                        let uu____5389 =
                                          FStar_SMTEncoding_Term.mkForall
                                            t0.FStar_Syntax_Syntax.pos
                                            ([[t_has_kind]], cvars1,
                                              t_has_kind)
                                           in
                                        (uu____5389,
                                          (FStar_Pervasives_Native.Some
                                             "refinement kinding"),
                                          (Prims.strcat "refinement_kinding_"
                                             tsym))
                                         in
                                      FStar_SMTEncoding_Util.mkAssume
                                        uu____5381
                                       in
                                    let t_interp =
                                      let uu____5403 =
                                        let uu____5411 =
                                          let uu____5412 =
                                            let uu____5423 =
                                              FStar_SMTEncoding_Util.mkIff
                                                (x_has_t, encoding)
                                               in
                                            ([[x_has_t]], (ffv :: xfv ::
                                              cvars1), uu____5423)
                                             in
                                          FStar_SMTEncoding_Term.mkForall
                                            t0.FStar_Syntax_Syntax.pos
                                            uu____5412
                                           in
                                        (uu____5411,
                                          (FStar_Pervasives_Native.Some
                                             "refinement_interpretation"),
                                          (Prims.strcat
                                             "refinement_interpretation_"
                                             tsym))
                                         in
                                      FStar_SMTEncoding_Util.mkAssume
                                        uu____5403
                                       in
                                    let t_decls1 =
                                      [tdecl; t_kinding; t_interp; t_haseq1]
                                       in
                                    let uu____5449 =
                                      let uu____5450 =
                                        let uu____5453 =
                                          FStar_SMTEncoding_Term.mk_decls
                                            tsym tkey_hash t_decls1
                                            (FStar_List.append decls decls')
                                           in
                                        FStar_List.append decls' uu____5453
                                         in
                                      FStar_List.append decls uu____5450  in
                                    (t1, uu____5449))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,uu____5457) ->
           let ttm =
             let uu____5475 =
               FStar_Syntax_Unionfind.uvar_id
                 uv.FStar_Syntax_Syntax.ctx_uvar_head
                in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____5475  in
           let uu____5477 =
             encode_term_pred FStar_Pervasives_Native.None
               uv.FStar_Syntax_Syntax.ctx_uvar_typ env ttm
              in
           (match uu____5477 with
            | (t_has_k,decls) ->
                let d =
                  let uu____5489 =
                    let uu____5497 =
                      let uu____5499 =
                        let uu____5501 =
                          let uu____5503 =
                            FStar_Syntax_Unionfind.uvar_id
                              uv.FStar_Syntax_Syntax.ctx_uvar_head
                             in
                          FStar_Util.string_of_int uu____5503  in
                        FStar_Util.format1 "uvar_typing_%s" uu____5501  in
                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                        uu____5499
                       in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____5497)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____5489  in
                let uu____5509 =
                  let uu____5510 =
                    FStar_All.pipe_right [d]
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append decls uu____5510  in
                (ttm, uu____5509))
       | FStar_Syntax_Syntax.Tm_app uu____5517 ->
           let uu____5534 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____5534 with
            | (head1,args_e) ->
                let uu____5581 =
                  let uu____5596 =
                    let uu____5597 = FStar_Syntax_Subst.compress head1  in
                    uu____5597.FStar_Syntax_Syntax.n  in
                  (uu____5596, args_e)  in
                (match uu____5581 with
                 | uu____5614 when head_redex env head1 ->
                     let uu____5629 = whnf env t  in
                     encode_term uu____5629 env
                 | uu____5630 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____5653 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5671) when
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
                       FStar_Syntax_Syntax.pos = uu____5693;
                       FStar_Syntax_Syntax.vars = uu____5694;_},uu____5695),uu____5696)
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
                       FStar_Syntax_Syntax.pos = uu____5722;
                       FStar_Syntax_Syntax.vars = uu____5723;_},uu____5724),
                    (v0,uu____5726)::(v1,uu____5728)::(v2,uu____5730)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____5801 = encode_term v0 env  in
                     (match uu____5801 with
                      | (v01,decls0) ->
                          let uu____5812 = encode_term v1 env  in
                          (match uu____5812 with
                           | (v11,decls1) ->
                               let uu____5823 = encode_term v2 env  in
                               (match uu____5823 with
                                | (v21,decls2) ->
                                    let uu____5834 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____5834,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(v0,uu____5837)::(v1,uu____5839)::(v2,uu____5841)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____5908 = encode_term v0 env  in
                     (match uu____5908 with
                      | (v01,decls0) ->
                          let uu____5919 = encode_term v1 env  in
                          (match uu____5919 with
                           | (v11,decls1) ->
                               let uu____5930 = encode_term v2 env  in
                               (match uu____5930 with
                                | (v21,decls2) ->
                                    let uu____5941 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____5941,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____5943)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____5979)::(rng,uu____5981)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____6032) ->
                     let e0 =
                       let uu____6054 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg
                         env.FStar_SMTEncoding_Env.tcenv head1 uu____6054
                        in
                     ((let uu____6064 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug
                              env.FStar_SMTEncoding_Env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____6064
                       then
                         let uu____6069 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____6069
                       else ());
                      (let e =
                         let uu____6077 =
                           let uu____6082 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____6083 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____6082
                             uu____6083
                            in
                         uu____6077 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____6094),(arg,uu____6096)::[]) -> encode_term arg env
                 | uu____6131 ->
                     let uu____6146 = encode_args args_e env  in
                     (match uu____6146 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____6207 = encode_term head1 env  in
                            match uu____6207 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____6279 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____6279 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____6377  ->
                                                 fun uu____6378  ->
                                                   match (uu____6377,
                                                           uu____6378)
                                                   with
                                                   | ((bv,uu____6408),
                                                      (a,uu____6410)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____6440 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____6440
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____6441 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm
                                             in
                                          (match uu____6441 with
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
                                                 let uu____6458 =
                                                   let uu____6466 =
                                                     FStar_SMTEncoding_Term.mkForall
                                                       t0.FStar_Syntax_Syntax.pos
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____6475 =
                                                     let uu____6477 =
                                                       let uu____6479 =
                                                         FStar_SMTEncoding_Term.hash_of_term
                                                           app_tm
                                                          in
                                                       FStar_Util.digest_of_string
                                                         uu____6479
                                                        in
                                                     Prims.strcat
                                                       "partial_app_typing_"
                                                       uu____6477
                                                      in
                                                   (uu____6466,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____6475)
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____6458
                                                  in
                                               let uu____6485 =
                                                 let uu____6488 =
                                                   let uu____6491 =
                                                     let uu____6494 =
                                                       FStar_SMTEncoding_Term.mk_decls
                                                         "" tkey_hash
                                                         [e_typing]
                                                         (FStar_List.append
                                                            decls
                                                            (FStar_List.append
                                                               decls' decls''))
                                                        in
                                                     FStar_List.append
                                                       decls'' uu____6494
                                                      in
                                                   FStar_List.append decls'
                                                     uu____6491
                                                    in
                                                 FStar_List.append decls
                                                   uu____6488
                                                  in
                                               (app_tm, uu____6485))))
                             in
                          let encode_full_app fv =
                            let uu____6514 =
                              FStar_SMTEncoding_Env.lookup_free_var_sym env
                                fv
                               in
                            match uu____6514 with
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
                                   FStar_Syntax_Syntax.pos = uu____6545;
                                   FStar_Syntax_Syntax.vars = uu____6546;_},uu____6547)
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
                                   FStar_Syntax_Syntax.pos = uu____6554;
                                   FStar_Syntax_Syntax.vars = uu____6555;_},uu____6556)
                                ->
                                let uu____6561 =
                                  let uu____6562 =
                                    let uu____6567 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____6567
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____6562
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____6561
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____6597 =
                                  let uu____6598 =
                                    let uu____6603 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____6603
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____6598
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____6597
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____6632,(FStar_Util.Inl t1,uu____6634),uu____6635)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____6682,(FStar_Util.Inr c,uu____6684),uu____6685)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____6732 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____6753 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Env.Weak;
                                     FStar_TypeChecker_Env.HNF;
                                     FStar_TypeChecker_Env.EraseUniverses]
                                     env.FStar_SMTEncoding_Env.tcenv
                                     head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____6753
                                  in
                               let uu____6754 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____6754 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____6770;
                                            FStar_Syntax_Syntax.vars =
                                              uu____6771;_},uu____6772)
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
                                     | uu____6790 ->
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
           let uu____6869 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____6869 with
            | (bs1,body1,opening) ->
                let fallback uu____6892 =
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
                  let uu____6902 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort)
                     in
                  let uu____6904 =
                    FStar_All.pipe_right [decl]
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  (uu____6902, uu____6904)  in
                let is_impure rc =
                  let uu____6914 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                      env.FStar_SMTEncoding_Env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____6914 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____6929 =
                          let uu____6942 =
                            FStar_TypeChecker_Env.get_range
                              env.FStar_SMTEncoding_Env.tcenv
                             in
                          FStar_TypeChecker_Util.new_implicit_var
                            "SMTEncoding codomain" uu____6942
                            env.FStar_SMTEncoding_Env.tcenv
                            FStar_Syntax_Util.ktype0
                           in
                        (match uu____6929 with
                         | (t1,uu____6945,uu____6946) -> t1)
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  let uu____6964 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                     in
                  if uu____6964
                  then
                    let uu____6969 = FStar_Syntax_Syntax.mk_Total res_typ  in
                    FStar_Pervasives_Native.Some uu____6969
                  else
                    (let uu____6972 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid
                        in
                     if uu____6972
                     then
                       let uu____6977 = FStar_Syntax_Syntax.mk_GTotal res_typ
                          in
                       FStar_Pervasives_Native.Some uu____6977
                     else FStar_Pervasives_Native.None)
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____6985 =
                         let uu____6991 =
                           let uu____6993 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____6993
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____6991)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____6985);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____6998 =
                       (is_impure rc) &&
                         (let uu____7001 =
                            FStar_TypeChecker_Env.is_reifiable_rc
                              env.FStar_SMTEncoding_Env.tcenv rc
                             in
                          Prims.op_Negation uu____7001)
                        in
                     if uu____6998
                     then fallback ()
                     else
                       (let uu____7010 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____7010 with
                        | (vars,guards,envbody,decls,uu____7035) ->
                            let body2 =
                              let uu____7049 =
                                FStar_TypeChecker_Env.is_reifiable_rc
                                  env.FStar_SMTEncoding_Env.tcenv rc
                                 in
                              if uu____7049
                              then
                                FStar_TypeChecker_Util.reify_body
                                  env.FStar_SMTEncoding_Env.tcenv body1
                              else body1  in
                            let uu____7054 = encode_term body2 envbody  in
                            (match uu____7054 with
                             | (body3,decls') ->
                                 let uu____7065 =
                                   let uu____7074 = codomain_eff rc  in
                                   match uu____7074 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____7093 = encode_term tfun env
                                          in
                                       (match uu____7093 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____7065 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____7127 =
                                          let uu____7138 =
                                            let uu____7139 =
                                              let uu____7144 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____7144, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____7139
                                             in
                                          ([], vars, uu____7138)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t0.FStar_Syntax_Syntax.pos
                                          uu____7127
                                         in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body
                                         in
                                      let uu____7152 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            (cvars, key_body)
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____7168 =
                                              let uu____7171 =
                                                let uu____7179 =
                                                  FStar_SMTEncoding_Term.free_variables
                                                    t1
                                                   in
                                                FStar_List.append uu____7179
                                                  cvars
                                                 in
                                              FStar_Util.remove_dups
                                                FStar_SMTEncoding_Term.fv_eq
                                                uu____7171
                                               in
                                            let uu____7197 =
                                              FStar_SMTEncoding_Util.mkAnd
                                                (key_body, t1)
                                               in
                                            (uu____7168, uu____7197)
                                         in
                                      (match uu____7152 with
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
                                           let uu____7219 =
                                             is_an_eta_expansion env vars
                                               body3
                                              in
                                           (match uu____7219 with
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
                                                    FStar_Pervasives_Native.snd
                                                    cvars1
                                                   in
                                                let fsym =
                                                  let uu____7236 =
                                                    FStar_Util.digest_of_string
                                                      tkey_hash
                                                     in
                                                  Prims.strcat "Tm_abs_"
                                                    uu____7236
                                                   in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None)
                                                   in
                                                let f =
                                                  let uu____7245 =
                                                    let uu____7253 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    (fsym, uu____7253)  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____7245
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
                                                      let uu____7270 =
                                                        let uu____7271 =
                                                          let uu____7279 =
                                                            FStar_SMTEncoding_Term.mkForall
                                                              t0.FStar_Syntax_Syntax.pos
                                                              ([[f]], cvars1,
                                                                f_has_t)
                                                             in
                                                          (uu____7279,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name)
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____7271
                                                         in
                                                      [uu____7270]
                                                   in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym
                                                     in
                                                  let uu____7294 =
                                                    let uu____7302 =
                                                      let uu____7303 =
                                                        let uu____7314 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3)
                                                           in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____7314)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        t0.FStar_Syntax_Syntax.pos
                                                        uu____7303
                                                       in
                                                    (uu____7302,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____7294
                                                   in
                                                let f_decls =
                                                  FStar_List.append (fdecl ::
                                                    typing_f) [interp_f]
                                                   in
                                                let uu____7328 =
                                                  let uu____7329 =
                                                    let uu____7332 =
                                                      let uu____7335 =
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
                                                        decls'' uu____7335
                                                       in
                                                    FStar_List.append decls'
                                                      uu____7332
                                                     in
                                                  FStar_List.append decls
                                                    uu____7329
                                                   in
                                                (f, uu____7328))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____7338,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____7339;
                          FStar_Syntax_Syntax.lbunivs = uu____7340;
                          FStar_Syntax_Syntax.lbtyp = uu____7341;
                          FStar_Syntax_Syntax.lbeff = uu____7342;
                          FStar_Syntax_Syntax.lbdef = uu____7343;
                          FStar_Syntax_Syntax.lbattrs = uu____7344;
                          FStar_Syntax_Syntax.lbpos = uu____7345;_}::uu____7346),uu____7347)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____7381;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____7383;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____7385;
                FStar_Syntax_Syntax.lbpos = uu____7386;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____7413 ->
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
              let uu____7485 =
                let uu____7490 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____7490 env  in
              match uu____7485 with
              | (ee1,decls1) ->
                  let uu____7515 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____7515 with
                   | (xs,e21) ->
                       let uu____7540 = FStar_List.hd xs  in
                       (match uu____7540 with
                        | (x1,uu____7558) ->
                            let env' =
                              FStar_SMTEncoding_Env.push_term_var env x1 ee1
                               in
                            let uu____7564 = encode_body e21 env'  in
                            (match uu____7564 with
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
            let uu____7594 =
              let uu____7602 =
                let uu____7603 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____7603  in
              FStar_SMTEncoding_Env.gen_term_var env uu____7602  in
            match uu____7594 with
            | (scrsym,scr',env1) ->
                let uu____7613 = encode_term e env1  in
                (match uu____7613 with
                 | (scr,decls) ->
                     let uu____7624 =
                       let encode_branch b uu____7653 =
                         match uu____7653 with
                         | (else_case,decls1) ->
                             let uu____7672 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____7672 with
                              | (p,w,br) ->
                                  let uu____7698 = encode_pat env1 p  in
                                  (match uu____7698 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____7735  ->
                                                   match uu____7735 with
                                                   | (x,t) ->
                                                       FStar_SMTEncoding_Env.push_term_var
                                                         env2 x t) env1)
                                          in
                                       let uu____7742 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____7764 =
                                               encode_term w1 env2  in
                                             (match uu____7764 with
                                              | (w2,decls2) ->
                                                  let uu____7777 =
                                                    let uu____7778 =
                                                      let uu____7783 =
                                                        let uu____7784 =
                                                          let uu____7789 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____7789)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____7784
                                                         in
                                                      (guard, uu____7783)  in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____7778
                                                     in
                                                  (uu____7777, decls2))
                                          in
                                       (match uu____7742 with
                                        | (guard1,decls2) ->
                                            let uu____7804 =
                                              encode_br br env2  in
                                            (match uu____7804 with
                                             | (br1,decls3) ->
                                                 let uu____7817 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____7817,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____7624 with
                      | (match_tm,decls1) ->
                          let uu____7838 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange
                             in
                          (uu____7838, decls1)))

and (encode_pat :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.pat -> (FStar_SMTEncoding_Env.env_t * pattern))
  =
  fun env  ->
    fun pat  ->
      (let uu____7861 =
         FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
           FStar_Options.Medium
          in
       if uu____7861
       then
         let uu____7864 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____7864
       else ());
      (let uu____7869 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____7869 with
       | (vars,pat_term) ->
           let uu____7886 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____7942  ->
                     fun v1  ->
                       match uu____7942 with
                       | (env1,vars1) ->
                           let uu____7998 =
                             FStar_SMTEncoding_Env.gen_term_var env1 v1  in
                           (match uu____7998 with
                            | (xx,uu____8022,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, []))
              in
           (match uu____7886 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____8115 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____8116 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____8117 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____8125 = encode_const c env1  in
                      (match uu____8125 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____8133::uu____8134 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____8138 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon
                            env1.FStar_SMTEncoding_Env.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____8161 =
                          FStar_TypeChecker_Env.datacons_of_typ
                            env1.FStar_SMTEncoding_Env.tcenv tc_name
                           in
                        match uu____8161 with
                        | (uu____8169,uu____8170::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____8175 ->
                            FStar_SMTEncoding_Env.mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____8211  ->
                                  match uu____8211 with
                                  | (arg,uu____8221) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____8230 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____8230))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____8262) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____8293 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____8318 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____8364  ->
                                  match uu____8364 with
                                  | (arg,uu____8380) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____8389 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____8389))
                         in
                      FStar_All.pipe_right uu____8318 FStar_List.flatten
                   in
                let pat_term1 uu____8420 = encode_term pat_term env1  in
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
      let uu____8430 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____8478  ->
                fun uu____8479  ->
                  match (uu____8478, uu____8479) with
                  | ((tms,decls),(t,uu____8519)) ->
                      let uu____8546 = encode_term t env  in
                      (match uu____8546 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____8430 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____8603 = FStar_Syntax_Util.list_elements e  in
        match uu____8603 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____8634 =
          let uu____8651 = FStar_Syntax_Util.unmeta p  in
          FStar_All.pipe_right uu____8651 FStar_Syntax_Util.head_and_args  in
        match uu____8634 with
        | (head1,args) ->
            let uu____8702 =
              let uu____8717 =
                let uu____8718 = FStar_Syntax_Util.un_uinst head1  in
                uu____8718.FStar_Syntax_Syntax.n  in
              (uu____8717, args)  in
            (match uu____8702 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____8740,uu____8741)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____8793 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or1 t1 =
          let uu____8848 =
            let uu____8865 = FStar_Syntax_Util.unmeta t1  in
            FStar_All.pipe_right uu____8865 FStar_Syntax_Util.head_and_args
             in
          match uu____8848 with
          | (head1,args) ->
              let uu____8912 =
                let uu____8927 =
                  let uu____8928 = FStar_Syntax_Util.un_uinst head1  in
                  uu____8928.FStar_Syntax_Syntax.n  in
                (uu____8927, args)  in
              (match uu____8912 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____8947)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____8984 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____9014 = smt_pat_or1 t1  in
            (match uu____9014 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____9036 = list_elements1 e  in
                 FStar_All.pipe_right uu____9036
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____9066 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____9066
                           (FStar_List.map one_pat)))
             | uu____9089 ->
                 let uu____9094 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____9094])
        | uu____9145 ->
            let uu____9148 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____9148]
         in
      let uu____9199 =
        let uu____9214 =
          let uu____9215 = FStar_Syntax_Subst.compress t  in
          uu____9215.FStar_Syntax_Syntax.n  in
        match uu____9214 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____9254 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____9254 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____9289;
                        FStar_Syntax_Syntax.effect_name = uu____9290;
                        FStar_Syntax_Syntax.result_typ = uu____9291;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____9293)::(post,uu____9295)::(pats,uu____9297)::[];
                        FStar_Syntax_Syntax.flags = uu____9298;_}
                      ->
                      let uu____9359 = lemma_pats pats  in
                      (binders1, pre, post, uu____9359)
                  | uu____9370 -> failwith "impos"))
        | uu____9386 -> failwith "Impos"  in
      match uu____9199 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___367_9423 = env  in
            {
              FStar_SMTEncoding_Env.bvar_bindings =
                (uu___367_9423.FStar_SMTEncoding_Env.bvar_bindings);
              FStar_SMTEncoding_Env.fvar_bindings =
                (uu___367_9423.FStar_SMTEncoding_Env.fvar_bindings);
              FStar_SMTEncoding_Env.depth =
                (uu___367_9423.FStar_SMTEncoding_Env.depth);
              FStar_SMTEncoding_Env.tcenv =
                (uu___367_9423.FStar_SMTEncoding_Env.tcenv);
              FStar_SMTEncoding_Env.warn =
                (uu___367_9423.FStar_SMTEncoding_Env.warn);
              FStar_SMTEncoding_Env.nolabels =
                (uu___367_9423.FStar_SMTEncoding_Env.nolabels);
              FStar_SMTEncoding_Env.use_zfuel_name = true;
              FStar_SMTEncoding_Env.encode_non_total_function_typ =
                (uu___367_9423.FStar_SMTEncoding_Env.encode_non_total_function_typ);
              FStar_SMTEncoding_Env.current_module_name =
                (uu___367_9423.FStar_SMTEncoding_Env.current_module_name);
              FStar_SMTEncoding_Env.encoding_quantifier =
                (uu___367_9423.FStar_SMTEncoding_Env.encoding_quantifier);
              FStar_SMTEncoding_Env.global_cache =
                (uu___367_9423.FStar_SMTEncoding_Env.global_cache)
            }  in
          let uu____9425 =
            encode_binders FStar_Pervasives_Native.None binders env1  in
          (match uu____9425 with
           | (vars,guards,env2,decls,uu____9450) ->
               let uu____9463 = encode_smt_patterns patterns env2  in
               (match uu____9463 with
                | (pats,decls') ->
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
                    let env3 =
                      let uu___368_9490 = env2  in
                      {
                        FStar_SMTEncoding_Env.bvar_bindings =
                          (uu___368_9490.FStar_SMTEncoding_Env.bvar_bindings);
                        FStar_SMTEncoding_Env.fvar_bindings =
                          (uu___368_9490.FStar_SMTEncoding_Env.fvar_bindings);
                        FStar_SMTEncoding_Env.depth =
                          (uu___368_9490.FStar_SMTEncoding_Env.depth);
                        FStar_SMTEncoding_Env.tcenv =
                          (uu___368_9490.FStar_SMTEncoding_Env.tcenv);
                        FStar_SMTEncoding_Env.warn =
                          (uu___368_9490.FStar_SMTEncoding_Env.warn);
                        FStar_SMTEncoding_Env.nolabels = true;
                        FStar_SMTEncoding_Env.use_zfuel_name =
                          (uu___368_9490.FStar_SMTEncoding_Env.use_zfuel_name);
                        FStar_SMTEncoding_Env.encode_non_total_function_typ =
                          (uu___368_9490.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                        FStar_SMTEncoding_Env.current_module_name =
                          (uu___368_9490.FStar_SMTEncoding_Env.current_module_name);
                        FStar_SMTEncoding_Env.encoding_quantifier =
                          (uu___368_9490.FStar_SMTEncoding_Env.encoding_quantifier);
                        FStar_SMTEncoding_Env.global_cache =
                          (uu___368_9490.FStar_SMTEncoding_Env.global_cache)
                      }  in
                    let uu____9492 =
                      let uu____9497 = FStar_Syntax_Util.unmeta pre  in
                      encode_formula uu____9497 env3  in
                    (match uu____9492 with
                     | (pre1,decls'') ->
                         let uu____9504 =
                           let uu____9509 = FStar_Syntax_Util.unmeta post1
                              in
                           encode_formula uu____9509 env3  in
                         (match uu____9504 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append decls'
                                     (FStar_List.append decls'' decls'''))
                                 in
                              let uu____9519 =
                                let uu____9520 =
                                  let uu____9531 =
                                    let uu____9532 =
                                      let uu____9537 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards)
                                         in
                                      (uu____9537, post2)  in
                                    FStar_SMTEncoding_Util.mkImp uu____9532
                                     in
                                  (pats, vars, uu____9531)  in
                                FStar_SMTEncoding_Term.mkForall
                                  t.FStar_Syntax_Syntax.pos uu____9520
                                 in
                              (uu____9519, decls1)))))

and (encode_smt_patterns :
  FStar_Syntax_Syntax.arg Prims.list Prims.list ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term Prims.list Prims.list *
        FStar_SMTEncoding_Term.decls_t))
  =
  fun pats_l  ->
    fun env  ->
      let env1 =
        let uu___369_9557 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___369_9557.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___369_9557.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___369_9557.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___369_9557.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___369_9557.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___369_9557.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___369_9557.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___369_9557.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___369_9557.FStar_SMTEncoding_Env.encoding_quantifier);
          FStar_SMTEncoding_Env.global_cache =
            (uu___369_9557.FStar_SMTEncoding_Env.global_cache)
        }  in
      let encode_smt_pattern t =
        let uu____9573 = FStar_Syntax_Util.head_and_args t  in
        match uu____9573 with
        | (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____9636::(x,uu____9638)::(t1,uu____9640)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____9707 = encode_term x env1  in
                 (match uu____9707 with
                  | (x1,decls) ->
                      let uu____9718 = encode_term t1 env1  in
                      (match uu____9718 with
                       | (t2,decls') ->
                           let uu____9729 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                           (uu____9729, (FStar_List.append decls decls'))))
             | uu____9730 -> encode_term t env1)
         in
      FStar_List.fold_right
        (fun pats  ->
           fun uu____9773  ->
             match uu____9773 with
             | (pats_l1,decls) ->
                 let uu____9818 =
                   FStar_List.fold_right
                     (fun uu____9853  ->
                        fun uu____9854  ->
                          match (uu____9853, uu____9854) with
                          | ((p,uu____9896),(pats1,decls1)) ->
                              let uu____9931 = encode_smt_pattern p  in
                              (match uu____9931 with
                               | (t,d) ->
                                   let uu____9946 =
                                     FStar_SMTEncoding_Term.check_pattern_ok
                                       t
                                      in
                                   (match uu____9946 with
                                    | FStar_Pervasives_Native.None  ->
                                        ((t :: pats1),
                                          (FStar_List.append d decls1))
                                    | FStar_Pervasives_Native.Some
                                        illegal_subterm ->
                                        ((let uu____9963 =
                                            let uu____9969 =
                                              let uu____9971 =
                                                FStar_Syntax_Print.term_to_string
                                                  p
                                                 in
                                              let uu____9973 =
                                                FStar_SMTEncoding_Term.print_smt_term
                                                  illegal_subterm
                                                 in
                                              FStar_Util.format2
                                                "Pattern %s contains illegal sub-term (%s); dropping it"
                                                uu____9971 uu____9973
                                               in
                                            (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                                              uu____9969)
                                             in
                                          FStar_Errors.log_issue
                                            p.FStar_Syntax_Syntax.pos
                                            uu____9963);
                                         (pats1,
                                           (FStar_List.append d decls1))))))
                     pats ([], decls)
                    in
                 (match uu____9818 with
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
        let uu____10033 =
          FStar_All.pipe_left
            (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____10033
        then
          let uu____10038 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____10040 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10038 uu____10040
        else ()  in
      let enc f r l =
        let uu____10082 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10114 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____10114 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____10082 with
        | (decls,args) ->
            let uu____10145 =
              let uu___370_10146 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___370_10146.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___370_10146.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10145, decls)
         in
      let const_op f r uu____10181 =
        let uu____10194 = f r  in (uu____10194, [])  in
      let un_op f l =
        let uu____10217 = FStar_List.hd l  in
        FStar_All.pipe_left f uu____10217  in
      let bin_op f uu___361_10237 =
        match uu___361_10237 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10248 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____10289 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____10314  ->
                 match uu____10314 with
                 | (t,uu____10330) ->
                     let uu____10335 = encode_formula t env  in
                     (match uu____10335 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____10289 with
        | (decls,phis) ->
            let uu____10364 =
              let uu___371_10365 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___371_10365.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___371_10365.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10364, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____10428  ->
               match uu____10428 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____10449) -> false
                    | uu____10452 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____10471 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____10471
        else
          (let uu____10488 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____10488 r rf)
         in
      let eq3_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____10560 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::t1::v0::v1::[] ->
                     let uu____10592 =
                       let uu____10597 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____10598 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____10597, uu____10598)  in
                     FStar_SMTEncoding_Util.mkAnd uu____10592
                 | uu____10599 -> failwith "Impossible")
             in
          uu____10560 r args
        else
          (let uu____10605 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____10605)
         in
      let h_equals_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____10677 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::v0::t1::v1::[] ->
                     let uu____10709 =
                       let uu____10714 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____10715 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____10714, uu____10715)  in
                     FStar_SMTEncoding_Util.mkAnd uu____10709
                 | uu____10716 -> failwith "Impossible")
             in
          uu____10677 r args
        else
          (let uu____10722 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____10722)
         in
      let mk_imp1 r uu___362_10757 =
        match uu___362_10757 with
        | (lhs,uu____10763)::(rhs,uu____10765)::[] ->
            let uu____10806 = encode_formula rhs env  in
            (match uu____10806 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____10821) ->
                      (l1, decls1)
                  | uu____10826 ->
                      let uu____10827 = encode_formula lhs env  in
                      (match uu____10827 with
                       | (l2,decls2) ->
                           let uu____10838 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____10838, (FStar_List.append decls1 decls2)))))
        | uu____10839 -> failwith "impossible"  in
      let mk_ite r uu___363_10867 =
        match uu___363_10867 with
        | (guard,uu____10873)::(_then,uu____10875)::(_else,uu____10877)::[]
            ->
            let uu____10934 = encode_formula guard env  in
            (match uu____10934 with
             | (g,decls1) ->
                 let uu____10945 = encode_formula _then env  in
                 (match uu____10945 with
                  | (t,decls2) ->
                      let uu____10956 = encode_formula _else env  in
                      (match uu____10956 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____10968 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____10998 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l
           in
        f uu____10998  in
      let connectives =
        let uu____11028 =
          let uu____11053 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____11053)  in
        let uu____11096 =
          let uu____11123 =
            let uu____11148 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____11148)  in
          let uu____11191 =
            let uu____11218 =
              let uu____11245 =
                let uu____11270 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____11270)  in
              let uu____11313 =
                let uu____11340 =
                  let uu____11367 =
                    let uu____11392 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____11392)  in
                  [uu____11367;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.c_eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq3_op);
                  (FStar_Parser_Const.c_eq3_lid, h_equals_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11340  in
              uu____11245 :: uu____11313  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11218  in
          uu____11123 :: uu____11191  in
        uu____11028 :: uu____11096  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____11937 = encode_formula phi' env  in
            (match uu____11937 with
             | (phi2,decls) ->
                 let uu____11948 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____11948, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____11950 ->
            let uu____11957 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____11957 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____11996 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____11996 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____12008;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____12010;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____12012;
                 FStar_Syntax_Syntax.lbpos = uu____12013;_}::[]),e2)
            ->
            let uu____12040 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____12040 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____12093::(x,uu____12095)::(t,uu____12097)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12164 = encode_term x env  in
                 (match uu____12164 with
                  | (x1,decls) ->
                      let uu____12175 = encode_term t env  in
                      (match uu____12175 with
                       | (t1,decls') ->
                           let uu____12186 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____12186, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12189)::(msg,uu____12191)::(phi2,uu____12193)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12260 =
                   let uu____12265 =
                     let uu____12266 = FStar_Syntax_Subst.compress r  in
                     uu____12266.FStar_Syntax_Syntax.n  in
                   let uu____12269 =
                     let uu____12270 = FStar_Syntax_Subst.compress msg  in
                     uu____12270.FStar_Syntax_Syntax.n  in
                   (uu____12265, uu____12269)  in
                 (match uu____12260 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12279))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____12290 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____12297)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____12332 when head_redex env head2 ->
                 let uu____12347 = whnf env phi1  in
                 encode_formula uu____12347 env
             | uu____12348 ->
                 let uu____12363 = encode_term phi1 env  in
                 (match uu____12363 with
                  | (tt,decls) ->
                      let tt1 =
                        let uu____12375 =
                          let uu____12377 =
                            FStar_Range.use_range
                              tt.FStar_SMTEncoding_Term.rng
                             in
                          let uu____12378 =
                            FStar_Range.use_range
                              phi1.FStar_Syntax_Syntax.pos
                             in
                          FStar_Range.rng_included uu____12377 uu____12378
                           in
                        if uu____12375
                        then tt
                        else
                          (let uu___372_12382 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___372_12382.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___372_12382.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      let uu____12383 = FStar_SMTEncoding_Term.mk_Valid tt1
                         in
                      (uu____12383, decls)))
        | uu____12384 ->
            let uu____12385 = encode_term phi1 env  in
            (match uu____12385 with
             | (tt,decls) ->
                 let tt1 =
                   let uu____12397 =
                     let uu____12399 =
                       FStar_Range.use_range tt.FStar_SMTEncoding_Term.rng
                        in
                     let uu____12400 =
                       FStar_Range.use_range phi1.FStar_Syntax_Syntax.pos  in
                     FStar_Range.rng_included uu____12399 uu____12400  in
                   if uu____12397
                   then tt
                   else
                     (let uu___373_12404 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___373_12404.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___373_12404.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 let uu____12405 = FStar_SMTEncoding_Term.mk_Valid tt1  in
                 (uu____12405, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____12449 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____12449 with
        | (vars,guards,env2,decls,uu____12488) ->
            let uu____12501 = encode_smt_patterns ps env2  in
            (match uu____12501 with
             | (pats,decls') ->
                 let uu____12538 = encode_formula body env2  in
                 (match uu____12538 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12570;
                             FStar_SMTEncoding_Term.rng = uu____12571;_}::[])::[]
                            when
                            let uu____12588 =
                              FStar_Ident.text_of_lid
                                FStar_Parser_Const.guard_free
                               in
                            uu____12588 = gf -> []
                        | uu____12591 -> guards  in
                      let uu____12596 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____12596, body1,
                        (FStar_List.append decls
                           (FStar_List.append decls' decls'')))))
         in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi  in
       let uu____12607 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____12607 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12616 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____12722  ->
                     match uu____12722 with
                     | (l,uu____12747) -> FStar_Ident.lid_equals op l))
              in
           (match uu____12616 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____12816,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____12908 = encode_q_body env vars pats body  in
             match uu____12908 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____12953 =
                     let uu____12964 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____12964)  in
                   FStar_SMTEncoding_Term.mkForall
                     phi1.FStar_Syntax_Syntax.pos uu____12953
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____12995 = encode_q_body env vars pats body  in
             match uu____12995 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____13039 =
                   let uu____13040 =
                     let uu____13051 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____13051)  in
                   FStar_SMTEncoding_Term.mkExists
                     phi1.FStar_Syntax_Syntax.pos uu____13040
                    in
                 (uu____13039, decls))))
