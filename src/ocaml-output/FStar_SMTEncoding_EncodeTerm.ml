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
               (fun uu___360_367  ->
                  match uu___360_367 with
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
  fun uu___361_671  ->
    match uu___361_671 with
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
          let uu____1897 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue  in
          (uu____1897, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____1899 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse  in
          (uu____1899, [])
      | FStar_Const.Const_char c1 ->
          let uu____1902 =
            let uu____1903 =
              let uu____1911 =
                let uu____1914 =
                  let uu____1915 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1)
                     in
                  FStar_SMTEncoding_Term.boxInt uu____1915  in
                [uu____1914]  in
              ("FStar.Char.__char_of_int", uu____1911)  in
            FStar_SMTEncoding_Util.mkApp uu____1903  in
          (uu____1902, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____1933 =
            let uu____1934 = FStar_SMTEncoding_Util.mkInteger i  in
            FStar_SMTEncoding_Term.boxInt uu____1934  in
          (uu____1933, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.FStar_SMTEncoding_Env.tcenv).FStar_TypeChecker_Env.dsenv
              repr sw FStar_Range.dummyRange
             in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____1955) ->
          let uu____1958 =
            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.string_const s
             in
          (uu____1958, [])
      | FStar_Const.Const_range uu____1959 ->
          let uu____1960 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          (uu____1960, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | c1 ->
          let uu____1962 =
            let uu____1964 = FStar_Syntax_Print.const_to_string c1  in
            FStar_Util.format1 "Unhandled constant: %s" uu____1964  in
          failwith uu____1962

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
        (let uu____1993 =
           FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
             FStar_Options.Medium
            in
         if uu____1993
         then
           let uu____1996 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____1996
         else ());
        (let uu____2002 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2099  ->
                   fun b  ->
                     match uu____2099 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2184 =
                           let x = FStar_Pervasives_Native.fst b  in
                           let uu____2205 =
                             FStar_SMTEncoding_Env.gen_term_var env1 x  in
                           match uu____2205 with
                           | (xxsym,xx,env') ->
                               let uu____2235 =
                                 let uu____2240 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____2240 env1 xx
                                  in
                               (match uu____2235 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x))
                            in
                         (match uu____2184 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____2002 with
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
          let uu____2414 = encode_term t env  in
          match uu____2414 with
          | (t1,decls) ->
              let uu____2425 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____2425, decls)

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
          let uu____2436 = encode_term t env  in
          match uu____2436 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____2451 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____2451, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____2453 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____2453, decls))

and (encode_arith_term :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____2459 = encode_args args_e env  in
        match uu____2459 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____2478 -> failwith "Impossible"  in
            let unary arg_tms1 =
              let uu____2490 = FStar_List.hd arg_tms1  in
              FStar_SMTEncoding_Term.unboxInt uu____2490  in
            let binary arg_tms1 =
              let uu____2505 =
                let uu____2506 = FStar_List.hd arg_tms1  in
                FStar_SMTEncoding_Term.unboxInt uu____2506  in
              let uu____2507 =
                let uu____2508 =
                  let uu____2509 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____2509  in
                FStar_SMTEncoding_Term.unboxInt uu____2508  in
              (uu____2505, uu____2507)  in
            let mk_default uu____2517 =
              let uu____2518 =
                FStar_SMTEncoding_Env.lookup_free_var_sym env
                  head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____2518 with
              | (fname,fuel_args,arity) ->
                  let args = FStar_List.append fuel_args arg_tms  in
                  maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity
                    args
               in
            let mk_l op mk_args ts =
              let uu____2583 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____2583
              then
                let uu____2586 =
                  let uu____2587 = mk_args ts  in op uu____2587  in
                FStar_All.pipe_right uu____2586 FStar_SMTEncoding_Term.boxInt
              else mk_default ()  in
            let mk_nl nm op ts =
              let uu____2625 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____2625
              then
                let uu____2628 = binary ts  in
                match uu____2628 with
                | (t1,t2) ->
                    let uu____2635 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____2635
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____2641 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____2641
                 then
                   let uu____2644 =
                     let uu____2645 = binary ts  in op uu____2645  in
                   FStar_All.pipe_right uu____2644
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
            let uu____2810 =
              let uu____2820 =
                FStar_List.tryFind
                  (fun uu____2844  ->
                     match uu____2844 with
                     | (l,uu____2855) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____2820 FStar_Util.must  in
            (match uu____2810 with
             | (uu____2899,op) ->
                 let uu____2911 = op arg_tms  in (uu____2911, decls))

and (encode_BitVector_term :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.arg Prims.list ->
        (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_elt
          Prims.list))
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____2919 = FStar_List.hd args_e  in
        match uu____2919 with
        | (tm_sz,uu____2927) ->
            let uu____2936 = uu____2919  in
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let uu____2945 =
                FStar_Util.smap_try_find env.FStar_SMTEncoding_Env.cache
                  sz_key
                 in
              match uu____2945 with
              | FStar_Pervasives_Native.Some cache_entry ->
                  FStar_All.pipe_right
                    (FStar_SMTEncoding_Env.use_cache_entry cache_entry)
                    FStar_SMTEncoding_Term.mk_decls_trivial
              | FStar_Pervasives_Native.None  ->
                  let t_decls1 = FStar_SMTEncoding_Term.mkBvConstructor sz
                     in
                  ((let uu____2959 =
                      FStar_SMTEncoding_Env.mk_cache_entry env "" [] t_decls1
                       in
                    FStar_Util.smap_add env.FStar_SMTEncoding_Env.cache
                      sz_key uu____2959);
                   FStar_SMTEncoding_Term.mk_decls "" [] sz_key t_decls1 [])
               in
            let uu____2962 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____2988::(sz_arg,uu____2990)::uu____2991::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____3058 =
                    let uu____3059 = FStar_List.tail args_e  in
                    FStar_List.tail uu____3059  in
                  let uu____3062 =
                    let uu____3066 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____3066  in
                  (uu____3058, uu____3062)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____3073::(sz_arg,uu____3075)::uu____3076::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____3143 =
                    let uu____3145 = FStar_Syntax_Print.term_to_string sz_arg
                       in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____3145
                     in
                  failwith uu____3143
              | uu____3155 ->
                  let uu____3170 = FStar_List.tail args_e  in
                  (uu____3170, FStar_Pervasives_Native.None)
               in
            (match uu____2962 with
             | (arg_tms,ext_sz) ->
                 let uu____3189 = encode_args arg_tms env  in
                 (match uu____3189 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____3210 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____3222 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____3222  in
                      let unary_arith arg_tms2 =
                        let uu____3233 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____3233  in
                      let binary arg_tms2 =
                        let uu____3248 =
                          let uu____3249 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3249
                           in
                        let uu____3250 =
                          let uu____3251 =
                            let uu____3252 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____3252  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3251
                           in
                        (uu____3248, uu____3250)  in
                      let binary_arith arg_tms2 =
                        let uu____3269 =
                          let uu____3270 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3270
                           in
                        let uu____3271 =
                          let uu____3272 =
                            let uu____3273 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____3273  in
                          FStar_SMTEncoding_Term.unboxInt uu____3272  in
                        (uu____3269, uu____3271)  in
                      let mk_bv op mk_args resBox ts =
                        let uu____3331 =
                          let uu____3332 = mk_args ts  in op uu____3332  in
                        FStar_All.pipe_right uu____3331 resBox  in
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
                        let uu____3464 =
                          let uu____3469 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____3469  in
                        let uu____3478 =
                          let uu____3483 =
                            let uu____3485 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____3485  in
                          FStar_SMTEncoding_Term.boxBitVec uu____3483  in
                        mk_bv uu____3464 unary uu____3478 arg_tms2  in
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
                      let uu____3725 =
                        let uu____3735 =
                          FStar_List.tryFind
                            (fun uu____3759  ->
                               match uu____3759 with
                               | (l,uu____3770) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____3735 FStar_Util.must  in
                      (match uu____3725 with
                       | (uu____3816,op) ->
                           let uu____3828 = op arg_tms1  in
                           (uu____3828, (FStar_List.append sz_decls decls)))))

and (encode_deeply_embedded_quantifier :
  FStar_Syntax_Syntax.term ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let env1 =
        let uu___365_3838 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___365_3838.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___365_3838.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___365_3838.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___365_3838.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___365_3838.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.cache =
            (uu___365_3838.FStar_SMTEncoding_Env.cache);
          FStar_SMTEncoding_Env.nolabels =
            (uu___365_3838.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name =
            (uu___365_3838.FStar_SMTEncoding_Env.use_zfuel_name);
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___365_3838.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___365_3838.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier = true;
          FStar_SMTEncoding_Env.global_cache =
            (uu___365_3838.FStar_SMTEncoding_Env.global_cache)
        }  in
      let uu____3840 = encode_term t env1  in
      match uu____3840 with
      | (tm,decls) ->
          let vars = FStar_SMTEncoding_Term.free_variables tm  in
          let valid_tm = FStar_SMTEncoding_Term.mk_Valid tm  in
          let key =
            FStar_SMTEncoding_Term.mkForall t.FStar_Syntax_Syntax.pos
              ([], vars, valid_tm)
             in
          let tkey_hash = FStar_SMTEncoding_Term.hash_of_term key  in
          let uu____3862 =
            FStar_Util.smap_try_find env1.FStar_SMTEncoding_Env.cache
              tkey_hash
             in
          (match uu____3862 with
           | FStar_Pervasives_Native.Some cache_entry ->
               let uu____3870 =
                 let uu____3871 =
                   FStar_All.pipe_right
                     (FStar_SMTEncoding_Env.use_cache_entry cache_entry)
                     FStar_SMTEncoding_Term.mk_decls_trivial
                    in
                 FStar_List.append decls uu____3871  in
               (tm, uu____3870)
           | uu____3878 ->
               (match tm.FStar_SMTEncoding_Term.tm with
                | FStar_SMTEncoding_Term.App
                    (uu____3885,{
                                  FStar_SMTEncoding_Term.tm =
                                    FStar_SMTEncoding_Term.FreeV uu____3886;
                                  FStar_SMTEncoding_Term.freevars =
                                    uu____3887;
                                  FStar_SMTEncoding_Term.rng = uu____3888;_}::
                     {
                       FStar_SMTEncoding_Term.tm =
                         FStar_SMTEncoding_Term.FreeV uu____3889;
                       FStar_SMTEncoding_Term.freevars = uu____3890;
                       FStar_SMTEncoding_Term.rng = uu____3891;_}::[])
                    ->
                    (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                       (FStar_Errors.Warning_QuantifierWithoutPattern,
                         "Not encoding deeply embedded, unguarded quantifier to SMT");
                     (tm, decls))
                | uu____3925 ->
                    let uu____3926 = encode_formula t env1  in
                    (match uu____3926 with
                     | (phi,decls') ->
                         let interp =
                           match vars with
                           | [] ->
                               let uu____3943 =
                                 let uu____3948 =
                                   FStar_SMTEncoding_Term.mk_Valid tm  in
                                 (uu____3948, phi)  in
                               FStar_SMTEncoding_Util.mkIff uu____3943
                           | uu____3949 ->
                               let uu____3950 =
                                 let uu____3961 =
                                   let uu____3962 =
                                     let uu____3967 =
                                       FStar_SMTEncoding_Term.mk_Valid tm  in
                                     (uu____3967, phi)  in
                                   FStar_SMTEncoding_Util.mkIff uu____3962
                                    in
                                 ([[valid_tm]], vars, uu____3961)  in
                               FStar_SMTEncoding_Term.mkForall
                                 t.FStar_Syntax_Syntax.pos uu____3950
                            in
                         let ax =
                           let uu____3977 =
                             let uu____3985 =
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 "l_quant_interp"
                                in
                             (interp,
                               (FStar_Pervasives_Native.Some
                                  "Interpretation of deeply embedded quantifier"),
                               uu____3985)
                              in
                           FStar_SMTEncoding_Util.mkAssume uu____3977  in
                         let decls_l =
                           let uu____3994 =
                             FStar_All.pipe_right
                               (FStar_List.append decls decls')
                               FStar_SMTEncoding_Term.decls_list_of
                              in
                           FStar_List.append uu____3994 [ax]  in
                         ((let uu____4000 =
                             FStar_SMTEncoding_Env.mk_cache_entry env1 "" []
                               decls_l
                              in
                           FStar_Util.smap_add
                             env1.FStar_SMTEncoding_Env.cache tkey_hash
                             uu____4000);
                          (let uu____4002 =
                             let uu____4003 =
                               let uu____4006 =
                                 let uu____4009 =
                                   FStar_SMTEncoding_Term.decls_list_of
                                     decls'
                                    in
                                 FStar_List.append uu____4009 [ax]  in
                               FStar_SMTEncoding_Term.mk_decls "" []
                                 tkey_hash uu____4006 decls
                                in
                             FStar_List.append decls uu____4003  in
                           (tm, uu____4002))))))

and (encode_term :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____4021 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____4021
       then
         let uu____4026 = FStar_Syntax_Print.tag_of_term t  in
         let uu____4028 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____4030 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____4026 uu____4028
           uu____4030
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____4039 ->
           let uu____4062 =
             let uu____4064 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____4067 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____4069 = FStar_Syntax_Print.term_to_string t0  in
             let uu____4071 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____4064
               uu____4067 uu____4069 uu____4071
              in
           failwith uu____4062
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____4078 =
             let uu____4080 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____4083 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____4085 = FStar_Syntax_Print.term_to_string t0  in
             let uu____4087 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____4080
               uu____4083 uu____4085 uu____4087
              in
           failwith uu____4078
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let e = FStar_Syntax_Util.unfold_lazy i  in
           ((let uu____4097 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____4097
             then
               let uu____4102 = FStar_Syntax_Print.term_to_string t0  in
               let uu____4104 = FStar_Syntax_Print.term_to_string e  in
               FStar_Util.print2 ">> Unfolded (%s) ~> (%s)\n" uu____4102
                 uu____4104
             else ());
            encode_term e env)
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____4110 =
             let uu____4112 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____4112
              in
           failwith uu____4110
       | FStar_Syntax_Syntax.Tm_ascribed (t1,(k,uu____4121),uu____4122) ->
           let uu____4171 =
             match k with
             | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
             | uu____4181 -> false  in
           if uu____4171
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t1 env
       | FStar_Syntax_Syntax.Tm_quoted (qt,uu____4199) ->
           let tv =
             let uu____4205 =
               let uu____4212 = FStar_Reflection_Basic.inspect_ln qt  in
               FStar_Syntax_Embeddings.embed
                 FStar_Reflection_Embeddings.e_term_view uu____4212
                in
             uu____4205 t.FStar_Syntax_Syntax.pos
               FStar_Pervasives_Native.None
               FStar_Syntax_Embeddings.id_norm_cb
              in
           ((let uu____4239 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____4239
             then
               let uu____4244 = FStar_Syntax_Print.term_to_string t0  in
               let uu____4246 = FStar_Syntax_Print.term_to_string tv  in
               FStar_Util.print2 ">> Inspected (%s) ~> (%s)\n" uu____4244
                 uu____4246
             else ());
            (let t1 =
               let uu____4254 =
                 let uu____4265 = FStar_Syntax_Syntax.as_arg tv  in
                 [uu____4265]  in
               FStar_Syntax_Util.mk_app
                 (FStar_Reflection_Data.refl_constant_term
                    FStar_Reflection_Data.fstar_refl_pack_ln) uu____4254
                in
             encode_term t1 env))
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_pattern uu____4291) ->
           encode_term t1
             (let uu___366_4309 = env  in
              {
                FStar_SMTEncoding_Env.bvar_bindings =
                  (uu___366_4309.FStar_SMTEncoding_Env.bvar_bindings);
                FStar_SMTEncoding_Env.fvar_bindings =
                  (uu___366_4309.FStar_SMTEncoding_Env.fvar_bindings);
                FStar_SMTEncoding_Env.depth =
                  (uu___366_4309.FStar_SMTEncoding_Env.depth);
                FStar_SMTEncoding_Env.tcenv =
                  (uu___366_4309.FStar_SMTEncoding_Env.tcenv);
                FStar_SMTEncoding_Env.warn =
                  (uu___366_4309.FStar_SMTEncoding_Env.warn);
                FStar_SMTEncoding_Env.cache =
                  (uu___366_4309.FStar_SMTEncoding_Env.cache);
                FStar_SMTEncoding_Env.nolabels =
                  (uu___366_4309.FStar_SMTEncoding_Env.nolabels);
                FStar_SMTEncoding_Env.use_zfuel_name =
                  (uu___366_4309.FStar_SMTEncoding_Env.use_zfuel_name);
                FStar_SMTEncoding_Env.encode_non_total_function_typ =
                  (uu___366_4309.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                FStar_SMTEncoding_Env.current_module_name =
                  (uu___366_4309.FStar_SMTEncoding_Env.current_module_name);
                FStar_SMTEncoding_Env.encoding_quantifier = false;
                FStar_SMTEncoding_Env.global_cache =
                  (uu___366_4309.FStar_SMTEncoding_Env.global_cache)
              })
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____4312) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = FStar_SMTEncoding_Env.lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____4320 = head_redex env t  in
           if uu____4320
           then let uu____4327 = whnf env t  in encode_term uu____4327 env
           else
             (let uu____4330 =
                FStar_SMTEncoding_Env.lookup_free_var_name env
                  v1.FStar_Syntax_Syntax.fv_name
                 in
              match uu____4330 with
              | (uu____4341,arity) ->
                  let tok =
                    FStar_SMTEncoding_Env.lookup_free_var env
                      v1.FStar_Syntax_Syntax.fv_name
                     in
                  let aux_decls =
                    if arity > (Prims.parse_int "0")
                    then
                      match tok.FStar_SMTEncoding_Term.tm with
                      | FStar_SMTEncoding_Term.FreeV uu____4357 ->
                          let uu____4363 =
                            let uu____4364 =
                              let uu____4372 =
                                FStar_SMTEncoding_Term.kick_partial_app tok
                                 in
                              let uu____4373 =
                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                  "@kick_partial_app"
                                 in
                              (uu____4372,
                                (FStar_Pervasives_Native.Some
                                   "kick_partial_app"), uu____4373)
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____4364  in
                          [uu____4363]
                      | FStar_SMTEncoding_Term.App (uu____4379,[]) ->
                          let uu____4382 =
                            let uu____4383 =
                              let uu____4391 =
                                FStar_SMTEncoding_Term.kick_partial_app tok
                                 in
                              let uu____4392 =
                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                  "@kick_partial_app"
                                 in
                              (uu____4391,
                                (FStar_Pervasives_Native.Some
                                   "kick_partial_app"), uu____4392)
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____4383  in
                          [uu____4382]
                      | uu____4398 -> []
                    else []  in
                  let uu____4401 =
                    FStar_All.pipe_right aux_decls
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  (tok, uu____4401))
       | FStar_Syntax_Syntax.Tm_type uu____4404 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4406) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.FStar_SMTEncoding_Env.current_module_name
              in
           let uu____4436 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____4436 with
            | (binders1,res) ->
                let uu____4447 =
                  (env.FStar_SMTEncoding_Env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____4447
                then
                  let uu____4454 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____4454 with
                   | (vars,guards,env',decls,uu____4479) ->
                       let fsym =
                         let uu____4498 =
                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                             "f"
                            in
                         (uu____4498, FStar_SMTEncoding_Term.Term_sort)  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____4504 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___367_4513 =
                              env.FStar_SMTEncoding_Env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___367_4513.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___367_4513.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___367_4513.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___367_4513.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___367_4513.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___367_4513.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___367_4513.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___367_4513.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___367_4513.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___367_4513.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___367_4513.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___367_4513.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___367_4513.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___367_4513.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___367_4513.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___367_4513.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___367_4513.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___367_4513.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___367_4513.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___367_4513.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___367_4513.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___367_4513.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___367_4513.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___367_4513.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___367_4513.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___367_4513.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___367_4513.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___367_4513.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___367_4513.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___367_4513.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___367_4513.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___367_4513.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___367_4513.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___367_4513.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___367_4513.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___367_4513.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___367_4513.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___367_4513.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___367_4513.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___367_4513.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___367_4513.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___367_4513.FStar_TypeChecker_Env.nbe)
                            }) res
                          in
                       (match uu____4504 with
                        | (pre_opt,res_t) ->
                            let uu____4525 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____4525 with
                             | (res_pred,decls') ->
                                 let uu____4536 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____4549 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____4549, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____4553 =
                                         encode_formula pre env'  in
                                       (match uu____4553 with
                                        | (guard,decls0) ->
                                            let uu____4566 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____4566, decls0))
                                    in
                                 (match uu____4536 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____4580 =
                                          let uu____4591 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____4591)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t.FStar_Syntax_Syntax.pos
                                          uu____4580
                                         in
                                      let cvars =
                                        let uu____4608 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____4608
                                          (FStar_List.filter
                                             (fun uu____4638  ->
                                                match uu____4638 with
                                                | (x,uu____4646) ->
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
                                      let uu____4665 =
                                        FStar_Util.smap_try_find
                                          env.FStar_SMTEncoding_Env.cache
                                          tkey_hash
                                         in
                                      (match uu____4665 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____4673 =
                                             let uu____4674 =
                                               let uu____4682 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV)
                                                  in
                                               ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                                 uu____4682)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4674
                                              in
                                           let uu____4702 =
                                             let uu____4703 =
                                               let uu____4706 =
                                                 let uu____4709 =
                                                   FStar_All.pipe_right
                                                     (FStar_SMTEncoding_Env.use_cache_entry
                                                        cache_entry)
                                                     FStar_SMTEncoding_Term.mk_decls_trivial
                                                    in
                                                 FStar_List.append
                                                   guard_decls uu____4709
                                                  in
                                               FStar_List.append decls'
                                                 uu____4706
                                                in
                                             FStar_List.append decls
                                               uu____4703
                                              in
                                           (uu____4673, uu____4702)
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____4718 =
                                               let uu____4720 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____4720
                                                in
                                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                               uu____4718
                                              in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars
                                              in
                                           let caption =
                                             let uu____4733 =
                                               FStar_Options.log_queries ()
                                                in
                                             if uu____4733
                                             then
                                               let uu____4736 =
                                                 let uu____4738 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env.FStar_SMTEncoding_Env.tcenv
                                                     t0
                                                    in
                                                 FStar_Util.replace_char
                                                   uu____4738 10 32
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____4736
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
                                             let uu____4751 =
                                               let uu____4759 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars
                                                  in
                                               (tsym, uu____4759)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4751
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
                                             let uu____4775 =
                                               let uu____4783 =
                                                 FStar_SMTEncoding_Term.mkForall
                                                   t0.FStar_Syntax_Syntax.pos
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind)
                                                  in
                                               (uu____4783,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name)
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4775
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
                                             let uu____4800 =
                                               let uu____4808 =
                                                 let uu____4809 =
                                                   let uu____4820 =
                                                     let uu____4821 =
                                                       let uu____4826 =
                                                         let uu____4827 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f
                                                            in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____4827
                                                          in
                                                       (f_has_t, uu____4826)
                                                        in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____4821
                                                      in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____4820)
                                                    in
                                                 let uu____4842 =
                                                   mkForall_fuel
                                                     t0.FStar_Syntax_Syntax.pos
                                                    in
                                                 uu____4842 uu____4809  in
                                               (uu____4808,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4800
                                              in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym
                                                in
                                             let uu____4865 =
                                               let uu____4873 =
                                                 let uu____4874 =
                                                   let uu____4885 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp)
                                                      in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____4885)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   t0.FStar_Syntax_Syntax.pos
                                                   uu____4874
                                                  in
                                               (uu____4873,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4865
                                              in
                                           let t_decls1 =
                                             [tdecl;
                                             k_assumption;
                                             pre_typing;
                                             t_interp1]  in
                                           ((let uu____4906 =
                                               let uu____4907 =
                                                 let uu____4910 =
                                                   FStar_All.pipe_right
                                                     (FStar_List.append decls
                                                        (FStar_List.append
                                                           decls' guard_decls))
                                                     FStar_SMTEncoding_Term.decls_list_of
                                                    in
                                                 FStar_List.append uu____4910
                                                   t_decls1
                                                  in
                                               FStar_SMTEncoding_Env.mk_cache_entry
                                                 env tsym cvar_sorts
                                                 uu____4907
                                                in
                                             FStar_Util.smap_add
                                               env.FStar_SMTEncoding_Env.cache
                                               tkey_hash uu____4906);
                                            (let uu____4915 =
                                               let uu____4916 =
                                                 let uu____4919 =
                                                   let uu____4922 =
                                                     FStar_SMTEncoding_Term.mk_decls
                                                       tsym cvar_sorts
                                                       tkey_hash t_decls1
                                                       (FStar_List.append
                                                          decls
                                                          (FStar_List.append
                                                             decls'
                                                             guard_decls))
                                                      in
                                                   FStar_List.append
                                                     guard_decls uu____4922
                                                    in
                                                 FStar_List.append decls'
                                                   uu____4919
                                                  in
                                               FStar_List.append decls
                                                 uu____4916
                                                in
                                             (t1, uu____4915))))))))
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
                     let uu____4943 =
                       let uu____4951 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____4951,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____4943  in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)  in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym  in
                     let uu____4970 =
                       let uu____4978 =
                         let uu____4979 =
                           let uu____4990 =
                             let uu____4991 =
                               let uu____4996 =
                                 let uu____4997 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____4997
                                  in
                               (f_has_t, uu____4996)  in
                             FStar_SMTEncoding_Util.mkImp uu____4991  in
                           ([[f_has_t]], [fsym], uu____4990)  in
                         let uu____5017 =
                           mkForall_fuel t0.FStar_Syntax_Syntax.pos  in
                         uu____5017 uu____4979  in
                       (uu____4978, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____4970  in
                   let uu____5035 =
                     FStar_All.pipe_right [tdecl; t_kinding; t_interp]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                      in
                   (t1, uu____5035)))
       | FStar_Syntax_Syntax.Tm_refine uu____5038 ->
           let uu____5045 =
             let uu____5050 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Env.Weak;
                 FStar_TypeChecker_Env.HNF;
                 FStar_TypeChecker_Env.EraseUniverses]
                 env.FStar_SMTEncoding_Env.tcenv t0
                in
             match uu____5050 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____5057;
                 FStar_Syntax_Syntax.vars = uu____5058;_} ->
                 let uu____5065 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____5065 with
                  | (b,f1) ->
                      let uu____5090 =
                        let uu____5091 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____5091  in
                      (uu____5090, f1))
             | uu____5106 -> failwith "impossible"  in
           (match uu____5045 with
            | (x,f) ->
                let uu____5118 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____5118 with
                 | (base_t,decls) ->
                     let uu____5129 =
                       FStar_SMTEncoding_Env.gen_term_var env x  in
                     (match uu____5129 with
                      | (x1,xtm,env') ->
                          let uu____5146 = encode_formula f env'  in
                          (match uu____5146 with
                           | (refinement,decls') ->
                               let uu____5157 =
                                 FStar_SMTEncoding_Env.fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____5157 with
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
                                      let uu____5182 =
                                        let uu____5190 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____5198 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____5190
                                          uu____5198
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____5182
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____5246  ->
                                              match uu____5246 with
                                              | (y,uu____5254) ->
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
                                    (match FStar_Pervasives_Native.None with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____5297 =
                                           let uu____5298 =
                                             let uu____5306 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV)
                                                in
                                             ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                               uu____5306)
                                              in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____5298
                                            in
                                         let uu____5326 =
                                           let uu____5327 =
                                             let uu____5330 =
                                               FStar_All.pipe_right
                                                 (FStar_SMTEncoding_Env.use_cache_entry
                                                    cache_entry)
                                                 FStar_SMTEncoding_Term.mk_decls_trivial
                                                in
                                             FStar_List.append decls'
                                               uu____5330
                                              in
                                           FStar_List.append decls uu____5327
                                            in
                                         (uu____5297, uu____5326)
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.FStar_SMTEncoding_Env.current_module_name
                                            in
                                         let tsym =
                                           let uu____5341 =
                                             let uu____5343 =
                                               let uu____5345 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____5345
                                                in
                                             Prims.strcat module_name
                                               uu____5343
                                              in
                                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                             uu____5341
                                            in
                                         let cvar_sorts =
                                           FStar_List.map
                                             FStar_Pervasives_Native.snd
                                             cvars1
                                            in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None)
                                            in
                                         let t1 =
                                           let uu____5363 =
                                             let uu____5371 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1
                                                in
                                             (tsym, uu____5371)  in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____5363
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
                                           let uu____5388 =
                                             let uu____5396 =
                                               let uu____5397 =
                                                 let uu____5408 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base)
                                                    in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____5408)
                                                  in
                                               FStar_SMTEncoding_Term.mkForall
                                                 t0.FStar_Syntax_Syntax.pos
                                                 uu____5397
                                                in
                                             (uu____5396,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____5388
                                            in
                                         let t_kinding =
                                           let uu____5422 =
                                             let uu____5430 =
                                               FStar_SMTEncoding_Term.mkForall
                                                 t0.FStar_Syntax_Syntax.pos
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind)
                                                in
                                             (uu____5430,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____5422
                                            in
                                         let t_interp =
                                           let uu____5444 =
                                             let uu____5452 =
                                               let uu____5453 =
                                                 let uu____5464 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding)
                                                    in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____5464)
                                                  in
                                               FStar_SMTEncoding_Term.mkForall
                                                 t0.FStar_Syntax_Syntax.pos
                                                 uu____5453
                                                in
                                             (uu____5452,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement_interpretation"),
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____5444
                                            in
                                         let t_decls1 =
                                           [tdecl;
                                           t_kinding;
                                           t_interp;
                                           t_haseq1]  in
                                         ((let uu____5491 =
                                             let uu____5492 =
                                               let uu____5495 =
                                                 FStar_All.pipe_right
                                                   (FStar_List.append decls
                                                      decls')
                                                   FStar_SMTEncoding_Term.decls_list_of
                                                  in
                                               FStar_List.append uu____5495
                                                 t_decls1
                                                in
                                             FStar_SMTEncoding_Env.mk_cache_entry
                                               env tsym cvar_sorts uu____5492
                                              in
                                           FStar_Util.smap_add
                                             env.FStar_SMTEncoding_Env.cache
                                             tkey_hash uu____5491);
                                          (let uu____5500 =
                                             let uu____5501 =
                                               let uu____5504 =
                                                 FStar_SMTEncoding_Term.mk_decls
                                                   tsym cvar_sorts tkey_hash
                                                   t_decls1
                                                   (FStar_List.append decls
                                                      decls')
                                                  in
                                               FStar_List.append decls'
                                                 uu____5504
                                                in
                                             FStar_List.append decls
                                               uu____5501
                                              in
                                           (t1, uu____5500)))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,uu____5508) ->
           let ttm =
             let uu____5526 =
               FStar_Syntax_Unionfind.uvar_id
                 uv.FStar_Syntax_Syntax.ctx_uvar_head
                in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____5526  in
           let uu____5528 =
             encode_term_pred FStar_Pervasives_Native.None
               uv.FStar_Syntax_Syntax.ctx_uvar_typ env ttm
              in
           (match uu____5528 with
            | (t_has_k,decls) ->
                let d =
                  let uu____5540 =
                    let uu____5548 =
                      let uu____5550 =
                        let uu____5552 =
                          let uu____5554 =
                            FStar_Syntax_Unionfind.uvar_id
                              uv.FStar_Syntax_Syntax.ctx_uvar_head
                             in
                          FStar_Util.string_of_int uu____5554  in
                        FStar_Util.format1 "uvar_typing_%s" uu____5552  in
                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                        uu____5550
                       in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____5548)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____5540  in
                let uu____5560 =
                  let uu____5561 =
                    FStar_All.pipe_right [d]
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append decls uu____5561  in
                (ttm, uu____5560))
       | FStar_Syntax_Syntax.Tm_app uu____5568 ->
           let uu____5585 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____5585 with
            | (head1,args_e) ->
                let uu____5632 =
                  let uu____5647 =
                    let uu____5648 = FStar_Syntax_Subst.compress head1  in
                    uu____5648.FStar_Syntax_Syntax.n  in
                  (uu____5647, args_e)  in
                (match uu____5632 with
                 | uu____5665 when head_redex env head1 ->
                     let uu____5680 = whnf env t  in
                     encode_term uu____5680 env
                 | uu____5681 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____5704 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5722) when
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
                       FStar_Syntax_Syntax.pos = uu____5744;
                       FStar_Syntax_Syntax.vars = uu____5745;_},uu____5746),uu____5747)
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
                       FStar_Syntax_Syntax.pos = uu____5773;
                       FStar_Syntax_Syntax.vars = uu____5774;_},uu____5775),
                    (v0,uu____5777)::(v1,uu____5779)::(v2,uu____5781)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____5852 = encode_term v0 env  in
                     (match uu____5852 with
                      | (v01,decls0) ->
                          let uu____5863 = encode_term v1 env  in
                          (match uu____5863 with
                           | (v11,decls1) ->
                               let uu____5874 = encode_term v2 env  in
                               (match uu____5874 with
                                | (v21,decls2) ->
                                    let uu____5885 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____5885,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(v0,uu____5888)::(v1,uu____5890)::(v2,uu____5892)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____5959 = encode_term v0 env  in
                     (match uu____5959 with
                      | (v01,decls0) ->
                          let uu____5970 = encode_term v1 env  in
                          (match uu____5970 with
                           | (v11,decls1) ->
                               let uu____5981 = encode_term v2 env  in
                               (match uu____5981 with
                                | (v21,decls2) ->
                                    let uu____5992 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____5992,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____5994)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____6030)::(rng,uu____6032)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____6083) ->
                     let e0 =
                       let uu____6105 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg
                         env.FStar_SMTEncoding_Env.tcenv head1 uu____6105
                        in
                     ((let uu____6115 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug
                              env.FStar_SMTEncoding_Env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____6115
                       then
                         let uu____6120 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____6120
                       else ());
                      (let e =
                         let uu____6128 =
                           let uu____6133 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____6134 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____6133
                             uu____6134
                            in
                         uu____6128 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____6145),(arg,uu____6147)::[]) -> encode_term arg env
                 | uu____6182 ->
                     let uu____6197 = encode_args args_e env  in
                     (match uu____6197 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____6258 = encode_term head1 env  in
                            match uu____6258 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____6330 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____6330 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____6428  ->
                                                 fun uu____6429  ->
                                                   match (uu____6428,
                                                           uu____6429)
                                                   with
                                                   | ((bv,uu____6459),
                                                      (a,uu____6461)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____6491 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____6491
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____6492 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm
                                             in
                                          (match uu____6492 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type
                                                  in
                                               let e_typing =
                                                 let uu____6507 =
                                                   let uu____6515 =
                                                     FStar_SMTEncoding_Term.mkForall
                                                       t0.FStar_Syntax_Syntax.pos
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____6524 =
                                                     let uu____6526 =
                                                       let uu____6528 =
                                                         let uu____6530 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm
                                                            in
                                                         FStar_Util.digest_of_string
                                                           uu____6530
                                                          in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____6528
                                                        in
                                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                       uu____6526
                                                      in
                                                   (uu____6515,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____6524)
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____6507
                                                  in
                                               let uu____6536 =
                                                 let uu____6539 =
                                                   let uu____6542 =
                                                     let uu____6545 =
                                                       FStar_All.pipe_right
                                                         [e_typing]
                                                         FStar_SMTEncoding_Term.mk_decls_trivial
                                                        in
                                                     FStar_List.append
                                                       decls'' uu____6545
                                                      in
                                                   FStar_List.append decls'
                                                     uu____6542
                                                    in
                                                 FStar_List.append decls
                                                   uu____6539
                                                  in
                                               (app_tm, uu____6536))))
                             in
                          let encode_full_app fv =
                            let uu____6568 =
                              FStar_SMTEncoding_Env.lookup_free_var_sym env
                                fv
                               in
                            match uu____6568 with
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
                                   FStar_Syntax_Syntax.pos = uu____6599;
                                   FStar_Syntax_Syntax.vars = uu____6600;_},uu____6601)
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
                                   FStar_Syntax_Syntax.pos = uu____6608;
                                   FStar_Syntax_Syntax.vars = uu____6609;_},uu____6610)
                                ->
                                let uu____6615 =
                                  let uu____6616 =
                                    let uu____6621 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____6621
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____6616
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____6615
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____6651 =
                                  let uu____6652 =
                                    let uu____6657 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____6657
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____6652
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____6651
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____6686,(FStar_Util.Inl t1,uu____6688),uu____6689)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____6736,(FStar_Util.Inr c,uu____6738),uu____6739)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____6786 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____6807 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Env.Weak;
                                     FStar_TypeChecker_Env.HNF;
                                     FStar_TypeChecker_Env.EraseUniverses]
                                     env.FStar_SMTEncoding_Env.tcenv
                                     head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____6807
                                  in
                               let uu____6808 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____6808 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____6824;
                                            FStar_Syntax_Syntax.vars =
                                              uu____6825;_},uu____6826)
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
                                     | uu____6844 ->
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
           let uu____6923 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____6923 with
            | (bs1,body1,opening) ->
                let fallback uu____6946 =
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
                  let uu____6956 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort)
                     in
                  let uu____6958 =
                    FStar_All.pipe_right [decl]
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  (uu____6956, uu____6958)  in
                let is_impure rc =
                  let uu____6968 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                      env.FStar_SMTEncoding_Env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____6968 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____6983 =
                          let uu____6996 =
                            FStar_TypeChecker_Env.get_range
                              env.FStar_SMTEncoding_Env.tcenv
                             in
                          FStar_TypeChecker_Util.new_implicit_var
                            "SMTEncoding codomain" uu____6996
                            env.FStar_SMTEncoding_Env.tcenv
                            FStar_Syntax_Util.ktype0
                           in
                        (match uu____6983 with
                         | (t1,uu____6999,uu____7000) -> t1)
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  let uu____7018 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                     in
                  if uu____7018
                  then
                    let uu____7023 = FStar_Syntax_Syntax.mk_Total res_typ  in
                    FStar_Pervasives_Native.Some uu____7023
                  else
                    (let uu____7026 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid
                        in
                     if uu____7026
                     then
                       let uu____7031 = FStar_Syntax_Syntax.mk_GTotal res_typ
                          in
                       FStar_Pervasives_Native.Some uu____7031
                     else FStar_Pervasives_Native.None)
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____7039 =
                         let uu____7045 =
                           let uu____7047 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____7047
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____7045)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____7039);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____7052 =
                       (is_impure rc) &&
                         (let uu____7055 =
                            FStar_TypeChecker_Env.is_reifiable_rc
                              env.FStar_SMTEncoding_Env.tcenv rc
                             in
                          Prims.op_Negation uu____7055)
                        in
                     if uu____7052
                     then fallback ()
                     else
                       (let cache_size =
                          FStar_Util.smap_size
                            env.FStar_SMTEncoding_Env.cache
                           in
                        let uu____7066 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____7066 with
                        | (vars,guards,envbody,decls,uu____7091) ->
                            let body2 =
                              let uu____7105 =
                                FStar_TypeChecker_Env.is_reifiable_rc
                                  env.FStar_SMTEncoding_Env.tcenv rc
                                 in
                              if uu____7105
                              then
                                FStar_TypeChecker_Util.reify_body
                                  env.FStar_SMTEncoding_Env.tcenv body1
                              else body1  in
                            let uu____7110 = encode_term body2 envbody  in
                            (match uu____7110 with
                             | (body3,decls') ->
                                 let uu____7121 =
                                   let uu____7130 = codomain_eff rc  in
                                   match uu____7130 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____7149 = encode_term tfun env
                                          in
                                       (match uu____7149 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____7121 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____7183 =
                                          let uu____7194 =
                                            let uu____7195 =
                                              let uu____7200 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____7200, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____7195
                                             in
                                          ([], vars, uu____7194)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t0.FStar_Syntax_Syntax.pos
                                          uu____7183
                                         in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body
                                         in
                                      let uu____7208 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            (cvars, key_body)
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____7239 =
                                              let uu____7247 =
                                                let uu____7255 =
                                                  FStar_SMTEncoding_Term.free_variables
                                                    t1
                                                   in
                                                FStar_List.append uu____7255
                                                  cvars
                                                 in
                                              FStar_Util.remove_dups
                                                FStar_SMTEncoding_Term.fv_eq
                                                uu____7247
                                               in
                                            let uu____7273 =
                                              FStar_SMTEncoding_Util.mkAnd
                                                (key_body, t1)
                                               in
                                            (uu____7239, uu____7273)
                                         in
                                      (match uu____7208 with
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
                                           let uu____7310 =
                                             FStar_Util.smap_try_find
                                               env.FStar_SMTEncoding_Env.cache
                                               tkey_hash
                                              in
                                           (match uu____7310 with
                                            | FStar_Pervasives_Native.Some
                                                cache_entry ->
                                                let uu____7318 =
                                                  let uu____7319 =
                                                    let uu____7327 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                                      uu____7327)
                                                     in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____7319
                                                   in
                                                let uu____7338 =
                                                  let uu____7339 =
                                                    let uu____7342 =
                                                      let uu____7345 =
                                                        FStar_All.pipe_right
                                                          (FStar_SMTEncoding_Env.use_cache_entry
                                                             cache_entry)
                                                          FStar_SMTEncoding_Term.mk_decls_trivial
                                                         in
                                                      FStar_List.append
                                                        decls'' uu____7345
                                                       in
                                                    FStar_List.append decls'
                                                      uu____7342
                                                     in
                                                  FStar_List.append decls
                                                    uu____7339
                                                   in
                                                (uu____7318, uu____7338)
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                let uu____7352 =
                                                  is_an_eta_expansion env
                                                    vars body3
                                                   in
                                                (match uu____7352 with
                                                 | FStar_Pervasives_Native.Some
                                                     t1 ->
                                                     let decls1 =
                                                       let uu____7361 =
                                                         let uu____7363 =
                                                           FStar_Util.smap_size
                                                             env.FStar_SMTEncoding_Env.cache
                                                            in
                                                         uu____7363 =
                                                           cache_size
                                                          in
                                                       if uu____7361
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
                                                         FStar_Pervasives_Native.snd
                                                         cvars1
                                                        in
                                                     let fsym =
                                                       let module_name =
                                                         env.FStar_SMTEncoding_Env.current_module_name
                                                          in
                                                       let fsym =
                                                         let uu____7384 =
                                                           let uu____7386 =
                                                             FStar_Util.digest_of_string
                                                               tkey_hash
                                                              in
                                                           Prims.strcat
                                                             "Tm_abs_"
                                                             uu____7386
                                                            in
                                                         FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                           uu____7384
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
                                                       let uu____7396 =
                                                         let uu____7404 =
                                                           FStar_List.map
                                                             FStar_SMTEncoding_Util.mkFreeV
                                                             cvars1
                                                            in
                                                         (fsym, uu____7404)
                                                          in
                                                       FStar_SMTEncoding_Util.mkApp
                                                         uu____7396
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
                                                           let uu____7426 =
                                                             let uu____7427 =
                                                               let uu____7435
                                                                 =
                                                                 FStar_SMTEncoding_Term.mkForall
                                                                   t0.FStar_Syntax_Syntax.pos
                                                                   ([[f]],
                                                                    cvars1,
                                                                    f_has_t)
                                                                  in
                                                               (uu____7435,
                                                                 (FStar_Pervasives_Native.Some
                                                                    a_name),
                                                                 a_name)
                                                                in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____7427
                                                              in
                                                           [uu____7426]
                                                        in
                                                     let interp_f =
                                                       let a_name =
                                                         Prims.strcat
                                                           "interpretation_"
                                                           fsym
                                                          in
                                                       let uu____7450 =
                                                         let uu____7458 =
                                                           let uu____7459 =
                                                             let uu____7470 =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (app, body3)
                                                                in
                                                             ([[app]],
                                                               (FStar_List.append
                                                                  vars cvars1),
                                                               uu____7470)
                                                              in
                                                           FStar_SMTEncoding_Term.mkForall
                                                             t0.FStar_Syntax_Syntax.pos
                                                             uu____7459
                                                            in
                                                         (uu____7458,
                                                           (FStar_Pervasives_Native.Some
                                                              a_name),
                                                           a_name)
                                                          in
                                                       FStar_SMTEncoding_Util.mkAssume
                                                         uu____7450
                                                        in
                                                     let f_decls =
                                                       FStar_List.append
                                                         (fdecl :: typing_f)
                                                         [interp_f]
                                                        in
                                                     ((let uu____7485 =
                                                         let uu____7486 =
                                                           let uu____7489 =
                                                             FStar_All.pipe_right
                                                               (FStar_List.append
                                                                  decls
                                                                  (FStar_List.append
                                                                    decls'
                                                                    decls''))
                                                               FStar_SMTEncoding_Term.decls_list_of
                                                              in
                                                           FStar_List.append
                                                             uu____7489
                                                             f_decls
                                                            in
                                                         FStar_SMTEncoding_Env.mk_cache_entry
                                                           env fsym
                                                           cvar_sorts
                                                           uu____7486
                                                          in
                                                       FStar_Util.smap_add
                                                         env.FStar_SMTEncoding_Env.cache
                                                         tkey_hash uu____7485);
                                                      (let uu____7494 =
                                                         let uu____7495 =
                                                           let uu____7498 =
                                                             let uu____7501 =
                                                               FStar_SMTEncoding_Term.mk_decls
                                                                 fsym
                                                                 cvar_sorts
                                                                 tkey_hash
                                                                 f_decls
                                                                 (FStar_List.append
                                                                    decls
                                                                    (
                                                                    FStar_List.append
                                                                    decls'
                                                                    decls''))
                                                                in
                                                             FStar_List.append
                                                               decls''
                                                               uu____7501
                                                              in
                                                           FStar_List.append
                                                             decls'
                                                             uu____7498
                                                            in
                                                         FStar_List.append
                                                           decls uu____7495
                                                          in
                                                       (f, uu____7494)))))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____7504,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____7505;
                          FStar_Syntax_Syntax.lbunivs = uu____7506;
                          FStar_Syntax_Syntax.lbtyp = uu____7507;
                          FStar_Syntax_Syntax.lbeff = uu____7508;
                          FStar_Syntax_Syntax.lbdef = uu____7509;
                          FStar_Syntax_Syntax.lbattrs = uu____7510;
                          FStar_Syntax_Syntax.lbpos = uu____7511;_}::uu____7512),uu____7513)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____7547;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____7549;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____7551;
                FStar_Syntax_Syntax.lbpos = uu____7552;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____7579 ->
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
              let uu____7651 =
                let uu____7656 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____7656 env  in
              match uu____7651 with
              | (ee1,decls1) ->
                  let uu____7681 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____7681 with
                   | (xs,e21) ->
                       let uu____7706 = FStar_List.hd xs  in
                       (match uu____7706 with
                        | (x1,uu____7724) ->
                            let env' =
                              FStar_SMTEncoding_Env.push_term_var env x1 ee1
                               in
                            let uu____7730 = encode_body e21 env'  in
                            (match uu____7730 with
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
            let uu____7760 =
              let uu____7768 =
                let uu____7769 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____7769  in
              FStar_SMTEncoding_Env.gen_term_var env uu____7768  in
            match uu____7760 with
            | (scrsym,scr',env1) ->
                let uu____7779 = encode_term e env1  in
                (match uu____7779 with
                 | (scr,decls) ->
                     let uu____7790 =
                       let encode_branch b uu____7819 =
                         match uu____7819 with
                         | (else_case,decls1) ->
                             let uu____7838 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____7838 with
                              | (p,w,br) ->
                                  let uu____7864 = encode_pat env1 p  in
                                  (match uu____7864 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____7901  ->
                                                   match uu____7901 with
                                                   | (x,t) ->
                                                       FStar_SMTEncoding_Env.push_term_var
                                                         env2 x t) env1)
                                          in
                                       let uu____7908 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____7930 =
                                               encode_term w1 env2  in
                                             (match uu____7930 with
                                              | (w2,decls2) ->
                                                  let uu____7943 =
                                                    let uu____7944 =
                                                      let uu____7949 =
                                                        let uu____7950 =
                                                          let uu____7955 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____7955)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____7950
                                                         in
                                                      (guard, uu____7949)  in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____7944
                                                     in
                                                  (uu____7943, decls2))
                                          in
                                       (match uu____7908 with
                                        | (guard1,decls2) ->
                                            let uu____7970 =
                                              encode_br br env2  in
                                            (match uu____7970 with
                                             | (br1,decls3) ->
                                                 let uu____7983 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____7983,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____7790 with
                      | (match_tm,decls1) ->
                          let uu____8004 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange
                             in
                          (uu____8004, decls1)))

and (encode_pat :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.pat -> (FStar_SMTEncoding_Env.env_t * pattern))
  =
  fun env  ->
    fun pat  ->
      (let uu____8027 =
         FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
           FStar_Options.Medium
          in
       if uu____8027
       then
         let uu____8030 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____8030
       else ());
      (let uu____8035 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____8035 with
       | (vars,pat_term) ->
           let uu____8052 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____8108  ->
                     fun v1  ->
                       match uu____8108 with
                       | (env1,vars1) ->
                           let uu____8164 =
                             FStar_SMTEncoding_Env.gen_term_var env1 v1  in
                           (match uu____8164 with
                            | (xx,uu____8188,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, []))
              in
           (match uu____8052 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____8281 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____8282 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____8283 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____8291 = encode_const c env1  in
                      (match uu____8291 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____8299::uu____8300 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____8304 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon
                            env1.FStar_SMTEncoding_Env.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____8327 =
                          FStar_TypeChecker_Env.datacons_of_typ
                            env1.FStar_SMTEncoding_Env.tcenv tc_name
                           in
                        match uu____8327 with
                        | (uu____8335,uu____8336::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____8341 ->
                            FStar_SMTEncoding_Env.mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____8377  ->
                                  match uu____8377 with
                                  | (arg,uu____8387) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____8396 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____8396))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____8428) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____8459 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____8484 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____8530  ->
                                  match uu____8530 with
                                  | (arg,uu____8546) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____8555 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____8555))
                         in
                      FStar_All.pipe_right uu____8484 FStar_List.flatten
                   in
                let pat_term1 uu____8586 = encode_term pat_term env1  in
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
      let uu____8596 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____8644  ->
                fun uu____8645  ->
                  match (uu____8644, uu____8645) with
                  | ((tms,decls),(t,uu____8685)) ->
                      let uu____8712 = encode_term t env  in
                      (match uu____8712 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____8596 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____8769 = FStar_Syntax_Util.list_elements e  in
        match uu____8769 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____8800 =
          let uu____8817 = FStar_Syntax_Util.unmeta p  in
          FStar_All.pipe_right uu____8817 FStar_Syntax_Util.head_and_args  in
        match uu____8800 with
        | (head1,args) ->
            let uu____8868 =
              let uu____8883 =
                let uu____8884 = FStar_Syntax_Util.un_uinst head1  in
                uu____8884.FStar_Syntax_Syntax.n  in
              (uu____8883, args)  in
            (match uu____8868 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____8906,uu____8907)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____8959 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or1 t1 =
          let uu____9014 =
            let uu____9031 = FStar_Syntax_Util.unmeta t1  in
            FStar_All.pipe_right uu____9031 FStar_Syntax_Util.head_and_args
             in
          match uu____9014 with
          | (head1,args) ->
              let uu____9078 =
                let uu____9093 =
                  let uu____9094 = FStar_Syntax_Util.un_uinst head1  in
                  uu____9094.FStar_Syntax_Syntax.n  in
                (uu____9093, args)  in
              (match uu____9078 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____9113)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____9150 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____9180 = smt_pat_or1 t1  in
            (match uu____9180 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____9202 = list_elements1 e  in
                 FStar_All.pipe_right uu____9202
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____9232 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____9232
                           (FStar_List.map one_pat)))
             | uu____9255 ->
                 let uu____9260 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____9260])
        | uu____9311 ->
            let uu____9314 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____9314]
         in
      let uu____9365 =
        let uu____9380 =
          let uu____9381 = FStar_Syntax_Subst.compress t  in
          uu____9381.FStar_Syntax_Syntax.n  in
        match uu____9380 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____9420 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____9420 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____9455;
                        FStar_Syntax_Syntax.effect_name = uu____9456;
                        FStar_Syntax_Syntax.result_typ = uu____9457;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____9459)::(post,uu____9461)::(pats,uu____9463)::[];
                        FStar_Syntax_Syntax.flags = uu____9464;_}
                      ->
                      let uu____9525 = lemma_pats pats  in
                      (binders1, pre, post, uu____9525)
                  | uu____9536 -> failwith "impos"))
        | uu____9552 -> failwith "Impos"  in
      match uu____9365 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___368_9589 = env  in
            {
              FStar_SMTEncoding_Env.bvar_bindings =
                (uu___368_9589.FStar_SMTEncoding_Env.bvar_bindings);
              FStar_SMTEncoding_Env.fvar_bindings =
                (uu___368_9589.FStar_SMTEncoding_Env.fvar_bindings);
              FStar_SMTEncoding_Env.depth =
                (uu___368_9589.FStar_SMTEncoding_Env.depth);
              FStar_SMTEncoding_Env.tcenv =
                (uu___368_9589.FStar_SMTEncoding_Env.tcenv);
              FStar_SMTEncoding_Env.warn =
                (uu___368_9589.FStar_SMTEncoding_Env.warn);
              FStar_SMTEncoding_Env.cache =
                (uu___368_9589.FStar_SMTEncoding_Env.cache);
              FStar_SMTEncoding_Env.nolabels =
                (uu___368_9589.FStar_SMTEncoding_Env.nolabels);
              FStar_SMTEncoding_Env.use_zfuel_name = true;
              FStar_SMTEncoding_Env.encode_non_total_function_typ =
                (uu___368_9589.FStar_SMTEncoding_Env.encode_non_total_function_typ);
              FStar_SMTEncoding_Env.current_module_name =
                (uu___368_9589.FStar_SMTEncoding_Env.current_module_name);
              FStar_SMTEncoding_Env.encoding_quantifier =
                (uu___368_9589.FStar_SMTEncoding_Env.encoding_quantifier);
              FStar_SMTEncoding_Env.global_cache =
                (uu___368_9589.FStar_SMTEncoding_Env.global_cache)
            }  in
          let uu____9591 =
            encode_binders FStar_Pervasives_Native.None binders env1  in
          (match uu____9591 with
           | (vars,guards,env2,decls,uu____9616) ->
               let uu____9629 = encode_smt_patterns patterns env2  in
               (match uu____9629 with
                | (pats,decls') ->
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
                    let env3 =
                      let uu___369_9656 = env2  in
                      {
                        FStar_SMTEncoding_Env.bvar_bindings =
                          (uu___369_9656.FStar_SMTEncoding_Env.bvar_bindings);
                        FStar_SMTEncoding_Env.fvar_bindings =
                          (uu___369_9656.FStar_SMTEncoding_Env.fvar_bindings);
                        FStar_SMTEncoding_Env.depth =
                          (uu___369_9656.FStar_SMTEncoding_Env.depth);
                        FStar_SMTEncoding_Env.tcenv =
                          (uu___369_9656.FStar_SMTEncoding_Env.tcenv);
                        FStar_SMTEncoding_Env.warn =
                          (uu___369_9656.FStar_SMTEncoding_Env.warn);
                        FStar_SMTEncoding_Env.cache =
                          (uu___369_9656.FStar_SMTEncoding_Env.cache);
                        FStar_SMTEncoding_Env.nolabels = true;
                        FStar_SMTEncoding_Env.use_zfuel_name =
                          (uu___369_9656.FStar_SMTEncoding_Env.use_zfuel_name);
                        FStar_SMTEncoding_Env.encode_non_total_function_typ =
                          (uu___369_9656.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                        FStar_SMTEncoding_Env.current_module_name =
                          (uu___369_9656.FStar_SMTEncoding_Env.current_module_name);
                        FStar_SMTEncoding_Env.encoding_quantifier =
                          (uu___369_9656.FStar_SMTEncoding_Env.encoding_quantifier);
                        FStar_SMTEncoding_Env.global_cache =
                          (uu___369_9656.FStar_SMTEncoding_Env.global_cache)
                      }  in
                    let uu____9658 =
                      let uu____9663 = FStar_Syntax_Util.unmeta pre  in
                      encode_formula uu____9663 env3  in
                    (match uu____9658 with
                     | (pre1,decls'') ->
                         let uu____9670 =
                           let uu____9675 = FStar_Syntax_Util.unmeta post1
                              in
                           encode_formula uu____9675 env3  in
                         (match uu____9670 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append decls'
                                     (FStar_List.append decls'' decls'''))
                                 in
                              let uu____9685 =
                                let uu____9686 =
                                  let uu____9697 =
                                    let uu____9698 =
                                      let uu____9703 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards)
                                         in
                                      (uu____9703, post2)  in
                                    FStar_SMTEncoding_Util.mkImp uu____9698
                                     in
                                  (pats, vars, uu____9697)  in
                                FStar_SMTEncoding_Term.mkForall
                                  t.FStar_Syntax_Syntax.pos uu____9686
                                 in
                              (uu____9685, decls1)))))

and (encode_smt_patterns :
  FStar_Syntax_Syntax.arg Prims.list Prims.list ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term Prims.list Prims.list *
        FStar_SMTEncoding_Term.decls_t))
  =
  fun pats_l  ->
    fun env  ->
      let env1 =
        let uu___370_9723 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___370_9723.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___370_9723.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___370_9723.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___370_9723.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___370_9723.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.cache =
            (uu___370_9723.FStar_SMTEncoding_Env.cache);
          FStar_SMTEncoding_Env.nolabels =
            (uu___370_9723.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___370_9723.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___370_9723.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___370_9723.FStar_SMTEncoding_Env.encoding_quantifier);
          FStar_SMTEncoding_Env.global_cache =
            (uu___370_9723.FStar_SMTEncoding_Env.global_cache)
        }  in
      let encode_smt_pattern t =
        let uu____9739 = FStar_Syntax_Util.head_and_args t  in
        match uu____9739 with
        | (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____9802::(x,uu____9804)::(t1,uu____9806)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____9873 = encode_term x env1  in
                 (match uu____9873 with
                  | (x1,decls) ->
                      let uu____9884 = encode_term t1 env1  in
                      (match uu____9884 with
                       | (t2,decls') ->
                           let uu____9895 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                           (uu____9895, (FStar_List.append decls decls'))))
             | uu____9896 -> encode_term t env1)
         in
      FStar_List.fold_right
        (fun pats  ->
           fun uu____9939  ->
             match uu____9939 with
             | (pats_l1,decls) ->
                 let uu____9984 =
                   FStar_List.fold_right
                     (fun uu____10019  ->
                        fun uu____10020  ->
                          match (uu____10019, uu____10020) with
                          | ((p,uu____10062),(pats1,decls1)) ->
                              let uu____10097 = encode_smt_pattern p  in
                              (match uu____10097 with
                               | (t,d) ->
                                   let uu____10112 =
                                     FStar_SMTEncoding_Term.check_pattern_ok
                                       t
                                      in
                                   (match uu____10112 with
                                    | FStar_Pervasives_Native.None  ->
                                        ((t :: pats1),
                                          (FStar_List.append d decls1))
                                    | FStar_Pervasives_Native.Some
                                        illegal_subterm ->
                                        ((let uu____10129 =
                                            let uu____10135 =
                                              let uu____10137 =
                                                FStar_Syntax_Print.term_to_string
                                                  p
                                                 in
                                              let uu____10139 =
                                                FStar_SMTEncoding_Term.print_smt_term
                                                  illegal_subterm
                                                 in
                                              FStar_Util.format2
                                                "Pattern %s contains illegal sub-term (%s); dropping it"
                                                uu____10137 uu____10139
                                               in
                                            (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                                              uu____10135)
                                             in
                                          FStar_Errors.log_issue
                                            p.FStar_Syntax_Syntax.pos
                                            uu____10129);
                                         (pats1,
                                           (FStar_List.append d decls1))))))
                     pats ([], decls)
                    in
                 (match uu____9984 with
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
        let uu____10199 =
          FStar_All.pipe_left
            (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____10199
        then
          let uu____10204 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____10206 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10204 uu____10206
        else ()  in
      let enc f r l =
        let uu____10248 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10280 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____10280 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____10248 with
        | (decls,args) ->
            let uu____10311 =
              let uu___371_10312 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___371_10312.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___371_10312.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10311, decls)
         in
      let const_op f r uu____10347 =
        let uu____10360 = f r  in (uu____10360, [])  in
      let un_op f l =
        let uu____10383 = FStar_List.hd l  in
        FStar_All.pipe_left f uu____10383  in
      let bin_op f uu___362_10403 =
        match uu___362_10403 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10414 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____10455 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____10480  ->
                 match uu____10480 with
                 | (t,uu____10496) ->
                     let uu____10501 = encode_formula t env  in
                     (match uu____10501 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____10455 with
        | (decls,phis) ->
            let uu____10530 =
              let uu___372_10531 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___372_10531.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___372_10531.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10530, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____10594  ->
               match uu____10594 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____10615) -> false
                    | uu____10618 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____10637 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____10637
        else
          (let uu____10654 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____10654 r rf)
         in
      let eq3_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____10726 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::t1::v0::v1::[] ->
                     let uu____10758 =
                       let uu____10763 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____10764 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____10763, uu____10764)  in
                     FStar_SMTEncoding_Util.mkAnd uu____10758
                 | uu____10765 -> failwith "Impossible")
             in
          uu____10726 r args
        else
          (let uu____10771 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____10771)
         in
      let h_equals_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____10843 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::v0::t1::v1::[] ->
                     let uu____10875 =
                       let uu____10880 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____10881 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____10880, uu____10881)  in
                     FStar_SMTEncoding_Util.mkAnd uu____10875
                 | uu____10882 -> failwith "Impossible")
             in
          uu____10843 r args
        else
          (let uu____10888 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____10888)
         in
      let mk_imp1 r uu___363_10923 =
        match uu___363_10923 with
        | (lhs,uu____10929)::(rhs,uu____10931)::[] ->
            let uu____10972 = encode_formula rhs env  in
            (match uu____10972 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____10987) ->
                      (l1, decls1)
                  | uu____10992 ->
                      let uu____10993 = encode_formula lhs env  in
                      (match uu____10993 with
                       | (l2,decls2) ->
                           let uu____11004 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____11004, (FStar_List.append decls1 decls2)))))
        | uu____11005 -> failwith "impossible"  in
      let mk_ite r uu___364_11033 =
        match uu___364_11033 with
        | (guard,uu____11039)::(_then,uu____11041)::(_else,uu____11043)::[]
            ->
            let uu____11100 = encode_formula guard env  in
            (match uu____11100 with
             | (g,decls1) ->
                 let uu____11111 = encode_formula _then env  in
                 (match uu____11111 with
                  | (t,decls2) ->
                      let uu____11122 = encode_formula _else env  in
                      (match uu____11122 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11134 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____11164 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l
           in
        f uu____11164  in
      let connectives =
        let uu____11194 =
          let uu____11219 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____11219)  in
        let uu____11262 =
          let uu____11289 =
            let uu____11314 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____11314)  in
          let uu____11357 =
            let uu____11384 =
              let uu____11411 =
                let uu____11436 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____11436)  in
              let uu____11479 =
                let uu____11506 =
                  let uu____11533 =
                    let uu____11558 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____11558)  in
                  [uu____11533;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.c_eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq3_op);
                  (FStar_Parser_Const.c_eq3_lid, h_equals_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11506  in
              uu____11411 :: uu____11479  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11384  in
          uu____11289 :: uu____11357  in
        uu____11194 :: uu____11262  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____12103 = encode_formula phi' env  in
            (match uu____12103 with
             | (phi2,decls) ->
                 let uu____12114 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____12114, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____12116 ->
            let uu____12123 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____12123 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____12162 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____12162 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____12174;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____12176;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____12178;
                 FStar_Syntax_Syntax.lbpos = uu____12179;_}::[]),e2)
            ->
            let uu____12206 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____12206 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____12259::(x,uu____12261)::(t,uu____12263)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12330 = encode_term x env  in
                 (match uu____12330 with
                  | (x1,decls) ->
                      let uu____12341 = encode_term t env  in
                      (match uu____12341 with
                       | (t1,decls') ->
                           let uu____12352 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____12352, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12355)::(msg,uu____12357)::(phi2,uu____12359)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12426 =
                   let uu____12431 =
                     let uu____12432 = FStar_Syntax_Subst.compress r  in
                     uu____12432.FStar_Syntax_Syntax.n  in
                   let uu____12435 =
                     let uu____12436 = FStar_Syntax_Subst.compress msg  in
                     uu____12436.FStar_Syntax_Syntax.n  in
                   (uu____12431, uu____12435)  in
                 (match uu____12426 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12445))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____12456 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____12463)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____12498 when head_redex env head2 ->
                 let uu____12513 = whnf env phi1  in
                 encode_formula uu____12513 env
             | uu____12514 ->
                 let uu____12529 = encode_term phi1 env  in
                 (match uu____12529 with
                  | (tt,decls) ->
                      let tt1 =
                        let uu____12541 =
                          let uu____12543 =
                            FStar_Range.use_range
                              tt.FStar_SMTEncoding_Term.rng
                             in
                          let uu____12544 =
                            FStar_Range.use_range
                              phi1.FStar_Syntax_Syntax.pos
                             in
                          FStar_Range.rng_included uu____12543 uu____12544
                           in
                        if uu____12541
                        then tt
                        else
                          (let uu___373_12548 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___373_12548.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___373_12548.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      let uu____12549 = FStar_SMTEncoding_Term.mk_Valid tt1
                         in
                      (uu____12549, decls)))
        | uu____12550 ->
            let uu____12551 = encode_term phi1 env  in
            (match uu____12551 with
             | (tt,decls) ->
                 let tt1 =
                   let uu____12563 =
                     let uu____12565 =
                       FStar_Range.use_range tt.FStar_SMTEncoding_Term.rng
                        in
                     let uu____12566 =
                       FStar_Range.use_range phi1.FStar_Syntax_Syntax.pos  in
                     FStar_Range.rng_included uu____12565 uu____12566  in
                   if uu____12563
                   then tt
                   else
                     (let uu___374_12570 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___374_12570.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___374_12570.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 let uu____12571 = FStar_SMTEncoding_Term.mk_Valid tt1  in
                 (uu____12571, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____12615 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____12615 with
        | (vars,guards,env2,decls,uu____12654) ->
            let uu____12667 = encode_smt_patterns ps env2  in
            (match uu____12667 with
             | (pats,decls') ->
                 let uu____12704 = encode_formula body env2  in
                 (match uu____12704 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12736;
                             FStar_SMTEncoding_Term.rng = uu____12737;_}::[])::[]
                            when
                            let uu____12754 =
                              FStar_Ident.text_of_lid
                                FStar_Parser_Const.guard_free
                               in
                            uu____12754 = gf -> []
                        | uu____12757 -> guards  in
                      let uu____12762 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____12762, body1,
                        (FStar_List.append decls
                           (FStar_List.append decls' decls'')))))
         in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi  in
       let uu____12773 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____12773 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12782 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____12888  ->
                     match uu____12888 with
                     | (l,uu____12913) -> FStar_Ident.lid_equals op l))
              in
           (match uu____12782 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____12982,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____13074 = encode_q_body env vars pats body  in
             match uu____13074 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____13119 =
                     let uu____13130 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____13130)  in
                   FStar_SMTEncoding_Term.mkForall
                     phi1.FStar_Syntax_Syntax.pos uu____13119
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____13161 = encode_q_body env vars pats body  in
             match uu____13161 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____13205 =
                   let uu____13206 =
                     let uu____13217 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____13217)  in
                   FStar_SMTEncoding_Term.mkExists
                     phi1.FStar_Syntax_Syntax.pos uu____13206
                    in
                 (uu____13205, decls))))
