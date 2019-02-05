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
               (fun uu___358_367  ->
                  match uu___358_367 with
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
  fun uu___359_671  ->
    match uu___359_671 with
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
                FStar_SMTEncoding_Env.lookup_local_cache env sz_key  in
              match uu____2945 with
              | FStar_Pervasives_Native.Some elt ->
                  FStar_SMTEncoding_Env.use_cache_entry elt
              | FStar_Pervasives_Native.None  ->
                  let t_decls1 = FStar_SMTEncoding_Term.mkBvConstructor sz
                     in
                  let uu____2954 =
                    FStar_SMTEncoding_Term.mk_decls "" sz_key t_decls1 []  in
                  FStar_SMTEncoding_Env.add_to_local_cache env uu____2954
               in
            let uu____2956 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____2982::(sz_arg,uu____2984)::uu____2985::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____3052 =
                    let uu____3053 = FStar_List.tail args_e  in
                    FStar_List.tail uu____3053  in
                  let uu____3056 =
                    let uu____3060 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____3060  in
                  (uu____3052, uu____3056)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____3067::(sz_arg,uu____3069)::uu____3070::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____3137 =
                    let uu____3139 = FStar_Syntax_Print.term_to_string sz_arg
                       in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____3139
                     in
                  failwith uu____3137
              | uu____3149 ->
                  let uu____3164 = FStar_List.tail args_e  in
                  (uu____3164, FStar_Pervasives_Native.None)
               in
            (match uu____2956 with
             | (arg_tms,ext_sz) ->
                 let uu____3183 = encode_args arg_tms env  in
                 (match uu____3183 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____3204 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____3216 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____3216  in
                      let unary_arith arg_tms2 =
                        let uu____3227 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____3227  in
                      let binary arg_tms2 =
                        let uu____3242 =
                          let uu____3243 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3243
                           in
                        let uu____3244 =
                          let uu____3245 =
                            let uu____3246 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____3246  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3245
                           in
                        (uu____3242, uu____3244)  in
                      let binary_arith arg_tms2 =
                        let uu____3263 =
                          let uu____3264 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3264
                           in
                        let uu____3265 =
                          let uu____3266 =
                            let uu____3267 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____3267  in
                          FStar_SMTEncoding_Term.unboxInt uu____3266  in
                        (uu____3263, uu____3265)  in
                      let mk_bv op mk_args resBox ts =
                        let uu____3325 =
                          let uu____3326 = mk_args ts  in op uu____3326  in
                        FStar_All.pipe_right uu____3325 resBox  in
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
                        let uu____3458 =
                          let uu____3463 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____3463  in
                        let uu____3472 =
                          let uu____3477 =
                            let uu____3479 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____3479  in
                          FStar_SMTEncoding_Term.boxBitVec uu____3477  in
                        mk_bv uu____3458 unary uu____3472 arg_tms2  in
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
                      let uu____3719 =
                        let uu____3729 =
                          FStar_List.tryFind
                            (fun uu____3753  ->
                               match uu____3753 with
                               | (l,uu____3764) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____3729 FStar_Util.must  in
                      (match uu____3719 with
                       | (uu____3810,op) ->
                           let uu____3822 = op arg_tms1  in
                           (uu____3822, (FStar_List.append sz_decls decls)))))

and (encode_deeply_embedded_quantifier :
  FStar_Syntax_Syntax.term ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let env1 =
        let uu___363_3832 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___363_3832.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___363_3832.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___363_3832.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___363_3832.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___363_3832.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___363_3832.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name =
            (uu___363_3832.FStar_SMTEncoding_Env.use_zfuel_name);
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___363_3832.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___363_3832.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier = true;
          FStar_SMTEncoding_Env.global_cache =
            (uu___363_3832.FStar_SMTEncoding_Env.global_cache);
          FStar_SMTEncoding_Env.local_cache =
            (uu___363_3832.FStar_SMTEncoding_Env.local_cache)
        }  in
      let uu____3834 = encode_term t env1  in
      match uu____3834 with
      | (tm,decls) ->
          let vars = FStar_SMTEncoding_Term.free_variables tm  in
          let valid_tm = FStar_SMTEncoding_Term.mk_Valid tm  in
          let key =
            FStar_SMTEncoding_Term.mkForall t.FStar_Syntax_Syntax.pos
              ([], vars, valid_tm)
             in
          let tkey_hash = FStar_SMTEncoding_Term.hash_of_term key  in
          let uu____3856 =
            FStar_SMTEncoding_Env.lookup_local_cache env1 tkey_hash  in
          (match uu____3856 with
           | FStar_Pervasives_Native.Some elt ->
               let uu____3864 = FStar_SMTEncoding_Env.use_cache_entry elt  in
               (tm, uu____3864)
           | FStar_Pervasives_Native.None  ->
               (match tm.FStar_SMTEncoding_Term.tm with
                | FStar_SMTEncoding_Term.App
                    (uu____3869,{
                                  FStar_SMTEncoding_Term.tm =
                                    FStar_SMTEncoding_Term.FreeV uu____3870;
                                  FStar_SMTEncoding_Term.freevars =
                                    uu____3871;
                                  FStar_SMTEncoding_Term.rng = uu____3872;_}::
                     {
                       FStar_SMTEncoding_Term.tm =
                         FStar_SMTEncoding_Term.FreeV uu____3873;
                       FStar_SMTEncoding_Term.freevars = uu____3874;
                       FStar_SMTEncoding_Term.rng = uu____3875;_}::[])
                    ->
                    (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                       (FStar_Errors.Warning_QuantifierWithoutPattern,
                         "Not encoding deeply embedded, unguarded quantifier to SMT");
                     (tm, decls))
                | uu____3909 ->
                    let uu____3910 = encode_formula t env1  in
                    (match uu____3910 with
                     | (phi,decls') ->
                         let interp =
                           match vars with
                           | [] ->
                               let uu____3927 =
                                 let uu____3932 =
                                   FStar_SMTEncoding_Term.mk_Valid tm  in
                                 (uu____3932, phi)  in
                               FStar_SMTEncoding_Util.mkIff uu____3927
                           | uu____3933 ->
                               let uu____3934 =
                                 let uu____3945 =
                                   let uu____3946 =
                                     let uu____3951 =
                                       FStar_SMTEncoding_Term.mk_Valid tm  in
                                     (uu____3951, phi)  in
                                   FStar_SMTEncoding_Util.mkIff uu____3946
                                    in
                                 ([[valid_tm]], vars, uu____3945)  in
                               FStar_SMTEncoding_Term.mkForall
                                 t.FStar_Syntax_Syntax.pos uu____3934
                            in
                         let ax =
                           let uu____3961 =
                             let uu____3969 =
                               let uu____3971 =
                                 FStar_Util.digest_of_string tkey_hash  in
                               Prims.strcat "l_quant_interp_" uu____3971  in
                             (interp,
                               (FStar_Pervasives_Native.Some
                                  "Interpretation of deeply embedded quantifier"),
                               uu____3969)
                              in
                           FStar_SMTEncoding_Util.mkAssume uu____3961  in
                         let uu____3977 =
                           let uu____3978 =
                             let uu____3981 =
                               let uu____3984 =
                                 FStar_SMTEncoding_Term.mk_decls "" tkey_hash
                                   [ax] (FStar_List.append decls decls')
                                  in
                               FStar_SMTEncoding_Env.add_to_local_cache env1
                                 uu____3984
                                in
                             FStar_List.append decls' uu____3981  in
                           FStar_List.append decls uu____3978  in
                         (tm, uu____3977))))

and (encode_term :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____3994 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____3994
       then
         let uu____3999 = FStar_Syntax_Print.tag_of_term t  in
         let uu____4001 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____4003 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____3999 uu____4001
           uu____4003
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____4012 ->
           let uu____4035 =
             let uu____4037 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____4040 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____4042 = FStar_Syntax_Print.term_to_string t0  in
             let uu____4044 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____4037
               uu____4040 uu____4042 uu____4044
              in
           failwith uu____4035
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____4051 =
             let uu____4053 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____4056 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____4058 = FStar_Syntax_Print.term_to_string t0  in
             let uu____4060 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____4053
               uu____4056 uu____4058 uu____4060
              in
           failwith uu____4051
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let e = FStar_Syntax_Util.unfold_lazy i  in
           ((let uu____4070 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____4070
             then
               let uu____4075 = FStar_Syntax_Print.term_to_string t0  in
               let uu____4077 = FStar_Syntax_Print.term_to_string e  in
               FStar_Util.print2 ">> Unfolded (%s) ~> (%s)\n" uu____4075
                 uu____4077
             else ());
            encode_term e env)
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____4083 =
             let uu____4085 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____4085
              in
           failwith uu____4083
       | FStar_Syntax_Syntax.Tm_ascribed (t1,(k,uu____4094),uu____4095) ->
           let uu____4144 =
             match k with
             | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
             | uu____4154 -> false  in
           if uu____4144
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t1 env
       | FStar_Syntax_Syntax.Tm_quoted (qt,uu____4172) ->
           let tv =
             let uu____4178 =
               let uu____4185 = FStar_Reflection_Basic.inspect_ln qt  in
               FStar_Syntax_Embeddings.embed
                 FStar_Reflection_Embeddings.e_term_view uu____4185
                in
             uu____4178 t.FStar_Syntax_Syntax.pos
               FStar_Pervasives_Native.None
               FStar_Syntax_Embeddings.id_norm_cb
              in
           ((let uu____4212 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____4212
             then
               let uu____4217 = FStar_Syntax_Print.term_to_string t0  in
               let uu____4219 = FStar_Syntax_Print.term_to_string tv  in
               FStar_Util.print2 ">> Inspected (%s) ~> (%s)\n" uu____4217
                 uu____4219
             else ());
            (let t1 =
               let uu____4227 =
                 let uu____4238 = FStar_Syntax_Syntax.as_arg tv  in
                 [uu____4238]  in
               FStar_Syntax_Util.mk_app
                 (FStar_Reflection_Data.refl_constant_term
                    FStar_Reflection_Data.fstar_refl_pack_ln) uu____4227
                in
             encode_term t1 env))
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_pattern uu____4264) ->
           encode_term t1
             (let uu___364_4282 = env  in
              {
                FStar_SMTEncoding_Env.bvar_bindings =
                  (uu___364_4282.FStar_SMTEncoding_Env.bvar_bindings);
                FStar_SMTEncoding_Env.fvar_bindings =
                  (uu___364_4282.FStar_SMTEncoding_Env.fvar_bindings);
                FStar_SMTEncoding_Env.depth =
                  (uu___364_4282.FStar_SMTEncoding_Env.depth);
                FStar_SMTEncoding_Env.tcenv =
                  (uu___364_4282.FStar_SMTEncoding_Env.tcenv);
                FStar_SMTEncoding_Env.warn =
                  (uu___364_4282.FStar_SMTEncoding_Env.warn);
                FStar_SMTEncoding_Env.nolabels =
                  (uu___364_4282.FStar_SMTEncoding_Env.nolabels);
                FStar_SMTEncoding_Env.use_zfuel_name =
                  (uu___364_4282.FStar_SMTEncoding_Env.use_zfuel_name);
                FStar_SMTEncoding_Env.encode_non_total_function_typ =
                  (uu___364_4282.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                FStar_SMTEncoding_Env.current_module_name =
                  (uu___364_4282.FStar_SMTEncoding_Env.current_module_name);
                FStar_SMTEncoding_Env.encoding_quantifier = false;
                FStar_SMTEncoding_Env.global_cache =
                  (uu___364_4282.FStar_SMTEncoding_Env.global_cache);
                FStar_SMTEncoding_Env.local_cache =
                  (uu___364_4282.FStar_SMTEncoding_Env.local_cache)
              })
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____4285) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = FStar_SMTEncoding_Env.lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____4293 = head_redex env t  in
           if uu____4293
           then let uu____4300 = whnf env t  in encode_term uu____4300 env
           else
             (let uu____4303 =
                FStar_SMTEncoding_Env.lookup_free_var_name env
                  v1.FStar_Syntax_Syntax.fv_name
                 in
              match uu____4303 with
              | (uu____4314,arity) ->
                  let tok =
                    FStar_SMTEncoding_Env.lookup_free_var env
                      v1.FStar_Syntax_Syntax.fv_name
                     in
                  let tkey_hash = FStar_SMTEncoding_Term.hash_of_term tok  in
                  let uu____4323 =
                    FStar_SMTEncoding_Env.lookup_local_cache env tkey_hash
                     in
                  (match uu____4323 with
                   | FStar_Pervasives_Native.Some elt ->
                       let uu____4331 =
                         FStar_SMTEncoding_Env.use_cache_entry elt  in
                       (tok, uu____4331)
                   | FStar_Pervasives_Native.None  ->
                       let uu____4332 =
                         if arity > (Prims.parse_int "0")
                         then
                           match tok.FStar_SMTEncoding_Term.tm with
                           | FStar_SMTEncoding_Term.FreeV uu____4356 ->
                               let sym_name =
                                 let uu____4364 =
                                   FStar_Util.digest_of_string tkey_hash  in
                                 Prims.strcat "@kick_partial_app_" uu____4364
                                  in
                               let uu____4367 =
                                 let uu____4370 =
                                   let uu____4371 =
                                     let uu____4379 =
                                       FStar_SMTEncoding_Term.kick_partial_app
                                         tok
                                        in
                                     (uu____4379,
                                       (FStar_Pervasives_Native.Some
                                          "kick_partial_app"), sym_name)
                                      in
                                   FStar_SMTEncoding_Util.mkAssume uu____4371
                                    in
                                 [uu____4370]  in
                               (uu____4367, sym_name)
                           | FStar_SMTEncoding_Term.App (uu____4386,[]) ->
                               let sym_name =
                                 let uu____4391 =
                                   FStar_Util.digest_of_string tkey_hash  in
                                 Prims.strcat "@kick_partial_app_" uu____4391
                                  in
                               let uu____4394 =
                                 let uu____4397 =
                                   let uu____4398 =
                                     let uu____4406 =
                                       FStar_SMTEncoding_Term.kick_partial_app
                                         tok
                                        in
                                     (uu____4406,
                                       (FStar_Pervasives_Native.Some
                                          "kick_partial_app"), sym_name)
                                      in
                                   FStar_SMTEncoding_Util.mkAssume uu____4398
                                    in
                                 [uu____4397]  in
                               (uu____4394, sym_name)
                           | uu____4413 -> ([], "")
                         else ([], "")  in
                       (match uu____4332 with
                        | (aux_decls,sym_name) ->
                            let uu____4436 =
                              if aux_decls = []
                              then
                                FStar_All.pipe_right []
                                  FStar_SMTEncoding_Term.mk_decls_trivial
                              else
                                (let uu____4444 =
                                   FStar_SMTEncoding_Term.mk_decls sym_name
                                     tkey_hash aux_decls []
                                    in
                                 FStar_SMTEncoding_Env.add_to_local_cache env
                                   uu____4444)
                               in
                            (tok, uu____4436))))
       | FStar_Syntax_Syntax.Tm_type uu____4445 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4447) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.FStar_SMTEncoding_Env.current_module_name
              in
           let uu____4477 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____4477 with
            | (binders1,res) ->
                let uu____4488 =
                  (env.FStar_SMTEncoding_Env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____4488
                then
                  let uu____4495 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____4495 with
                   | (vars,guards,env',decls,uu____4520) ->
                       let fsym =
                         let uu____4539 =
                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                             "f"
                            in
                         (uu____4539, FStar_SMTEncoding_Term.Term_sort)  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____4545 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___365_4554 =
                              env.FStar_SMTEncoding_Env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___365_4554.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___365_4554.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___365_4554.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___365_4554.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___365_4554.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___365_4554.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___365_4554.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___365_4554.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___365_4554.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___365_4554.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___365_4554.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___365_4554.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___365_4554.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___365_4554.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___365_4554.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___365_4554.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___365_4554.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___365_4554.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___365_4554.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___365_4554.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___365_4554.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___365_4554.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___365_4554.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___365_4554.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___365_4554.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___365_4554.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___365_4554.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___365_4554.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___365_4554.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___365_4554.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___365_4554.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___365_4554.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___365_4554.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___365_4554.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___365_4554.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___365_4554.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___365_4554.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___365_4554.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___365_4554.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___365_4554.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___365_4554.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___365_4554.FStar_TypeChecker_Env.nbe)
                            }) res
                          in
                       (match uu____4545 with
                        | (pre_opt,res_t) ->
                            let uu____4566 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____4566 with
                             | (res_pred,decls') ->
                                 let uu____4577 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____4590 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____4590, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____4594 =
                                         encode_formula pre env'  in
                                       (match uu____4594 with
                                        | (guard,decls0) ->
                                            let uu____4607 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____4607, decls0))
                                    in
                                 (match uu____4577 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____4621 =
                                          let uu____4632 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____4632)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t.FStar_Syntax_Syntax.pos
                                          uu____4621
                                         in
                                      let cvars =
                                        let uu____4649 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____4649
                                          (FStar_List.filter
                                             (fun uu____4679  ->
                                                match uu____4679 with
                                                | (x,uu____4687) ->
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
                                      let uu____4706 =
                                        FStar_SMTEncoding_Env.lookup_local_cache
                                          env tkey_hash
                                         in
                                      (match uu____4706 with
                                       | FStar_Pervasives_Native.Some elt ->
                                           let uu____4714 =
                                             let uu____4715 =
                                               let uu____4723 =
                                                 FStar_All.pipe_right
                                                   elt.FStar_SMTEncoding_Term.sym_name
                                                   FStar_Util.must
                                                  in
                                               let uu____4730 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV)
                                                  in
                                               (uu____4723, uu____4730)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4715
                                              in
                                           let uu____4750 =
                                             let uu____4751 =
                                               let uu____4754 =
                                                 let uu____4757 =
                                                   FStar_SMTEncoding_Env.use_cache_entry
                                                     elt
                                                    in
                                                 FStar_List.append
                                                   guard_decls uu____4757
                                                  in
                                               FStar_List.append decls'
                                                 uu____4754
                                                in
                                             FStar_List.append decls
                                               uu____4751
                                              in
                                           (uu____4714, uu____4750)
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____4762 =
                                               FStar_Util.digest_of_string
                                                 tkey_hash
                                                in
                                             Prims.strcat "Tm_arrow_"
                                               uu____4762
                                              in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars
                                              in
                                           let caption =
                                             let uu____4775 =
                                               FStar_Options.log_queries ()
                                                in
                                             if uu____4775
                                             then
                                               let uu____4778 =
                                                 let uu____4780 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env.FStar_SMTEncoding_Env.tcenv
                                                     t0
                                                    in
                                                 FStar_Util.replace_char
                                                   uu____4780 10 32
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____4778
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
                                             let uu____4793 =
                                               let uu____4801 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars
                                                  in
                                               (tsym, uu____4801)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4793
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
                                             let uu____4817 =
                                               let uu____4825 =
                                                 FStar_SMTEncoding_Term.mkForall
                                                   t0.FStar_Syntax_Syntax.pos
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind)
                                                  in
                                               (uu____4825,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name)
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4817
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
                                             let uu____4842 =
                                               let uu____4850 =
                                                 let uu____4851 =
                                                   let uu____4862 =
                                                     let uu____4863 =
                                                       let uu____4868 =
                                                         let uu____4869 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f
                                                            in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____4869
                                                          in
                                                       (f_has_t, uu____4868)
                                                        in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____4863
                                                      in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____4862)
                                                    in
                                                 let uu____4884 =
                                                   mkForall_fuel
                                                     t0.FStar_Syntax_Syntax.pos
                                                    in
                                                 uu____4884 uu____4851  in
                                               (uu____4850,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4842
                                              in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym
                                                in
                                             let uu____4907 =
                                               let uu____4915 =
                                                 let uu____4916 =
                                                   let uu____4927 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp)
                                                      in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____4927)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   t0.FStar_Syntax_Syntax.pos
                                                   uu____4916
                                                  in
                                               (uu____4915,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4907
                                              in
                                           let t_decls1 =
                                             [tdecl;
                                             k_assumption;
                                             pre_typing;
                                             t_interp1]  in
                                           let uu____4947 =
                                             let uu____4948 =
                                               let uu____4951 =
                                                 let uu____4954 =
                                                   let uu____4957 =
                                                     FStar_SMTEncoding_Term.mk_decls
                                                       tsym tkey_hash
                                                       t_decls1
                                                       (FStar_List.append
                                                          decls
                                                          (FStar_List.append
                                                             decls'
                                                             guard_decls))
                                                      in
                                                   FStar_SMTEncoding_Env.add_to_local_cache
                                                     env uu____4957
                                                    in
                                                 FStar_List.append
                                                   guard_decls uu____4954
                                                  in
                                               FStar_List.append decls'
                                                 uu____4951
                                                in
                                             FStar_List.append decls
                                               uu____4948
                                              in
                                           (t1, uu____4947))))))
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
                     let uu____4976 =
                       let uu____4984 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____4984,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____4976  in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)  in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym  in
                     let uu____5003 =
                       let uu____5011 =
                         let uu____5012 =
                           let uu____5023 =
                             let uu____5024 =
                               let uu____5029 =
                                 let uu____5030 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____5030
                                  in
                               (f_has_t, uu____5029)  in
                             FStar_SMTEncoding_Util.mkImp uu____5024  in
                           ([[f_has_t]], [fsym], uu____5023)  in
                         let uu____5050 =
                           mkForall_fuel t0.FStar_Syntax_Syntax.pos  in
                         uu____5050 uu____5012  in
                       (uu____5011, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____5003  in
                   let uu____5068 =
                     FStar_All.pipe_right [tdecl; t_kinding; t_interp]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                      in
                   (t1, uu____5068)))
       | FStar_Syntax_Syntax.Tm_refine uu____5071 ->
           let uu____5078 =
             let uu____5083 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Env.Weak;
                 FStar_TypeChecker_Env.HNF;
                 FStar_TypeChecker_Env.EraseUniverses]
                 env.FStar_SMTEncoding_Env.tcenv t0
                in
             match uu____5083 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____5090;
                 FStar_Syntax_Syntax.vars = uu____5091;_} ->
                 let uu____5098 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____5098 with
                  | (b,f1) ->
                      let uu____5123 =
                        let uu____5124 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____5124  in
                      (uu____5123, f1))
             | uu____5139 -> failwith "impossible"  in
           (match uu____5078 with
            | (x,f) ->
                let uu____5151 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____5151 with
                 | (base_t,decls) ->
                     let uu____5162 =
                       FStar_SMTEncoding_Env.gen_term_var env x  in
                     (match uu____5162 with
                      | (x1,xtm,env') ->
                          let uu____5179 = encode_formula f env'  in
                          (match uu____5179 with
                           | (refinement,decls') ->
                               let uu____5190 =
                                 FStar_SMTEncoding_Env.fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____5190 with
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
                                      let uu____5215 =
                                        let uu____5223 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____5231 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____5223
                                          uu____5231
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____5215
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____5279  ->
                                              match uu____5279 with
                                              | (y,uu____5287) ->
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
                                    let uu____5325 =
                                      FStar_SMTEncoding_Env.lookup_local_cache
                                        env tkey_hash
                                       in
                                    (match uu____5325 with
                                     | FStar_Pervasives_Native.Some elt ->
                                         let uu____5333 =
                                           let uu____5334 =
                                             let uu____5342 =
                                               FStar_All.pipe_right
                                                 elt.FStar_SMTEncoding_Term.sym_name
                                                 FStar_Util.must
                                                in
                                             let uu____5349 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV)
                                                in
                                             (uu____5342, uu____5349)  in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____5334
                                            in
                                         let uu____5369 =
                                           let uu____5370 =
                                             let uu____5373 =
                                               FStar_SMTEncoding_Env.use_cache_entry
                                                 elt
                                                in
                                             FStar_List.append decls'
                                               uu____5373
                                              in
                                           FStar_List.append decls uu____5370
                                            in
                                         (uu____5333, uu____5369)
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.FStar_SMTEncoding_Env.current_module_name
                                            in
                                         let tsym =
                                           let uu____5380 =
                                             FStar_Util.digest_of_string
                                               tkey_hash
                                              in
                                           Prims.strcat "Tm_refine_"
                                             uu____5380
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
                                           let uu____5398 =
                                             let uu____5406 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1
                                                in
                                             (tsym, uu____5406)  in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____5398
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
                                           let uu____5423 =
                                             let uu____5431 =
                                               let uu____5432 =
                                                 let uu____5443 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base)
                                                    in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____5443)
                                                  in
                                               FStar_SMTEncoding_Term.mkForall
                                                 t0.FStar_Syntax_Syntax.pos
                                                 uu____5432
                                                in
                                             (uu____5431,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____5423
                                            in
                                         let t_kinding =
                                           let uu____5457 =
                                             let uu____5465 =
                                               FStar_SMTEncoding_Term.mkForall
                                                 t0.FStar_Syntax_Syntax.pos
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind)
                                                in
                                             (uu____5465,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____5457
                                            in
                                         let t_interp =
                                           let uu____5479 =
                                             let uu____5487 =
                                               let uu____5488 =
                                                 let uu____5499 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding)
                                                    in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____5499)
                                                  in
                                               FStar_SMTEncoding_Term.mkForall
                                                 t0.FStar_Syntax_Syntax.pos
                                                 uu____5488
                                                in
                                             (uu____5487,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement_interpretation"),
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____5479
                                            in
                                         let t_decls1 =
                                           [tdecl;
                                           t_kinding;
                                           t_interp;
                                           t_haseq1]  in
                                         let uu____5525 =
                                           let uu____5526 =
                                             let uu____5529 =
                                               let uu____5532 =
                                                 FStar_SMTEncoding_Term.mk_decls
                                                   tsym tkey_hash t_decls1
                                                   (FStar_List.append decls
                                                      decls')
                                                  in
                                               FStar_SMTEncoding_Env.add_to_local_cache
                                                 env uu____5532
                                                in
                                             FStar_List.append decls'
                                               uu____5529
                                              in
                                           FStar_List.append decls uu____5526
                                            in
                                         (t1, uu____5525)))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,uu____5534) ->
           let ttm =
             let uu____5552 =
               FStar_Syntax_Unionfind.uvar_id
                 uv.FStar_Syntax_Syntax.ctx_uvar_head
                in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____5552  in
           let uu____5554 =
             encode_term_pred FStar_Pervasives_Native.None
               uv.FStar_Syntax_Syntax.ctx_uvar_typ env ttm
              in
           (match uu____5554 with
            | (t_has_k,decls) ->
                let d =
                  let uu____5566 =
                    let uu____5574 =
                      let uu____5576 =
                        let uu____5578 =
                          let uu____5580 =
                            FStar_Syntax_Unionfind.uvar_id
                              uv.FStar_Syntax_Syntax.ctx_uvar_head
                             in
                          FStar_Util.string_of_int uu____5580  in
                        FStar_Util.format1 "uvar_typing_%s" uu____5578  in
                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                        uu____5576
                       in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____5574)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____5566  in
                let uu____5586 =
                  let uu____5587 =
                    FStar_All.pipe_right [d]
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  FStar_List.append decls uu____5587  in
                (ttm, uu____5586))
       | FStar_Syntax_Syntax.Tm_app uu____5594 ->
           let uu____5611 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____5611 with
            | (head1,args_e) ->
                let uu____5658 =
                  let uu____5673 =
                    let uu____5674 = FStar_Syntax_Subst.compress head1  in
                    uu____5674.FStar_Syntax_Syntax.n  in
                  (uu____5673, args_e)  in
                (match uu____5658 with
                 | uu____5691 when head_redex env head1 ->
                     let uu____5706 = whnf env t  in
                     encode_term uu____5706 env
                 | uu____5707 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____5730 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5748) when
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
                       FStar_Syntax_Syntax.pos = uu____5770;
                       FStar_Syntax_Syntax.vars = uu____5771;_},uu____5772),uu____5773)
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
                       FStar_Syntax_Syntax.pos = uu____5799;
                       FStar_Syntax_Syntax.vars = uu____5800;_},uu____5801),
                    (v0,uu____5803)::(v1,uu____5805)::(v2,uu____5807)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____5878 = encode_term v0 env  in
                     (match uu____5878 with
                      | (v01,decls0) ->
                          let uu____5889 = encode_term v1 env  in
                          (match uu____5889 with
                           | (v11,decls1) ->
                               let uu____5900 = encode_term v2 env  in
                               (match uu____5900 with
                                | (v21,decls2) ->
                                    let uu____5911 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____5911,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(v0,uu____5914)::(v1,uu____5916)::(v2,uu____5918)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____5985 = encode_term v0 env  in
                     (match uu____5985 with
                      | (v01,decls0) ->
                          let uu____5996 = encode_term v1 env  in
                          (match uu____5996 with
                           | (v11,decls1) ->
                               let uu____6007 = encode_term v2 env  in
                               (match uu____6007 with
                                | (v21,decls2) ->
                                    let uu____6018 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____6018,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____6020)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____6056)::(rng,uu____6058)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____6109) ->
                     let e0 =
                       let uu____6131 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg
                         env.FStar_SMTEncoding_Env.tcenv head1 uu____6131
                        in
                     ((let uu____6141 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug
                              env.FStar_SMTEncoding_Env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____6141
                       then
                         let uu____6146 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____6146
                       else ());
                      (let e =
                         let uu____6154 =
                           let uu____6159 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____6160 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____6159
                             uu____6160
                            in
                         uu____6154 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____6171),(arg,uu____6173)::[]) -> encode_term arg env
                 | uu____6208 ->
                     let uu____6223 = encode_args args_e env  in
                     (match uu____6223 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____6284 = encode_term head1 env  in
                            match uu____6284 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____6356 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____6356 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____6454  ->
                                                 fun uu____6455  ->
                                                   match (uu____6454,
                                                           uu____6455)
                                                   with
                                                   | ((bv,uu____6485),
                                                      (a,uu____6487)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____6517 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____6517
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____6518 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm
                                             in
                                          (match uu____6518 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type
                                                  in
                                               let tkey_hash =
                                                 FStar_SMTEncoding_Term.hash_of_term
                                                   app_tm
                                                  in
                                               let uu____6534 =
                                                 FStar_SMTEncoding_Env.lookup_local_cache
                                                   env tkey_hash
                                                  in
                                               (match uu____6534 with
                                                | FStar_Pervasives_Native.Some
                                                    elt ->
                                                    let uu____6544 =
                                                      let uu____6547 =
                                                        let uu____6550 =
                                                          let uu____6553 =
                                                            FStar_SMTEncoding_Env.use_cache_entry
                                                              elt
                                                             in
                                                          FStar_List.append
                                                            decls''
                                                            uu____6553
                                                           in
                                                        FStar_List.append
                                                          decls' uu____6550
                                                         in
                                                      FStar_List.append decls
                                                        uu____6547
                                                       in
                                                    (app_tm, uu____6544)
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    let e_typing =
                                                      let uu____6559 =
                                                        let uu____6567 =
                                                          FStar_SMTEncoding_Term.mkForall
                                                            t0.FStar_Syntax_Syntax.pos
                                                            ([[has_type]],
                                                              cvars,
                                                              has_type)
                                                           in
                                                        let uu____6576 =
                                                          let uu____6578 =
                                                            let uu____6580 =
                                                              FStar_SMTEncoding_Term.hash_of_term
                                                                app_tm
                                                               in
                                                            FStar_Util.digest_of_string
                                                              uu____6580
                                                             in
                                                          Prims.strcat
                                                            "partial_app_typing_"
                                                            uu____6578
                                                           in
                                                        (uu____6567,
                                                          (FStar_Pervasives_Native.Some
                                                             "Partial app typing"),
                                                          uu____6576)
                                                         in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____6559
                                                       in
                                                    let uu____6586 =
                                                      let uu____6589 =
                                                        let uu____6592 =
                                                          let uu____6595 =
                                                            let uu____6598 =
                                                              FStar_SMTEncoding_Term.mk_decls
                                                                "" tkey_hash
                                                                [e_typing]
                                                                (FStar_List.append
                                                                   decls
                                                                   (FStar_List.append
                                                                    decls'
                                                                    decls''))
                                                               in
                                                            FStar_SMTEncoding_Env.add_to_local_cache
                                                              env uu____6598
                                                             in
                                                          FStar_List.append
                                                            decls''
                                                            uu____6595
                                                           in
                                                        FStar_List.append
                                                          decls' uu____6592
                                                         in
                                                      FStar_List.append decls
                                                        uu____6589
                                                       in
                                                    (app_tm, uu____6586)))))
                             in
                          let encode_full_app fv =
                            let uu____6616 =
                              FStar_SMTEncoding_Env.lookup_free_var_sym env
                                fv
                               in
                            match uu____6616 with
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
                                   FStar_Syntax_Syntax.pos = uu____6647;
                                   FStar_Syntax_Syntax.vars = uu____6648;_},uu____6649)
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
                                   FStar_Syntax_Syntax.pos = uu____6656;
                                   FStar_Syntax_Syntax.vars = uu____6657;_},uu____6658)
                                ->
                                let uu____6663 =
                                  let uu____6664 =
                                    let uu____6669 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____6669
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____6664
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____6663
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____6699 =
                                  let uu____6700 =
                                    let uu____6705 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____6705
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____6700
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____6699
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____6734,(FStar_Util.Inl t1,uu____6736),uu____6737)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____6784,(FStar_Util.Inr c,uu____6786),uu____6787)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____6834 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____6855 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Env.Weak;
                                     FStar_TypeChecker_Env.HNF;
                                     FStar_TypeChecker_Env.EraseUniverses]
                                     env.FStar_SMTEncoding_Env.tcenv
                                     head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____6855
                                  in
                               let uu____6856 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____6856 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____6872;
                                            FStar_Syntax_Syntax.vars =
                                              uu____6873;_},uu____6874)
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
                                     | uu____6892 ->
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
           let uu____6971 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____6971 with
            | (bs1,body1,opening) ->
                let fallback uu____6994 =
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
                  let uu____7004 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort)
                     in
                  let uu____7006 =
                    FStar_All.pipe_right [decl]
                      FStar_SMTEncoding_Term.mk_decls_trivial
                     in
                  (uu____7004, uu____7006)  in
                let is_impure rc =
                  let uu____7016 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                      env.FStar_SMTEncoding_Env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____7016 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____7031 =
                          let uu____7044 =
                            FStar_TypeChecker_Env.get_range
                              env.FStar_SMTEncoding_Env.tcenv
                             in
                          FStar_TypeChecker_Util.new_implicit_var
                            "SMTEncoding codomain" uu____7044
                            env.FStar_SMTEncoding_Env.tcenv
                            FStar_Syntax_Util.ktype0
                           in
                        (match uu____7031 with
                         | (t1,uu____7047,uu____7048) -> t1)
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  let uu____7066 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                     in
                  if uu____7066
                  then
                    let uu____7071 = FStar_Syntax_Syntax.mk_Total res_typ  in
                    FStar_Pervasives_Native.Some uu____7071
                  else
                    (let uu____7074 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid
                        in
                     if uu____7074
                     then
                       let uu____7079 = FStar_Syntax_Syntax.mk_GTotal res_typ
                          in
                       FStar_Pervasives_Native.Some uu____7079
                     else FStar_Pervasives_Native.None)
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____7087 =
                         let uu____7093 =
                           let uu____7095 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____7095
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____7093)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____7087);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____7100 =
                       (is_impure rc) &&
                         (let uu____7103 =
                            FStar_TypeChecker_Env.is_reifiable_rc
                              env.FStar_SMTEncoding_Env.tcenv rc
                             in
                          Prims.op_Negation uu____7103)
                        in
                     if uu____7100
                     then fallback ()
                     else
                       (let uu____7112 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____7112 with
                        | (vars,guards,envbody,decls,uu____7137) ->
                            let body2 =
                              let uu____7151 =
                                FStar_TypeChecker_Env.is_reifiable_rc
                                  env.FStar_SMTEncoding_Env.tcenv rc
                                 in
                              if uu____7151
                              then
                                FStar_TypeChecker_Util.reify_body
                                  env.FStar_SMTEncoding_Env.tcenv body1
                              else body1  in
                            let uu____7156 = encode_term body2 envbody  in
                            (match uu____7156 with
                             | (body3,decls') ->
                                 let uu____7167 =
                                   let uu____7176 = codomain_eff rc  in
                                   match uu____7176 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____7195 = encode_term tfun env
                                          in
                                       (match uu____7195 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____7167 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____7229 =
                                          let uu____7240 =
                                            let uu____7241 =
                                              let uu____7246 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____7246, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____7241
                                             in
                                          ([], vars, uu____7240)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t0.FStar_Syntax_Syntax.pos
                                          uu____7229
                                         in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body
                                         in
                                      let uu____7254 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            (cvars, key_body)
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____7285 =
                                              let uu____7293 =
                                                let uu____7301 =
                                                  FStar_SMTEncoding_Term.free_variables
                                                    t1
                                                   in
                                                FStar_List.append uu____7301
                                                  cvars
                                                 in
                                              FStar_Util.remove_dups
                                                FStar_SMTEncoding_Term.fv_eq
                                                uu____7293
                                               in
                                            let uu____7319 =
                                              FStar_SMTEncoding_Util.mkAnd
                                                (key_body, t1)
                                               in
                                            (uu____7285, uu____7319)
                                         in
                                      (match uu____7254 with
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
                                           let uu____7356 =
                                             FStar_SMTEncoding_Env.lookup_local_cache
                                               env tkey_hash
                                              in
                                           (match uu____7356 with
                                            | FStar_Pervasives_Native.Some
                                                elt ->
                                                let uu____7364 =
                                                  let uu____7365 =
                                                    let uu____7373 =
                                                      FStar_All.pipe_right
                                                        elt.FStar_SMTEncoding_Term.sym_name
                                                        FStar_Util.must
                                                       in
                                                    let uu____7380 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    (uu____7373, uu____7380)
                                                     in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____7365
                                                   in
                                                let uu____7391 =
                                                  let uu____7392 =
                                                    let uu____7395 =
                                                      let uu____7398 =
                                                        FStar_SMTEncoding_Env.use_cache_entry
                                                          elt
                                                         in
                                                      FStar_List.append
                                                        decls'' uu____7398
                                                       in
                                                    FStar_List.append decls'
                                                      uu____7395
                                                     in
                                                  FStar_List.append decls
                                                    uu____7392
                                                   in
                                                (uu____7364, uu____7391)
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                let uu____7401 =
                                                  is_an_eta_expansion env
                                                    vars body3
                                                   in
                                                (match uu____7401 with
                                                 | FStar_Pervasives_Native.Some
                                                     t1 ->
                                                     let decls1 =
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
                                                       let uu____7423 =
                                                         FStar_Util.digest_of_string
                                                           tkey_hash
                                                          in
                                                       Prims.strcat "Tm_abs_"
                                                         uu____7423
                                                        in
                                                     let fdecl =
                                                       FStar_SMTEncoding_Term.DeclFun
                                                         (fsym, cvar_sorts,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           FStar_Pervasives_Native.None)
                                                        in
                                                     let f =
                                                       let uu____7432 =
                                                         let uu____7440 =
                                                           FStar_List.map
                                                             FStar_SMTEncoding_Util.mkFreeV
                                                             cvars1
                                                            in
                                                         (fsym, uu____7440)
                                                          in
                                                       FStar_SMTEncoding_Util.mkApp
                                                         uu____7432
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
                                                           let uu____7462 =
                                                             let uu____7463 =
                                                               let uu____7471
                                                                 =
                                                                 FStar_SMTEncoding_Term.mkForall
                                                                   t0.FStar_Syntax_Syntax.pos
                                                                   ([[f]],
                                                                    cvars1,
                                                                    f_has_t)
                                                                  in
                                                               (uu____7471,
                                                                 (FStar_Pervasives_Native.Some
                                                                    a_name),
                                                                 a_name)
                                                                in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____7463
                                                              in
                                                           [uu____7462]
                                                        in
                                                     let interp_f =
                                                       let a_name =
                                                         Prims.strcat
                                                           "interpretation_"
                                                           fsym
                                                          in
                                                       let uu____7486 =
                                                         let uu____7494 =
                                                           let uu____7495 =
                                                             let uu____7506 =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (app, body3)
                                                                in
                                                             ([[app]],
                                                               (FStar_List.append
                                                                  vars cvars1),
                                                               uu____7506)
                                                              in
                                                           FStar_SMTEncoding_Term.mkForall
                                                             t0.FStar_Syntax_Syntax.pos
                                                             uu____7495
                                                            in
                                                         (uu____7494,
                                                           (FStar_Pervasives_Native.Some
                                                              a_name),
                                                           a_name)
                                                          in
                                                       FStar_SMTEncoding_Util.mkAssume
                                                         uu____7486
                                                        in
                                                     let f_decls =
                                                       FStar_List.append
                                                         (fdecl :: typing_f)
                                                         [interp_f]
                                                        in
                                                     let uu____7520 =
                                                       let uu____7521 =
                                                         let uu____7524 =
                                                           let uu____7527 =
                                                             let uu____7530 =
                                                               FStar_SMTEncoding_Term.mk_decls
                                                                 fsym
                                                                 tkey_hash
                                                                 f_decls
                                                                 (FStar_List.append
                                                                    decls
                                                                    (
                                                                    FStar_List.append
                                                                    decls'
                                                                    decls''))
                                                                in
                                                             FStar_SMTEncoding_Env.add_to_local_cache
                                                               env uu____7530
                                                              in
                                                           FStar_List.append
                                                             decls''
                                                             uu____7527
                                                            in
                                                         FStar_List.append
                                                           decls' uu____7524
                                                          in
                                                       FStar_List.append
                                                         decls uu____7521
                                                        in
                                                     (f, uu____7520)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____7531,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____7532;
                          FStar_Syntax_Syntax.lbunivs = uu____7533;
                          FStar_Syntax_Syntax.lbtyp = uu____7534;
                          FStar_Syntax_Syntax.lbeff = uu____7535;
                          FStar_Syntax_Syntax.lbdef = uu____7536;
                          FStar_Syntax_Syntax.lbattrs = uu____7537;
                          FStar_Syntax_Syntax.lbpos = uu____7538;_}::uu____7539),uu____7540)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____7574;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____7576;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____7578;
                FStar_Syntax_Syntax.lbpos = uu____7579;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____7606 ->
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
              let uu____7678 =
                let uu____7683 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____7683 env  in
              match uu____7678 with
              | (ee1,decls1) ->
                  let uu____7708 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____7708 with
                   | (xs,e21) ->
                       let uu____7733 = FStar_List.hd xs  in
                       (match uu____7733 with
                        | (x1,uu____7751) ->
                            let env' =
                              FStar_SMTEncoding_Env.push_term_var env x1 ee1
                               in
                            let uu____7757 = encode_body e21 env'  in
                            (match uu____7757 with
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
            let uu____7787 =
              let uu____7795 =
                let uu____7796 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____7796  in
              FStar_SMTEncoding_Env.gen_term_var env uu____7795  in
            match uu____7787 with
            | (scrsym,scr',env1) ->
                let uu____7806 = encode_term e env1  in
                (match uu____7806 with
                 | (scr,decls) ->
                     let uu____7817 =
                       let encode_branch b uu____7846 =
                         match uu____7846 with
                         | (else_case,decls1) ->
                             let uu____7865 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____7865 with
                              | (p,w,br) ->
                                  let uu____7891 = encode_pat env1 p  in
                                  (match uu____7891 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____7928  ->
                                                   match uu____7928 with
                                                   | (x,t) ->
                                                       FStar_SMTEncoding_Env.push_term_var
                                                         env2 x t) env1)
                                          in
                                       let uu____7935 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____7957 =
                                               encode_term w1 env2  in
                                             (match uu____7957 with
                                              | (w2,decls2) ->
                                                  let uu____7970 =
                                                    let uu____7971 =
                                                      let uu____7976 =
                                                        let uu____7977 =
                                                          let uu____7982 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____7982)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____7977
                                                         in
                                                      (guard, uu____7976)  in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____7971
                                                     in
                                                  (uu____7970, decls2))
                                          in
                                       (match uu____7935 with
                                        | (guard1,decls2) ->
                                            let uu____7997 =
                                              encode_br br env2  in
                                            (match uu____7997 with
                                             | (br1,decls3) ->
                                                 let uu____8010 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____8010,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____7817 with
                      | (match_tm,decls1) ->
                          let uu____8031 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange
                             in
                          (uu____8031, decls1)))

and (encode_pat :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.pat -> (FStar_SMTEncoding_Env.env_t * pattern))
  =
  fun env  ->
    fun pat  ->
      (let uu____8054 =
         FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
           FStar_Options.Medium
          in
       if uu____8054
       then
         let uu____8057 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____8057
       else ());
      (let uu____8062 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____8062 with
       | (vars,pat_term) ->
           let uu____8079 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____8135  ->
                     fun v1  ->
                       match uu____8135 with
                       | (env1,vars1) ->
                           let uu____8191 =
                             FStar_SMTEncoding_Env.gen_term_var env1 v1  in
                           (match uu____8191 with
                            | (xx,uu____8215,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, []))
              in
           (match uu____8079 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____8308 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____8309 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____8310 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____8318 = encode_const c env1  in
                      (match uu____8318 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____8326::uu____8327 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____8331 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon
                            env1.FStar_SMTEncoding_Env.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____8354 =
                          FStar_TypeChecker_Env.datacons_of_typ
                            env1.FStar_SMTEncoding_Env.tcenv tc_name
                           in
                        match uu____8354 with
                        | (uu____8362,uu____8363::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____8368 ->
                            FStar_SMTEncoding_Env.mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____8404  ->
                                  match uu____8404 with
                                  | (arg,uu____8414) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____8423 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____8423))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____8455) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____8486 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____8511 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____8557  ->
                                  match uu____8557 with
                                  | (arg,uu____8573) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____8582 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____8582))
                         in
                      FStar_All.pipe_right uu____8511 FStar_List.flatten
                   in
                let pat_term1 uu____8613 = encode_term pat_term env1  in
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
      let uu____8623 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____8671  ->
                fun uu____8672  ->
                  match (uu____8671, uu____8672) with
                  | ((tms,decls),(t,uu____8712)) ->
                      let uu____8739 = encode_term t env  in
                      (match uu____8739 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____8623 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____8796 = FStar_Syntax_Util.list_elements e  in
        match uu____8796 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____8827 =
          let uu____8844 = FStar_Syntax_Util.unmeta p  in
          FStar_All.pipe_right uu____8844 FStar_Syntax_Util.head_and_args  in
        match uu____8827 with
        | (head1,args) ->
            let uu____8895 =
              let uu____8910 =
                let uu____8911 = FStar_Syntax_Util.un_uinst head1  in
                uu____8911.FStar_Syntax_Syntax.n  in
              (uu____8910, args)  in
            (match uu____8895 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____8933,uu____8934)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____8986 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or1 t1 =
          let uu____9041 =
            let uu____9058 = FStar_Syntax_Util.unmeta t1  in
            FStar_All.pipe_right uu____9058 FStar_Syntax_Util.head_and_args
             in
          match uu____9041 with
          | (head1,args) ->
              let uu____9105 =
                let uu____9120 =
                  let uu____9121 = FStar_Syntax_Util.un_uinst head1  in
                  uu____9121.FStar_Syntax_Syntax.n  in
                (uu____9120, args)  in
              (match uu____9105 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____9140)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____9177 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____9207 = smt_pat_or1 t1  in
            (match uu____9207 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____9229 = list_elements1 e  in
                 FStar_All.pipe_right uu____9229
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____9259 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____9259
                           (FStar_List.map one_pat)))
             | uu____9282 ->
                 let uu____9287 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____9287])
        | uu____9338 ->
            let uu____9341 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____9341]
         in
      let uu____9392 =
        let uu____9407 =
          let uu____9408 = FStar_Syntax_Subst.compress t  in
          uu____9408.FStar_Syntax_Syntax.n  in
        match uu____9407 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____9447 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____9447 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____9482;
                        FStar_Syntax_Syntax.effect_name = uu____9483;
                        FStar_Syntax_Syntax.result_typ = uu____9484;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____9486)::(post,uu____9488)::(pats,uu____9490)::[];
                        FStar_Syntax_Syntax.flags = uu____9491;_}
                      ->
                      let uu____9552 = lemma_pats pats  in
                      (binders1, pre, post, uu____9552)
                  | uu____9563 -> failwith "impos"))
        | uu____9579 -> failwith "Impos"  in
      match uu____9392 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___366_9616 = env  in
            {
              FStar_SMTEncoding_Env.bvar_bindings =
                (uu___366_9616.FStar_SMTEncoding_Env.bvar_bindings);
              FStar_SMTEncoding_Env.fvar_bindings =
                (uu___366_9616.FStar_SMTEncoding_Env.fvar_bindings);
              FStar_SMTEncoding_Env.depth =
                (uu___366_9616.FStar_SMTEncoding_Env.depth);
              FStar_SMTEncoding_Env.tcenv =
                (uu___366_9616.FStar_SMTEncoding_Env.tcenv);
              FStar_SMTEncoding_Env.warn =
                (uu___366_9616.FStar_SMTEncoding_Env.warn);
              FStar_SMTEncoding_Env.nolabels =
                (uu___366_9616.FStar_SMTEncoding_Env.nolabels);
              FStar_SMTEncoding_Env.use_zfuel_name = true;
              FStar_SMTEncoding_Env.encode_non_total_function_typ =
                (uu___366_9616.FStar_SMTEncoding_Env.encode_non_total_function_typ);
              FStar_SMTEncoding_Env.current_module_name =
                (uu___366_9616.FStar_SMTEncoding_Env.current_module_name);
              FStar_SMTEncoding_Env.encoding_quantifier =
                (uu___366_9616.FStar_SMTEncoding_Env.encoding_quantifier);
              FStar_SMTEncoding_Env.global_cache =
                (uu___366_9616.FStar_SMTEncoding_Env.global_cache);
              FStar_SMTEncoding_Env.local_cache =
                (uu___366_9616.FStar_SMTEncoding_Env.local_cache)
            }  in
          let uu____9618 =
            encode_binders FStar_Pervasives_Native.None binders env1  in
          (match uu____9618 with
           | (vars,guards,env2,decls,uu____9643) ->
               let uu____9656 = encode_smt_patterns patterns env2  in
               (match uu____9656 with
                | (pats,decls') ->
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
                    let env3 =
                      let uu___367_9683 = env2  in
                      {
                        FStar_SMTEncoding_Env.bvar_bindings =
                          (uu___367_9683.FStar_SMTEncoding_Env.bvar_bindings);
                        FStar_SMTEncoding_Env.fvar_bindings =
                          (uu___367_9683.FStar_SMTEncoding_Env.fvar_bindings);
                        FStar_SMTEncoding_Env.depth =
                          (uu___367_9683.FStar_SMTEncoding_Env.depth);
                        FStar_SMTEncoding_Env.tcenv =
                          (uu___367_9683.FStar_SMTEncoding_Env.tcenv);
                        FStar_SMTEncoding_Env.warn =
                          (uu___367_9683.FStar_SMTEncoding_Env.warn);
                        FStar_SMTEncoding_Env.nolabels = true;
                        FStar_SMTEncoding_Env.use_zfuel_name =
                          (uu___367_9683.FStar_SMTEncoding_Env.use_zfuel_name);
                        FStar_SMTEncoding_Env.encode_non_total_function_typ =
                          (uu___367_9683.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                        FStar_SMTEncoding_Env.current_module_name =
                          (uu___367_9683.FStar_SMTEncoding_Env.current_module_name);
                        FStar_SMTEncoding_Env.encoding_quantifier =
                          (uu___367_9683.FStar_SMTEncoding_Env.encoding_quantifier);
                        FStar_SMTEncoding_Env.global_cache =
                          (uu___367_9683.FStar_SMTEncoding_Env.global_cache);
                        FStar_SMTEncoding_Env.local_cache =
                          (uu___367_9683.FStar_SMTEncoding_Env.local_cache)
                      }  in
                    let uu____9685 =
                      let uu____9690 = FStar_Syntax_Util.unmeta pre  in
                      encode_formula uu____9690 env3  in
                    (match uu____9685 with
                     | (pre1,decls'') ->
                         let uu____9697 =
                           let uu____9702 = FStar_Syntax_Util.unmeta post1
                              in
                           encode_formula uu____9702 env3  in
                         (match uu____9697 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append decls'
                                     (FStar_List.append decls'' decls'''))
                                 in
                              let uu____9712 =
                                let uu____9713 =
                                  let uu____9724 =
                                    let uu____9725 =
                                      let uu____9730 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards)
                                         in
                                      (uu____9730, post2)  in
                                    FStar_SMTEncoding_Util.mkImp uu____9725
                                     in
                                  (pats, vars, uu____9724)  in
                                FStar_SMTEncoding_Term.mkForall
                                  t.FStar_Syntax_Syntax.pos uu____9713
                                 in
                              (uu____9712, decls1)))))

and (encode_smt_patterns :
  FStar_Syntax_Syntax.arg Prims.list Prims.list ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term Prims.list Prims.list *
        FStar_SMTEncoding_Term.decls_t))
  =
  fun pats_l  ->
    fun env  ->
      let env1 =
        let uu___368_9750 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___368_9750.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___368_9750.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___368_9750.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___368_9750.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___368_9750.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.nolabels =
            (uu___368_9750.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___368_9750.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___368_9750.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___368_9750.FStar_SMTEncoding_Env.encoding_quantifier);
          FStar_SMTEncoding_Env.global_cache =
            (uu___368_9750.FStar_SMTEncoding_Env.global_cache);
          FStar_SMTEncoding_Env.local_cache =
            (uu___368_9750.FStar_SMTEncoding_Env.local_cache)
        }  in
      let encode_smt_pattern t =
        let uu____9766 = FStar_Syntax_Util.head_and_args t  in
        match uu____9766 with
        | (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____9829::(x,uu____9831)::(t1,uu____9833)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____9900 = encode_term x env1  in
                 (match uu____9900 with
                  | (x1,decls) ->
                      let uu____9911 = encode_term t1 env1  in
                      (match uu____9911 with
                       | (t2,decls') ->
                           let uu____9922 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                           (uu____9922, (FStar_List.append decls decls'))))
             | uu____9923 -> encode_term t env1)
         in
      FStar_List.fold_right
        (fun pats  ->
           fun uu____9966  ->
             match uu____9966 with
             | (pats_l1,decls) ->
                 let uu____10011 =
                   FStar_List.fold_right
                     (fun uu____10046  ->
                        fun uu____10047  ->
                          match (uu____10046, uu____10047) with
                          | ((p,uu____10089),(pats1,decls1)) ->
                              let uu____10124 = encode_smt_pattern p  in
                              (match uu____10124 with
                               | (t,d) ->
                                   let uu____10139 =
                                     FStar_SMTEncoding_Term.check_pattern_ok
                                       t
                                      in
                                   (match uu____10139 with
                                    | FStar_Pervasives_Native.None  ->
                                        ((t :: pats1),
                                          (FStar_List.append d decls1))
                                    | FStar_Pervasives_Native.Some
                                        illegal_subterm ->
                                        ((let uu____10156 =
                                            let uu____10162 =
                                              let uu____10164 =
                                                FStar_Syntax_Print.term_to_string
                                                  p
                                                 in
                                              let uu____10166 =
                                                FStar_SMTEncoding_Term.print_smt_term
                                                  illegal_subterm
                                                 in
                                              FStar_Util.format2
                                                "Pattern %s contains illegal sub-term (%s); dropping it"
                                                uu____10164 uu____10166
                                               in
                                            (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                                              uu____10162)
                                             in
                                          FStar_Errors.log_issue
                                            p.FStar_Syntax_Syntax.pos
                                            uu____10156);
                                         (pats1,
                                           (FStar_List.append d decls1))))))
                     pats ([], decls)
                    in
                 (match uu____10011 with
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
        let uu____10226 =
          FStar_All.pipe_left
            (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____10226
        then
          let uu____10231 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____10233 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10231 uu____10233
        else ()  in
      let enc f r l =
        let uu____10275 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10307 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____10307 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____10275 with
        | (decls,args) ->
            let uu____10338 =
              let uu___369_10339 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___369_10339.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___369_10339.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10338, decls)
         in
      let const_op f r uu____10374 =
        let uu____10387 = f r  in (uu____10387, [])  in
      let un_op f l =
        let uu____10410 = FStar_List.hd l  in
        FStar_All.pipe_left f uu____10410  in
      let bin_op f uu___360_10430 =
        match uu___360_10430 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10441 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____10482 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____10507  ->
                 match uu____10507 with
                 | (t,uu____10523) ->
                     let uu____10528 = encode_formula t env  in
                     (match uu____10528 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____10482 with
        | (decls,phis) ->
            let uu____10557 =
              let uu___370_10558 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___370_10558.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___370_10558.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10557, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____10621  ->
               match uu____10621 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____10642) -> false
                    | uu____10645 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____10664 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____10664
        else
          (let uu____10681 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____10681 r rf)
         in
      let eq3_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____10753 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::t1::v0::v1::[] ->
                     let uu____10785 =
                       let uu____10790 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____10791 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____10790, uu____10791)  in
                     FStar_SMTEncoding_Util.mkAnd uu____10785
                 | uu____10792 -> failwith "Impossible")
             in
          uu____10753 r args
        else
          (let uu____10798 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____10798)
         in
      let h_equals_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____10870 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::v0::t1::v1::[] ->
                     let uu____10902 =
                       let uu____10907 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____10908 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____10907, uu____10908)  in
                     FStar_SMTEncoding_Util.mkAnd uu____10902
                 | uu____10909 -> failwith "Impossible")
             in
          uu____10870 r args
        else
          (let uu____10915 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____10915)
         in
      let mk_imp1 r uu___361_10950 =
        match uu___361_10950 with
        | (lhs,uu____10956)::(rhs,uu____10958)::[] ->
            let uu____10999 = encode_formula rhs env  in
            (match uu____10999 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11014) ->
                      (l1, decls1)
                  | uu____11019 ->
                      let uu____11020 = encode_formula lhs env  in
                      (match uu____11020 with
                       | (l2,decls2) ->
                           let uu____11031 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____11031, (FStar_List.append decls1 decls2)))))
        | uu____11032 -> failwith "impossible"  in
      let mk_ite r uu___362_11060 =
        match uu___362_11060 with
        | (guard,uu____11066)::(_then,uu____11068)::(_else,uu____11070)::[]
            ->
            let uu____11127 = encode_formula guard env  in
            (match uu____11127 with
             | (g,decls1) ->
                 let uu____11138 = encode_formula _then env  in
                 (match uu____11138 with
                  | (t,decls2) ->
                      let uu____11149 = encode_formula _else env  in
                      (match uu____11149 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11161 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____11191 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l
           in
        f uu____11191  in
      let connectives =
        let uu____11221 =
          let uu____11246 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____11246)  in
        let uu____11289 =
          let uu____11316 =
            let uu____11341 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____11341)  in
          let uu____11384 =
            let uu____11411 =
              let uu____11438 =
                let uu____11463 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____11463)  in
              let uu____11506 =
                let uu____11533 =
                  let uu____11560 =
                    let uu____11585 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____11585)  in
                  [uu____11560;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.c_eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq3_op);
                  (FStar_Parser_Const.c_eq3_lid, h_equals_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11533  in
              uu____11438 :: uu____11506  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11411  in
          uu____11316 :: uu____11384  in
        uu____11221 :: uu____11289  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____12130 = encode_formula phi' env  in
            (match uu____12130 with
             | (phi2,decls) ->
                 let uu____12141 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____12141, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____12143 ->
            let uu____12150 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____12150 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____12189 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____12189 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____12201;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____12203;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____12205;
                 FStar_Syntax_Syntax.lbpos = uu____12206;_}::[]),e2)
            ->
            let uu____12233 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____12233 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____12286::(x,uu____12288)::(t,uu____12290)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12357 = encode_term x env  in
                 (match uu____12357 with
                  | (x1,decls) ->
                      let uu____12368 = encode_term t env  in
                      (match uu____12368 with
                       | (t1,decls') ->
                           let uu____12379 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____12379, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12382)::(msg,uu____12384)::(phi2,uu____12386)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12453 =
                   let uu____12458 =
                     let uu____12459 = FStar_Syntax_Subst.compress r  in
                     uu____12459.FStar_Syntax_Syntax.n  in
                   let uu____12462 =
                     let uu____12463 = FStar_Syntax_Subst.compress msg  in
                     uu____12463.FStar_Syntax_Syntax.n  in
                   (uu____12458, uu____12462)  in
                 (match uu____12453 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12472))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____12483 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____12490)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____12525 when head_redex env head2 ->
                 let uu____12540 = whnf env phi1  in
                 encode_formula uu____12540 env
             | uu____12541 ->
                 let uu____12556 = encode_term phi1 env  in
                 (match uu____12556 with
                  | (tt,decls) ->
                      let tt1 =
                        let uu____12568 =
                          let uu____12570 =
                            FStar_Range.use_range
                              tt.FStar_SMTEncoding_Term.rng
                             in
                          let uu____12571 =
                            FStar_Range.use_range
                              phi1.FStar_Syntax_Syntax.pos
                             in
                          FStar_Range.rng_included uu____12570 uu____12571
                           in
                        if uu____12568
                        then tt
                        else
                          (let uu___371_12575 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___371_12575.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___371_12575.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      let uu____12576 = FStar_SMTEncoding_Term.mk_Valid tt1
                         in
                      (uu____12576, decls)))
        | uu____12577 ->
            let uu____12578 = encode_term phi1 env  in
            (match uu____12578 with
             | (tt,decls) ->
                 let tt1 =
                   let uu____12590 =
                     let uu____12592 =
                       FStar_Range.use_range tt.FStar_SMTEncoding_Term.rng
                        in
                     let uu____12593 =
                       FStar_Range.use_range phi1.FStar_Syntax_Syntax.pos  in
                     FStar_Range.rng_included uu____12592 uu____12593  in
                   if uu____12590
                   then tt
                   else
                     (let uu___372_12597 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___372_12597.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___372_12597.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 let uu____12598 = FStar_SMTEncoding_Term.mk_Valid tt1  in
                 (uu____12598, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____12642 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____12642 with
        | (vars,guards,env2,decls,uu____12681) ->
            let uu____12694 = encode_smt_patterns ps env2  in
            (match uu____12694 with
             | (pats,decls') ->
                 let uu____12731 = encode_formula body env2  in
                 (match uu____12731 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12763;
                             FStar_SMTEncoding_Term.rng = uu____12764;_}::[])::[]
                            when
                            let uu____12781 =
                              FStar_Ident.text_of_lid
                                FStar_Parser_Const.guard_free
                               in
                            uu____12781 = gf -> []
                        | uu____12784 -> guards  in
                      let uu____12789 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____12789, body1,
                        (FStar_List.append decls
                           (FStar_List.append decls' decls'')))))
         in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi  in
       let uu____12800 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____12800 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12809 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____12915  ->
                     match uu____12915 with
                     | (l,uu____12940) -> FStar_Ident.lid_equals op l))
              in
           (match uu____12809 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____13009,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____13101 = encode_q_body env vars pats body  in
             match uu____13101 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____13146 =
                     let uu____13157 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____13157)  in
                   FStar_SMTEncoding_Term.mkForall
                     phi1.FStar_Syntax_Syntax.pos uu____13146
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____13188 = encode_q_body env vars pats body  in
             match uu____13188 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____13232 =
                   let uu____13233 =
                     let uu____13244 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____13244)  in
                   FStar_SMTEncoding_Term.mkExists
                     phi1.FStar_Syntax_Syntax.pos uu____13233
                    in
                 (uu____13232, decls))))
