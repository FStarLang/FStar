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
          let uu____1899 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue  in
          (uu____1899, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____1901 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse  in
          (uu____1901, [])
      | FStar_Const.Const_char c1 ->
          let uu____1904 =
            let uu____1905 =
              let uu____1913 =
                let uu____1916 =
                  let uu____1917 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1)
                     in
                  FStar_SMTEncoding_Term.boxInt uu____1917  in
                [uu____1916]  in
              ("FStar.Char.__char_of_int", uu____1913)  in
            FStar_SMTEncoding_Util.mkApp uu____1905  in
          (uu____1904, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____1935 =
            let uu____1936 = FStar_SMTEncoding_Util.mkInteger i  in
            FStar_SMTEncoding_Term.boxInt uu____1936  in
          (uu____1935, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.FStar_SMTEncoding_Env.tcenv).FStar_TypeChecker_Env.dsenv
              repr sw FStar_Range.dummyRange
             in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____1957) ->
          let uu____1960 =
            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.string_const s
             in
          (uu____1960, [])
      | FStar_Const.Const_range uu____1961 ->
          let uu____1962 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          (uu____1962, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | c1 ->
          let uu____1964 =
            let uu____1966 = FStar_Syntax_Print.const_to_string c1  in
            FStar_Util.format1 "Unhandled constant: %s" uu____1966  in
          failwith uu____1964

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
        (let uu____1995 =
           FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
             FStar_Options.Medium
            in
         if uu____1995
         then
           let uu____1998 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____1998
         else ());
        (let uu____2004 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2101  ->
                   fun b  ->
                     match uu____2101 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2186 =
                           let x = FStar_Pervasives_Native.fst b  in
                           let uu____2207 =
                             FStar_SMTEncoding_Env.gen_term_var env1 x  in
                           match uu____2207 with
                           | (xxsym,xx,env') ->
                               let uu____2237 =
                                 let uu____2242 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____2242 env1 xx
                                  in
                               (match uu____2237 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x))
                            in
                         (match uu____2186 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____2004 with
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
          let uu____2416 = encode_term t env  in
          match uu____2416 with
          | (t1,decls) ->
              let uu____2427 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____2427, decls)

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
          let uu____2438 = encode_term t env  in
          match uu____2438 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____2453 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____2453, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____2455 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____2455, decls))

and (encode_arith_term :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____2461 = encode_args args_e env  in
        match uu____2461 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____2480 -> failwith "Impossible"  in
            let unary arg_tms1 =
              let uu____2492 = FStar_List.hd arg_tms1  in
              FStar_SMTEncoding_Term.unboxInt uu____2492  in
            let binary arg_tms1 =
              let uu____2507 =
                let uu____2508 = FStar_List.hd arg_tms1  in
                FStar_SMTEncoding_Term.unboxInt uu____2508  in
              let uu____2509 =
                let uu____2510 =
                  let uu____2511 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____2511  in
                FStar_SMTEncoding_Term.unboxInt uu____2510  in
              (uu____2507, uu____2509)  in
            let mk_default uu____2519 =
              let uu____2520 =
                FStar_SMTEncoding_Env.lookup_free_var_sym env
                  head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____2520 with
              | (fname,fuel_args,arity) ->
                  let args = FStar_List.append fuel_args arg_tms  in
                  maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity
                    args
               in
            let mk_l op mk_args ts =
              let uu____2585 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____2585
              then
                let uu____2588 =
                  let uu____2589 = mk_args ts  in op uu____2589  in
                FStar_All.pipe_right uu____2588 FStar_SMTEncoding_Term.boxInt
              else mk_default ()  in
            let mk_nl nm op ts =
              let uu____2627 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____2627
              then
                let uu____2630 = binary ts  in
                match uu____2630 with
                | (t1,t2) ->
                    let uu____2637 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____2637
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____2643 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____2643
                 then
                   let uu____2646 =
                     let uu____2647 = binary ts  in op uu____2647  in
                   FStar_All.pipe_right uu____2646
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
            let uu____2812 =
              let uu____2822 =
                FStar_List.tryFind
                  (fun uu____2846  ->
                     match uu____2846 with
                     | (l,uu____2857) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____2822 FStar_Util.must  in
            (match uu____2812 with
             | (uu____2901,op) ->
                 let uu____2913 = op arg_tms  in (uu____2913, decls))

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
        let uu____2921 = FStar_List.hd args_e  in
        match uu____2921 with
        | (tm_sz,uu____2929) ->
            let uu____2938 = uu____2921  in
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let uu____2947 =
                FStar_Util.smap_try_find env.FStar_SMTEncoding_Env.cache
                  sz_key
                 in
              match uu____2947 with
              | FStar_Pervasives_Native.Some cache_entry ->
                  FStar_SMTEncoding_Env.use_cache_entry cache_entry
              | FStar_Pervasives_Native.None  ->
                  let t_decls1 = FStar_SMTEncoding_Term.mkBvConstructor sz
                     in
                  ((let uu____2955 =
                      FStar_SMTEncoding_Env.mk_cache_entry env "" [] t_decls1
                       in
                    FStar_Util.smap_add env.FStar_SMTEncoding_Env.cache
                      sz_key uu____2955);
                   t_decls1)
               in
            let uu____2957 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____2983::(sz_arg,uu____2985)::uu____2986::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____3053 =
                    let uu____3054 = FStar_List.tail args_e  in
                    FStar_List.tail uu____3054  in
                  let uu____3057 =
                    let uu____3061 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____3061  in
                  (uu____3053, uu____3057)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____3068::(sz_arg,uu____3070)::uu____3071::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____3138 =
                    let uu____3140 = FStar_Syntax_Print.term_to_string sz_arg
                       in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____3140
                     in
                  failwith uu____3138
              | uu____3150 ->
                  let uu____3165 = FStar_List.tail args_e  in
                  (uu____3165, FStar_Pervasives_Native.None)
               in
            (match uu____2957 with
             | (arg_tms,ext_sz) ->
                 let uu____3184 = encode_args arg_tms env  in
                 (match uu____3184 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____3205 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____3217 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____3217  in
                      let unary_arith arg_tms2 =
                        let uu____3228 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____3228  in
                      let binary arg_tms2 =
                        let uu____3243 =
                          let uu____3244 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3244
                           in
                        let uu____3245 =
                          let uu____3246 =
                            let uu____3247 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____3247  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3246
                           in
                        (uu____3243, uu____3245)  in
                      let binary_arith arg_tms2 =
                        let uu____3264 =
                          let uu____3265 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3265
                           in
                        let uu____3266 =
                          let uu____3267 =
                            let uu____3268 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____3268  in
                          FStar_SMTEncoding_Term.unboxInt uu____3267  in
                        (uu____3264, uu____3266)  in
                      let mk_bv op mk_args resBox ts =
                        let uu____3326 =
                          let uu____3327 = mk_args ts  in op uu____3327  in
                        FStar_All.pipe_right uu____3326 resBox  in
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
                        let uu____3459 =
                          let uu____3464 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____3464  in
                        let uu____3473 =
                          let uu____3478 =
                            let uu____3480 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____3480  in
                          FStar_SMTEncoding_Term.boxBitVec uu____3478  in
                        mk_bv uu____3459 unary uu____3473 arg_tms2  in
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
                      let uu____3720 =
                        let uu____3730 =
                          FStar_List.tryFind
                            (fun uu____3754  ->
                               match uu____3754 with
                               | (l,uu____3765) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____3730 FStar_Util.must  in
                      (match uu____3720 with
                       | (uu____3811,op) ->
                           let uu____3823 = op arg_tms1  in
                           (uu____3823, (FStar_List.append sz_decls decls)))))

and (encode_deeply_embedded_quantifier :
  FStar_Syntax_Syntax.term ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let env1 =
        let uu___363_3833 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___363_3833.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___363_3833.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___363_3833.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___363_3833.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___363_3833.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.cache =
            (uu___363_3833.FStar_SMTEncoding_Env.cache);
          FStar_SMTEncoding_Env.nolabels =
            (uu___363_3833.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name =
            (uu___363_3833.FStar_SMTEncoding_Env.use_zfuel_name);
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___363_3833.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___363_3833.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier = true
        }  in
      let uu____3835 = encode_term t env1  in
      match uu____3835 with
      | (tm,decls) ->
          let vars = FStar_SMTEncoding_Term.free_variables tm  in
          let valid_tm = FStar_SMTEncoding_Term.mk_Valid tm  in
          let key =
            FStar_SMTEncoding_Term.mkForall t.FStar_Syntax_Syntax.pos
              ([], vars, valid_tm)
             in
          let tkey_hash = FStar_SMTEncoding_Term.hash_of_term key  in
          let uu____3857 =
            FStar_Util.smap_try_find env1.FStar_SMTEncoding_Env.cache
              tkey_hash
             in
          (match uu____3857 with
           | FStar_Pervasives_Native.Some cache_entry ->
               (tm,
                 (FStar_List.append decls
                    (FStar_SMTEncoding_Env.use_cache_entry cache_entry)))
           | uu____3865 ->
               (match tm.FStar_SMTEncoding_Term.tm with
                | FStar_SMTEncoding_Term.App
                    (uu____3872,{
                                  FStar_SMTEncoding_Term.tm =
                                    FStar_SMTEncoding_Term.FreeV uu____3873;
                                  FStar_SMTEncoding_Term.freevars =
                                    uu____3874;
                                  FStar_SMTEncoding_Term.rng = uu____3875;_}::
                     {
                       FStar_SMTEncoding_Term.tm =
                         FStar_SMTEncoding_Term.FreeV uu____3876;
                       FStar_SMTEncoding_Term.freevars = uu____3877;
                       FStar_SMTEncoding_Term.rng = uu____3878;_}::[])
                    ->
                    (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                       (FStar_Errors.Warning_QuantifierWithoutPattern,
                         "Not encoding deeply embedded, unguarded quantifier to SMT");
                     (tm, decls))
                | uu____3912 ->
                    let uu____3913 = encode_formula t env1  in
                    (match uu____3913 with
                     | (phi,decls') ->
                         let interp =
                           match vars with
                           | [] ->
                               let uu____3930 =
                                 let uu____3935 =
                                   FStar_SMTEncoding_Term.mk_Valid tm  in
                                 (uu____3935, phi)  in
                               FStar_SMTEncoding_Util.mkIff uu____3930
                           | uu____3936 ->
                               let uu____3937 =
                                 let uu____3948 =
                                   let uu____3949 =
                                     let uu____3954 =
                                       FStar_SMTEncoding_Term.mk_Valid tm  in
                                     (uu____3954, phi)  in
                                   FStar_SMTEncoding_Util.mkIff uu____3949
                                    in
                                 ([[valid_tm]], vars, uu____3948)  in
                               FStar_SMTEncoding_Term.mkForall
                                 t.FStar_Syntax_Syntax.pos uu____3937
                            in
                         let ax =
                           let uu____3964 =
                             let uu____3972 =
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 "l_quant_interp"
                                in
                             (interp,
                               (FStar_Pervasives_Native.Some
                                  "Interpretation of deeply embedded quantifier"),
                               uu____3972)
                              in
                           FStar_SMTEncoding_Util.mkAssume uu____3964  in
                         let decls1 =
                           FStar_List.append decls
                             (FStar_List.append decls' [ax])
                            in
                         ((let uu____3982 =
                             FStar_SMTEncoding_Env.mk_cache_entry env1 "" []
                               decls1
                              in
                           FStar_Util.smap_add
                             env1.FStar_SMTEncoding_Env.cache tkey_hash
                             uu____3982);
                          (tm, decls1)))))

and (encode_term :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____3992 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____3992
       then
         let uu____3997 = FStar_Syntax_Print.tag_of_term t  in
         let uu____3999 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____4001 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____3997 uu____3999
           uu____4001
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____4010 ->
           let uu____4033 =
             let uu____4035 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____4038 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____4040 = FStar_Syntax_Print.term_to_string t0  in
             let uu____4042 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____4035
               uu____4038 uu____4040 uu____4042
              in
           failwith uu____4033
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____4049 =
             let uu____4051 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____4054 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____4056 = FStar_Syntax_Print.term_to_string t0  in
             let uu____4058 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____4051
               uu____4054 uu____4056 uu____4058
              in
           failwith uu____4049
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let e = FStar_Syntax_Util.unfold_lazy i  in
           ((let uu____4068 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____4068
             then
               let uu____4073 = FStar_Syntax_Print.term_to_string t0  in
               let uu____4075 = FStar_Syntax_Print.term_to_string e  in
               FStar_Util.print2 ">> Unfolded (%s) ~> (%s)\n" uu____4073
                 uu____4075
             else ());
            encode_term e env)
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____4081 =
             let uu____4083 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____4083
              in
           failwith uu____4081
       | FStar_Syntax_Syntax.Tm_ascribed (t1,(k,uu____4092),uu____4093) ->
           let uu____4142 =
             match k with
             | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
             | uu____4152 -> false  in
           if uu____4142
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t1 env
       | FStar_Syntax_Syntax.Tm_quoted (qt,uu____4170) ->
           let tv =
             let uu____4176 =
               let uu____4183 = FStar_Reflection_Basic.inspect_ln qt  in
               FStar_Syntax_Embeddings.embed
                 FStar_Reflection_Embeddings.e_term_view uu____4183
                in
             uu____4176 t.FStar_Syntax_Syntax.pos
               FStar_Pervasives_Native.None
               FStar_Syntax_Embeddings.id_norm_cb
              in
           ((let uu____4210 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____4210
             then
               let uu____4215 = FStar_Syntax_Print.term_to_string t0  in
               let uu____4217 = FStar_Syntax_Print.term_to_string tv  in
               FStar_Util.print2 ">> Inspected (%s) ~> (%s)\n" uu____4215
                 uu____4217
             else ());
            (let t1 =
               let uu____4225 =
                 let uu____4236 = FStar_Syntax_Syntax.as_arg tv  in
                 [uu____4236]  in
               FStar_Syntax_Util.mk_app
                 (FStar_Reflection_Data.refl_constant_term
                    FStar_Reflection_Data.fstar_refl_pack_ln) uu____4225
                in
             encode_term t1 env))
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_pattern uu____4262) ->
           encode_term t1
             (let uu___364_4280 = env  in
              {
                FStar_SMTEncoding_Env.bvar_bindings =
                  (uu___364_4280.FStar_SMTEncoding_Env.bvar_bindings);
                FStar_SMTEncoding_Env.fvar_bindings =
                  (uu___364_4280.FStar_SMTEncoding_Env.fvar_bindings);
                FStar_SMTEncoding_Env.depth =
                  (uu___364_4280.FStar_SMTEncoding_Env.depth);
                FStar_SMTEncoding_Env.tcenv =
                  (uu___364_4280.FStar_SMTEncoding_Env.tcenv);
                FStar_SMTEncoding_Env.warn =
                  (uu___364_4280.FStar_SMTEncoding_Env.warn);
                FStar_SMTEncoding_Env.cache =
                  (uu___364_4280.FStar_SMTEncoding_Env.cache);
                FStar_SMTEncoding_Env.nolabels =
                  (uu___364_4280.FStar_SMTEncoding_Env.nolabels);
                FStar_SMTEncoding_Env.use_zfuel_name =
                  (uu___364_4280.FStar_SMTEncoding_Env.use_zfuel_name);
                FStar_SMTEncoding_Env.encode_non_total_function_typ =
                  (uu___364_4280.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                FStar_SMTEncoding_Env.current_module_name =
                  (uu___364_4280.FStar_SMTEncoding_Env.current_module_name);
                FStar_SMTEncoding_Env.encoding_quantifier = false
              })
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____4283) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = FStar_SMTEncoding_Env.lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____4291 = head_redex env t  in
           if uu____4291
           then let uu____4298 = whnf env t  in encode_term uu____4298 env
           else
             (let uu____4301 =
                FStar_SMTEncoding_Env.lookup_free_var_name env
                  v1.FStar_Syntax_Syntax.fv_name
                 in
              match uu____4301 with
              | (uu____4312,arity) ->
                  let tok =
                    FStar_SMTEncoding_Env.lookup_free_var env
                      v1.FStar_Syntax_Syntax.fv_name
                     in
                  let aux_decls =
                    if arity > (Prims.parse_int "0")
                    then
                      match tok.FStar_SMTEncoding_Term.tm with
                      | FStar_SMTEncoding_Term.FreeV uu____4322 ->
                          let uu____4328 =
                            let uu____4329 =
                              let uu____4337 =
                                FStar_SMTEncoding_Term.kick_partial_app tok
                                 in
                              let uu____4338 =
                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                  "@kick_partial_app"
                                 in
                              (uu____4337,
                                (FStar_Pervasives_Native.Some
                                   "kick_partial_app"), uu____4338)
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____4329  in
                          [uu____4328]
                      | FStar_SMTEncoding_Term.App (uu____4344,[]) ->
                          let uu____4347 =
                            let uu____4348 =
                              let uu____4356 =
                                FStar_SMTEncoding_Term.kick_partial_app tok
                                 in
                              let uu____4357 =
                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                  "@kick_partial_app"
                                 in
                              (uu____4356,
                                (FStar_Pervasives_Native.Some
                                   "kick_partial_app"), uu____4357)
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____4348  in
                          [uu____4347]
                      | uu____4363 -> []
                    else []  in
                  (tok, aux_decls))
       | FStar_Syntax_Syntax.Tm_type uu____4366 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4368) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.FStar_SMTEncoding_Env.current_module_name
              in
           let uu____4398 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____4398 with
            | (binders1,res) ->
                let uu____4409 =
                  (env.FStar_SMTEncoding_Env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____4409
                then
                  let uu____4416 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____4416 with
                   | (vars,guards,env',decls,uu____4441) ->
                       let fsym =
                         let uu____4460 =
                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                             "f"
                            in
                         (uu____4460, FStar_SMTEncoding_Term.Term_sort)  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____4466 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___365_4475 =
                              env.FStar_SMTEncoding_Env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___365_4475.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___365_4475.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___365_4475.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___365_4475.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___365_4475.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___365_4475.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___365_4475.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___365_4475.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___365_4475.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___365_4475.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___365_4475.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___365_4475.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___365_4475.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___365_4475.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___365_4475.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___365_4475.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___365_4475.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___365_4475.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___365_4475.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___365_4475.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___365_4475.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___365_4475.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___365_4475.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___365_4475.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___365_4475.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___365_4475.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___365_4475.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___365_4475.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___365_4475.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___365_4475.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___365_4475.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___365_4475.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___365_4475.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___365_4475.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___365_4475.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___365_4475.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___365_4475.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___365_4475.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___365_4475.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___365_4475.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___365_4475.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___365_4475.FStar_TypeChecker_Env.nbe)
                            }) res
                          in
                       (match uu____4466 with
                        | (pre_opt,res_t) ->
                            let uu____4487 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____4487 with
                             | (res_pred,decls') ->
                                 let uu____4498 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____4511 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____4511, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____4515 =
                                         encode_formula pre env'  in
                                       (match uu____4515 with
                                        | (guard,decls0) ->
                                            let uu____4528 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____4528, decls0))
                                    in
                                 (match uu____4498 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____4542 =
                                          let uu____4553 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____4553)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t.FStar_Syntax_Syntax.pos
                                          uu____4542
                                         in
                                      let cvars =
                                        let uu____4570 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____4570
                                          (FStar_List.filter
                                             (fun uu____4600  ->
                                                match uu____4600 with
                                                | (x,uu____4608) ->
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
                                      let uu____4627 =
                                        FStar_Util.smap_try_find
                                          env.FStar_SMTEncoding_Env.cache
                                          tkey_hash
                                         in
                                      (match uu____4627 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____4635 =
                                             let uu____4636 =
                                               let uu____4644 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV)
                                                  in
                                               ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                                 uu____4644)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4636
                                              in
                                           (uu____4635,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (FStar_SMTEncoding_Env.use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____4666 =
                                               let uu____4668 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____4668
                                                in
                                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                               uu____4666
                                              in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars
                                              in
                                           let caption =
                                             let uu____4681 =
                                               FStar_Options.log_queries ()
                                                in
                                             if uu____4681
                                             then
                                               let uu____4684 =
                                                 let uu____4686 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env.FStar_SMTEncoding_Env.tcenv
                                                     t0
                                                    in
                                                 FStar_Util.replace_char
                                                   uu____4686 10 32
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____4684
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
                                             let uu____4699 =
                                               let uu____4707 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars
                                                  in
                                               (tsym, uu____4707)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4699
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
                                             let uu____4723 =
                                               let uu____4731 =
                                                 FStar_SMTEncoding_Term.mkForall
                                                   t0.FStar_Syntax_Syntax.pos
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind)
                                                  in
                                               (uu____4731,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name)
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4723
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
                                             let uu____4748 =
                                               let uu____4756 =
                                                 let uu____4757 =
                                                   let uu____4768 =
                                                     let uu____4769 =
                                                       let uu____4774 =
                                                         let uu____4775 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f
                                                            in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____4775
                                                          in
                                                       (f_has_t, uu____4774)
                                                        in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____4769
                                                      in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____4768)
                                                    in
                                                 let uu____4790 =
                                                   mkForall_fuel
                                                     t0.FStar_Syntax_Syntax.pos
                                                    in
                                                 uu____4790 uu____4757  in
                                               (uu____4756,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4748
                                              in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym
                                                in
                                             let uu____4813 =
                                               let uu____4821 =
                                                 let uu____4822 =
                                                   let uu____4833 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp)
                                                      in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____4833)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   t0.FStar_Syntax_Syntax.pos
                                                   uu____4822
                                                  in
                                               (uu____4821,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4813
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
                                           ((let uu____4854 =
                                               FStar_SMTEncoding_Env.mk_cache_entry
                                                 env tsym cvar_sorts t_decls1
                                                in
                                             FStar_Util.smap_add
                                               env.FStar_SMTEncoding_Env.cache
                                               tkey_hash uu____4854);
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
                     let uu____4873 =
                       let uu____4881 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____4881,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____4873  in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)  in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym  in
                     let uu____4900 =
                       let uu____4908 =
                         let uu____4909 =
                           let uu____4920 =
                             let uu____4921 =
                               let uu____4926 =
                                 let uu____4927 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____4927
                                  in
                               (f_has_t, uu____4926)  in
                             FStar_SMTEncoding_Util.mkImp uu____4921  in
                           ([[f_has_t]], [fsym], uu____4920)  in
                         let uu____4947 =
                           mkForall_fuel t0.FStar_Syntax_Syntax.pos  in
                         uu____4947 uu____4909  in
                       (uu____4908, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____4900  in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____4965 ->
           let uu____4972 =
             let uu____4977 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Env.Weak;
                 FStar_TypeChecker_Env.HNF;
                 FStar_TypeChecker_Env.EraseUniverses]
                 env.FStar_SMTEncoding_Env.tcenv t0
                in
             match uu____4977 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____4984;
                 FStar_Syntax_Syntax.vars = uu____4985;_} ->
                 let uu____4992 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____4992 with
                  | (b,f1) ->
                      let uu____5017 =
                        let uu____5018 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____5018  in
                      (uu____5017, f1))
             | uu____5033 -> failwith "impossible"  in
           (match uu____4972 with
            | (x,f) ->
                let uu____5045 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____5045 with
                 | (base_t,decls) ->
                     let uu____5056 =
                       FStar_SMTEncoding_Env.gen_term_var env x  in
                     (match uu____5056 with
                      | (x1,xtm,env') ->
                          let uu____5073 = encode_formula f env'  in
                          (match uu____5073 with
                           | (refinement,decls') ->
                               let uu____5084 =
                                 FStar_SMTEncoding_Env.fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____5084 with
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
                                      let uu____5109 =
                                        let uu____5117 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____5125 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____5117
                                          uu____5125
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____5109
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____5173  ->
                                              match uu____5173 with
                                              | (y,uu____5181) ->
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
                                    let uu____5219 =
                                      FStar_Util.smap_try_find
                                        env.FStar_SMTEncoding_Env.cache
                                        tkey_hash
                                       in
                                    (match uu____5219 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____5227 =
                                           let uu____5228 =
                                             let uu____5236 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV)
                                                in
                                             ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                               uu____5236)
                                              in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____5228
                                            in
                                         (uu____5227,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (FStar_SMTEncoding_Env.use_cache_entry
                                                    cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.FStar_SMTEncoding_Env.current_module_name
                                            in
                                         let tsym =
                                           let uu____5260 =
                                             let uu____5262 =
                                               let uu____5264 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____5264
                                                in
                                             Prims.strcat module_name
                                               uu____5262
                                              in
                                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                             uu____5260
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
                                           let uu____5282 =
                                             let uu____5290 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1
                                                in
                                             (tsym, uu____5290)  in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____5282
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
                                           let uu____5307 =
                                             let uu____5315 =
                                               let uu____5316 =
                                                 let uu____5327 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base)
                                                    in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____5327)
                                                  in
                                               FStar_SMTEncoding_Term.mkForall
                                                 t0.FStar_Syntax_Syntax.pos
                                                 uu____5316
                                                in
                                             (uu____5315,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____5307
                                            in
                                         let t_kinding =
                                           let uu____5341 =
                                             let uu____5349 =
                                               FStar_SMTEncoding_Term.mkForall
                                                 t0.FStar_Syntax_Syntax.pos
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind)
                                                in
                                             (uu____5349,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____5341
                                            in
                                         let t_interp =
                                           let uu____5363 =
                                             let uu____5371 =
                                               let uu____5372 =
                                                 let uu____5383 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding)
                                                    in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____5383)
                                                  in
                                               FStar_SMTEncoding_Term.mkForall
                                                 t0.FStar_Syntax_Syntax.pos
                                                 uu____5372
                                                in
                                             (uu____5371,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement_interpretation"),
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____5363
                                            in
                                         let t_decls1 =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1])
                                            in
                                         ((let uu____5410 =
                                             FStar_SMTEncoding_Env.mk_cache_entry
                                               env tsym cvar_sorts t_decls1
                                              in
                                           FStar_Util.smap_add
                                             env.FStar_SMTEncoding_Env.cache
                                             tkey_hash uu____5410);
                                          (t1, t_decls1))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,uu____5412) ->
           let ttm =
             let uu____5430 =
               FStar_Syntax_Unionfind.uvar_id
                 uv.FStar_Syntax_Syntax.ctx_uvar_head
                in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____5430  in
           let uu____5432 =
             encode_term_pred FStar_Pervasives_Native.None
               uv.FStar_Syntax_Syntax.ctx_uvar_typ env ttm
              in
           (match uu____5432 with
            | (t_has_k,decls) ->
                let d =
                  let uu____5444 =
                    let uu____5452 =
                      let uu____5454 =
                        let uu____5456 =
                          let uu____5458 =
                            FStar_Syntax_Unionfind.uvar_id
                              uv.FStar_Syntax_Syntax.ctx_uvar_head
                             in
                          FStar_Util.string_of_int uu____5458  in
                        FStar_Util.format1 "uvar_typing_%s" uu____5456  in
                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                        uu____5454
                       in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____5452)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____5444  in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____5464 ->
           let uu____5481 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____5481 with
            | (head1,args_e) ->
                let uu____5528 =
                  let uu____5543 =
                    let uu____5544 = FStar_Syntax_Subst.compress head1  in
                    uu____5544.FStar_Syntax_Syntax.n  in
                  (uu____5543, args_e)  in
                (match uu____5528 with
                 | uu____5561 when head_redex env head1 ->
                     let uu____5576 = whnf env t  in
                     encode_term uu____5576 env
                 | uu____5577 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____5600 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5618) when
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
                       FStar_Syntax_Syntax.pos = uu____5640;
                       FStar_Syntax_Syntax.vars = uu____5641;_},uu____5642),uu____5643)
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
                       FStar_Syntax_Syntax.pos = uu____5669;
                       FStar_Syntax_Syntax.vars = uu____5670;_},uu____5671),
                    (v0,uu____5673)::(v1,uu____5675)::(v2,uu____5677)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____5748 = encode_term v0 env  in
                     (match uu____5748 with
                      | (v01,decls0) ->
                          let uu____5759 = encode_term v1 env  in
                          (match uu____5759 with
                           | (v11,decls1) ->
                               let uu____5770 = encode_term v2 env  in
                               (match uu____5770 with
                                | (v21,decls2) ->
                                    let uu____5781 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____5781,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(v0,uu____5784)::(v1,uu____5786)::(v2,uu____5788)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____5855 = encode_term v0 env  in
                     (match uu____5855 with
                      | (v01,decls0) ->
                          let uu____5866 = encode_term v1 env  in
                          (match uu____5866 with
                           | (v11,decls1) ->
                               let uu____5877 = encode_term v2 env  in
                               (match uu____5877 with
                                | (v21,decls2) ->
                                    let uu____5888 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____5888,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____5890)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____5926)::(rng,uu____5928)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____5979) ->
                     let e0 =
                       let uu____6001 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg
                         env.FStar_SMTEncoding_Env.tcenv head1 uu____6001
                        in
                     ((let uu____6011 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug
                              env.FStar_SMTEncoding_Env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____6011
                       then
                         let uu____6016 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____6016
                       else ());
                      (let e =
                         let uu____6024 =
                           let uu____6029 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____6030 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____6029
                             uu____6030
                            in
                         uu____6024 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____6041),(arg,uu____6043)::[]) -> encode_term arg env
                 | uu____6078 ->
                     let uu____6093 = encode_args args_e env  in
                     (match uu____6093 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____6154 = encode_term head1 env  in
                            match uu____6154 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____6226 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____6226 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____6324  ->
                                                 fun uu____6325  ->
                                                   match (uu____6324,
                                                           uu____6325)
                                                   with
                                                   | ((bv,uu____6355),
                                                      (a,uu____6357)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____6387 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____6387
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____6388 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm
                                             in
                                          (match uu____6388 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type
                                                  in
                                               let e_typing =
                                                 let uu____6403 =
                                                   let uu____6411 =
                                                     FStar_SMTEncoding_Term.mkForall
                                                       t0.FStar_Syntax_Syntax.pos
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____6420 =
                                                     let uu____6422 =
                                                       let uu____6424 =
                                                         let uu____6426 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm
                                                            in
                                                         FStar_Util.digest_of_string
                                                           uu____6426
                                                          in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____6424
                                                        in
                                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                       uu____6422
                                                      in
                                                   (uu____6411,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____6420)
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____6403
                                                  in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing])))))))
                             in
                          let encode_full_app fv =
                            let uu____6448 =
                              FStar_SMTEncoding_Env.lookup_free_var_sym env
                                fv
                               in
                            match uu____6448 with
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
                                   FStar_Syntax_Syntax.pos = uu____6479;
                                   FStar_Syntax_Syntax.vars = uu____6480;_},uu____6481)
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
                                   FStar_Syntax_Syntax.pos = uu____6488;
                                   FStar_Syntax_Syntax.vars = uu____6489;_},uu____6490)
                                ->
                                let uu____6495 =
                                  let uu____6496 =
                                    let uu____6501 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____6501
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____6496
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____6495
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____6531 =
                                  let uu____6532 =
                                    let uu____6537 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____6537
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____6532
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____6531
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____6566,(FStar_Util.Inl t1,uu____6568),uu____6569)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____6616,(FStar_Util.Inr c,uu____6618),uu____6619)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____6666 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____6687 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Env.Weak;
                                     FStar_TypeChecker_Env.HNF;
                                     FStar_TypeChecker_Env.EraseUniverses]
                                     env.FStar_SMTEncoding_Env.tcenv
                                     head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____6687
                                  in
                               let uu____6688 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____6688 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____6704;
                                            FStar_Syntax_Syntax.vars =
                                              uu____6705;_},uu____6706)
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
                                     | uu____6724 ->
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
           let uu____6803 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____6803 with
            | (bs1,body1,opening) ->
                let fallback uu____6828 =
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
                  let uu____6838 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort)
                     in
                  (uu____6838, [decl])  in
                let is_impure rc =
                  let uu____6849 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                      env.FStar_SMTEncoding_Env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____6849 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____6864 =
                          let uu____6877 =
                            FStar_TypeChecker_Env.get_range
                              env.FStar_SMTEncoding_Env.tcenv
                             in
                          FStar_TypeChecker_Util.new_implicit_var
                            "SMTEncoding codomain" uu____6877
                            env.FStar_SMTEncoding_Env.tcenv
                            FStar_Syntax_Util.ktype0
                           in
                        (match uu____6864 with
                         | (t1,uu____6880,uu____6881) -> t1)
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  let uu____6899 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                     in
                  if uu____6899
                  then
                    let uu____6904 = FStar_Syntax_Syntax.mk_Total res_typ  in
                    FStar_Pervasives_Native.Some uu____6904
                  else
                    (let uu____6907 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid
                        in
                     if uu____6907
                     then
                       let uu____6912 = FStar_Syntax_Syntax.mk_GTotal res_typ
                          in
                       FStar_Pervasives_Native.Some uu____6912
                     else FStar_Pervasives_Native.None)
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____6920 =
                         let uu____6926 =
                           let uu____6928 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____6928
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____6926)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____6920);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____6933 =
                       (is_impure rc) &&
                         (let uu____6936 =
                            FStar_TypeChecker_Env.is_reifiable_rc
                              env.FStar_SMTEncoding_Env.tcenv rc
                             in
                          Prims.op_Negation uu____6936)
                        in
                     if uu____6933
                     then fallback ()
                     else
                       (let cache_size =
                          FStar_Util.smap_size
                            env.FStar_SMTEncoding_Env.cache
                           in
                        let uu____6947 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____6947 with
                        | (vars,guards,envbody,decls,uu____6972) ->
                            let body2 =
                              let uu____6986 =
                                FStar_TypeChecker_Env.is_reifiable_rc
                                  env.FStar_SMTEncoding_Env.tcenv rc
                                 in
                              if uu____6986
                              then
                                FStar_TypeChecker_Util.reify_body
                                  env.FStar_SMTEncoding_Env.tcenv body1
                              else body1  in
                            let uu____6991 = encode_term body2 envbody  in
                            (match uu____6991 with
                             | (body3,decls') ->
                                 let uu____7002 =
                                   let uu____7011 = codomain_eff rc  in
                                   match uu____7011 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____7030 = encode_term tfun env
                                          in
                                       (match uu____7030 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____7002 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____7064 =
                                          let uu____7075 =
                                            let uu____7076 =
                                              let uu____7081 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____7081, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____7076
                                             in
                                          ([], vars, uu____7075)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t0.FStar_Syntax_Syntax.pos
                                          uu____7064
                                         in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body
                                         in
                                      let uu____7089 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            (cvars, key_body)
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____7105 =
                                              let uu____7108 =
                                                let uu____7116 =
                                                  FStar_SMTEncoding_Term.free_variables
                                                    t1
                                                   in
                                                FStar_List.append uu____7116
                                                  cvars
                                                 in
                                              FStar_Util.remove_dups
                                                FStar_SMTEncoding_Term.fv_eq
                                                uu____7108
                                               in
                                            let uu____7134 =
                                              FStar_SMTEncoding_Util.mkAnd
                                                (key_body, t1)
                                               in
                                            (uu____7105, uu____7134)
                                         in
                                      (match uu____7089 with
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
                                           let uu____7156 =
                                             FStar_Util.smap_try_find
                                               env.FStar_SMTEncoding_Env.cache
                                               tkey_hash
                                              in
                                           (match uu____7156 with
                                            | FStar_Pervasives_Native.Some
                                                cache_entry ->
                                                let uu____7164 =
                                                  let uu____7165 =
                                                    let uu____7173 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                                      uu____7173)
                                                     in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____7165
                                                   in
                                                (uu____7164,
                                                  (FStar_List.append decls
                                                     (FStar_List.append
                                                        decls'
                                                        (FStar_List.append
                                                           decls''
                                                           (FStar_SMTEncoding_Env.use_cache_entry
                                                              cache_entry)))))
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                let uu____7179 =
                                                  is_an_eta_expansion env
                                                    vars body3
                                                   in
                                                (match uu____7179 with
                                                 | FStar_Pervasives_Native.Some
                                                     t1 ->
                                                     let decls1 =
                                                       let uu____7188 =
                                                         let uu____7190 =
                                                           FStar_Util.smap_size
                                                             env.FStar_SMTEncoding_Env.cache
                                                            in
                                                         uu____7190 =
                                                           cache_size
                                                          in
                                                       if uu____7188
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
                                                         let uu____7206 =
                                                           let uu____7208 =
                                                             FStar_Util.digest_of_string
                                                               tkey_hash
                                                              in
                                                           Prims.strcat
                                                             "Tm_abs_"
                                                             uu____7208
                                                            in
                                                         FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                           uu____7206
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
                                                       let uu____7218 =
                                                         let uu____7226 =
                                                           FStar_List.map
                                                             FStar_SMTEncoding_Util.mkFreeV
                                                             cvars1
                                                            in
                                                         (fsym, uu____7226)
                                                          in
                                                       FStar_SMTEncoding_Util.mkApp
                                                         uu____7218
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
                                                           let uu____7243 =
                                                             let uu____7244 =
                                                               let uu____7252
                                                                 =
                                                                 FStar_SMTEncoding_Term.mkForall
                                                                   t0.FStar_Syntax_Syntax.pos
                                                                   ([[f]],
                                                                    cvars1,
                                                                    f_has_t)
                                                                  in
                                                               (uu____7252,
                                                                 (FStar_Pervasives_Native.Some
                                                                    a_name),
                                                                 a_name)
                                                                in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____7244
                                                              in
                                                           [uu____7243]
                                                        in
                                                     let interp_f =
                                                       let a_name =
                                                         Prims.strcat
                                                           "interpretation_"
                                                           fsym
                                                          in
                                                       let uu____7267 =
                                                         let uu____7275 =
                                                           let uu____7276 =
                                                             let uu____7287 =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (app, body3)
                                                                in
                                                             ([[app]],
                                                               (FStar_List.append
                                                                  vars cvars1),
                                                               uu____7287)
                                                              in
                                                           FStar_SMTEncoding_Term.mkForall
                                                             t0.FStar_Syntax_Syntax.pos
                                                             uu____7276
                                                            in
                                                         (uu____7275,
                                                           (FStar_Pervasives_Native.Some
                                                              a_name),
                                                           a_name)
                                                          in
                                                       FStar_SMTEncoding_Util.mkAssume
                                                         uu____7267
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
                                                     ((let uu____7302 =
                                                         FStar_SMTEncoding_Env.mk_cache_entry
                                                           env fsym
                                                           cvar_sorts f_decls
                                                          in
                                                       FStar_Util.smap_add
                                                         env.FStar_SMTEncoding_Env.cache
                                                         tkey_hash uu____7302);
                                                      (f, f_decls))))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____7303,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____7304;
                          FStar_Syntax_Syntax.lbunivs = uu____7305;
                          FStar_Syntax_Syntax.lbtyp = uu____7306;
                          FStar_Syntax_Syntax.lbeff = uu____7307;
                          FStar_Syntax_Syntax.lbdef = uu____7308;
                          FStar_Syntax_Syntax.lbattrs = uu____7309;
                          FStar_Syntax_Syntax.lbpos = uu____7310;_}::uu____7311),uu____7312)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____7346;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____7348;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____7350;
                FStar_Syntax_Syntax.lbpos = uu____7351;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____7378 ->
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
              let uu____7450 =
                let uu____7455 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____7455 env  in
              match uu____7450 with
              | (ee1,decls1) ->
                  let uu____7480 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____7480 with
                   | (xs,e21) ->
                       let uu____7505 = FStar_List.hd xs  in
                       (match uu____7505 with
                        | (x1,uu____7523) ->
                            let env' =
                              FStar_SMTEncoding_Env.push_term_var env x1 ee1
                               in
                            let uu____7529 = encode_body e21 env'  in
                            (match uu____7529 with
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
            let uu____7559 =
              let uu____7567 =
                let uu____7568 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____7568  in
              FStar_SMTEncoding_Env.gen_term_var env uu____7567  in
            match uu____7559 with
            | (scrsym,scr',env1) ->
                let uu____7578 = encode_term e env1  in
                (match uu____7578 with
                 | (scr,decls) ->
                     let uu____7589 =
                       let encode_branch b uu____7618 =
                         match uu____7618 with
                         | (else_case,decls1) ->
                             let uu____7637 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____7637 with
                              | (p,w,br) ->
                                  let uu____7663 = encode_pat env1 p  in
                                  (match uu____7663 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____7700  ->
                                                   match uu____7700 with
                                                   | (x,t) ->
                                                       FStar_SMTEncoding_Env.push_term_var
                                                         env2 x t) env1)
                                          in
                                       let uu____7707 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____7729 =
                                               encode_term w1 env2  in
                                             (match uu____7729 with
                                              | (w2,decls2) ->
                                                  let uu____7742 =
                                                    let uu____7743 =
                                                      let uu____7748 =
                                                        let uu____7749 =
                                                          let uu____7754 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____7754)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____7749
                                                         in
                                                      (guard, uu____7748)  in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____7743
                                                     in
                                                  (uu____7742, decls2))
                                          in
                                       (match uu____7707 with
                                        | (guard1,decls2) ->
                                            let uu____7769 =
                                              encode_br br env2  in
                                            (match uu____7769 with
                                             | (br1,decls3) ->
                                                 let uu____7782 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____7782,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____7589 with
                      | (match_tm,decls1) ->
                          let uu____7803 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange
                             in
                          (uu____7803, decls1)))

and (encode_pat :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.pat -> (FStar_SMTEncoding_Env.env_t * pattern))
  =
  fun env  ->
    fun pat  ->
      (let uu____7826 =
         FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
           FStar_Options.Medium
          in
       if uu____7826
       then
         let uu____7829 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____7829
       else ());
      (let uu____7834 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____7834 with
       | (vars,pat_term) ->
           let uu____7851 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____7907  ->
                     fun v1  ->
                       match uu____7907 with
                       | (env1,vars1) ->
                           let uu____7963 =
                             FStar_SMTEncoding_Env.gen_term_var env1 v1  in
                           (match uu____7963 with
                            | (xx,uu____7987,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, []))
              in
           (match uu____7851 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____8080 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____8081 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____8082 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____8090 = encode_const c env1  in
                      (match uu____8090 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____8098::uu____8099 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____8103 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon
                            env1.FStar_SMTEncoding_Env.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____8126 =
                          FStar_TypeChecker_Env.datacons_of_typ
                            env1.FStar_SMTEncoding_Env.tcenv tc_name
                           in
                        match uu____8126 with
                        | (uu____8134,uu____8135::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____8140 ->
                            FStar_SMTEncoding_Env.mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____8176  ->
                                  match uu____8176 with
                                  | (arg,uu____8186) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____8195 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____8195))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____8227) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____8258 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____8283 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____8329  ->
                                  match uu____8329 with
                                  | (arg,uu____8345) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____8354 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____8354))
                         in
                      FStar_All.pipe_right uu____8283 FStar_List.flatten
                   in
                let pat_term1 uu____8385 = encode_term pat_term env1  in
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
      let uu____8395 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____8443  ->
                fun uu____8444  ->
                  match (uu____8443, uu____8444) with
                  | ((tms,decls),(t,uu____8484)) ->
                      let uu____8511 = encode_term t env  in
                      (match uu____8511 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____8395 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____8568 = FStar_Syntax_Util.list_elements e  in
        match uu____8568 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____8599 =
          let uu____8616 = FStar_Syntax_Util.unmeta p  in
          FStar_All.pipe_right uu____8616 FStar_Syntax_Util.head_and_args  in
        match uu____8599 with
        | (head1,args) ->
            let uu____8667 =
              let uu____8682 =
                let uu____8683 = FStar_Syntax_Util.un_uinst head1  in
                uu____8683.FStar_Syntax_Syntax.n  in
              (uu____8682, args)  in
            (match uu____8667 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____8705,uu____8706)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____8758 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or1 t1 =
          let uu____8813 =
            let uu____8830 = FStar_Syntax_Util.unmeta t1  in
            FStar_All.pipe_right uu____8830 FStar_Syntax_Util.head_and_args
             in
          match uu____8813 with
          | (head1,args) ->
              let uu____8877 =
                let uu____8892 =
                  let uu____8893 = FStar_Syntax_Util.un_uinst head1  in
                  uu____8893.FStar_Syntax_Syntax.n  in
                (uu____8892, args)  in
              (match uu____8877 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____8912)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____8949 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____8979 = smt_pat_or1 t1  in
            (match uu____8979 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____9001 = list_elements1 e  in
                 FStar_All.pipe_right uu____9001
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____9031 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____9031
                           (FStar_List.map one_pat)))
             | uu____9054 ->
                 let uu____9059 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____9059])
        | uu____9110 ->
            let uu____9113 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____9113]
         in
      let uu____9164 =
        let uu____9179 =
          let uu____9180 = FStar_Syntax_Subst.compress t  in
          uu____9180.FStar_Syntax_Syntax.n  in
        match uu____9179 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____9219 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____9219 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____9254;
                        FStar_Syntax_Syntax.effect_name = uu____9255;
                        FStar_Syntax_Syntax.result_typ = uu____9256;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____9258)::(post,uu____9260)::(pats,uu____9262)::[];
                        FStar_Syntax_Syntax.flags = uu____9263;_}
                      ->
                      let uu____9324 = lemma_pats pats  in
                      (binders1, pre, post, uu____9324)
                  | uu____9335 -> failwith "impos"))
        | uu____9351 -> failwith "Impos"  in
      match uu____9164 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___366_9388 = env  in
            {
              FStar_SMTEncoding_Env.bvar_bindings =
                (uu___366_9388.FStar_SMTEncoding_Env.bvar_bindings);
              FStar_SMTEncoding_Env.fvar_bindings =
                (uu___366_9388.FStar_SMTEncoding_Env.fvar_bindings);
              FStar_SMTEncoding_Env.depth =
                (uu___366_9388.FStar_SMTEncoding_Env.depth);
              FStar_SMTEncoding_Env.tcenv =
                (uu___366_9388.FStar_SMTEncoding_Env.tcenv);
              FStar_SMTEncoding_Env.warn =
                (uu___366_9388.FStar_SMTEncoding_Env.warn);
              FStar_SMTEncoding_Env.cache =
                (uu___366_9388.FStar_SMTEncoding_Env.cache);
              FStar_SMTEncoding_Env.nolabels =
                (uu___366_9388.FStar_SMTEncoding_Env.nolabels);
              FStar_SMTEncoding_Env.use_zfuel_name = true;
              FStar_SMTEncoding_Env.encode_non_total_function_typ =
                (uu___366_9388.FStar_SMTEncoding_Env.encode_non_total_function_typ);
              FStar_SMTEncoding_Env.current_module_name =
                (uu___366_9388.FStar_SMTEncoding_Env.current_module_name);
              FStar_SMTEncoding_Env.encoding_quantifier =
                (uu___366_9388.FStar_SMTEncoding_Env.encoding_quantifier)
            }  in
          let uu____9390 =
            encode_binders FStar_Pervasives_Native.None binders env1  in
          (match uu____9390 with
           | (vars,guards,env2,decls,uu____9415) ->
               let uu____9428 = encode_smt_patterns patterns env2  in
               (match uu____9428 with
                | (pats,decls') ->
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
                    let env3 =
                      let uu___367_9461 = env2  in
                      {
                        FStar_SMTEncoding_Env.bvar_bindings =
                          (uu___367_9461.FStar_SMTEncoding_Env.bvar_bindings);
                        FStar_SMTEncoding_Env.fvar_bindings =
                          (uu___367_9461.FStar_SMTEncoding_Env.fvar_bindings);
                        FStar_SMTEncoding_Env.depth =
                          (uu___367_9461.FStar_SMTEncoding_Env.depth);
                        FStar_SMTEncoding_Env.tcenv =
                          (uu___367_9461.FStar_SMTEncoding_Env.tcenv);
                        FStar_SMTEncoding_Env.warn =
                          (uu___367_9461.FStar_SMTEncoding_Env.warn);
                        FStar_SMTEncoding_Env.cache =
                          (uu___367_9461.FStar_SMTEncoding_Env.cache);
                        FStar_SMTEncoding_Env.nolabels = true;
                        FStar_SMTEncoding_Env.use_zfuel_name =
                          (uu___367_9461.FStar_SMTEncoding_Env.use_zfuel_name);
                        FStar_SMTEncoding_Env.encode_non_total_function_typ =
                          (uu___367_9461.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                        FStar_SMTEncoding_Env.current_module_name =
                          (uu___367_9461.FStar_SMTEncoding_Env.current_module_name);
                        FStar_SMTEncoding_Env.encoding_quantifier =
                          (uu___367_9461.FStar_SMTEncoding_Env.encoding_quantifier)
                      }  in
                    let uu____9463 =
                      let uu____9468 = FStar_Syntax_Util.unmeta pre  in
                      encode_formula uu____9468 env3  in
                    (match uu____9463 with
                     | (pre1,decls'') ->
                         let uu____9475 =
                           let uu____9480 = FStar_Syntax_Util.unmeta post1
                              in
                           encode_formula uu____9480 env3  in
                         (match uu____9475 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append decls'
                                     (FStar_List.append decls'' decls'''))
                                 in
                              let uu____9490 =
                                let uu____9491 =
                                  let uu____9502 =
                                    let uu____9503 =
                                      let uu____9508 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards)
                                         in
                                      (uu____9508, post2)  in
                                    FStar_SMTEncoding_Util.mkImp uu____9503
                                     in
                                  (pats, vars, uu____9502)  in
                                FStar_SMTEncoding_Term.mkForall
                                  t.FStar_Syntax_Syntax.pos uu____9491
                                 in
                              (uu____9490, decls1)))))

and (encode_smt_patterns :
  FStar_Syntax_Syntax.arg Prims.list Prims.list ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term Prims.list Prims.list *
        FStar_SMTEncoding_Term.decl Prims.list))
  =
  fun pats_l  ->
    fun env  ->
      let env1 =
        let uu___368_9530 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___368_9530.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___368_9530.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___368_9530.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___368_9530.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___368_9530.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.cache =
            (uu___368_9530.FStar_SMTEncoding_Env.cache);
          FStar_SMTEncoding_Env.nolabels =
            (uu___368_9530.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___368_9530.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___368_9530.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___368_9530.FStar_SMTEncoding_Env.encoding_quantifier)
        }  in
      let encode_smt_pattern t =
        let uu____9546 = FStar_Syntax_Util.head_and_args t  in
        match uu____9546 with
        | (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____9609::(x,uu____9611)::(t1,uu____9613)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____9680 = encode_term x env1  in
                 (match uu____9680 with
                  | (x1,decls) ->
                      let uu____9691 = encode_term t1 env1  in
                      (match uu____9691 with
                       | (t2,decls') ->
                           let uu____9702 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                           (uu____9702, (FStar_List.append decls decls'))))
             | uu____9703 -> encode_term t env1)
         in
      FStar_List.fold_right
        (fun pats  ->
           fun uu____9746  ->
             match uu____9746 with
             | (pats_l1,decls) ->
                 let uu____9791 =
                   FStar_List.fold_right
                     (fun uu____9826  ->
                        fun uu____9827  ->
                          match (uu____9826, uu____9827) with
                          | ((p,uu____9869),(pats1,decls1)) ->
                              let uu____9904 = encode_smt_pattern p  in
                              (match uu____9904 with
                               | (t,d) ->
                                   let uu____9919 =
                                     FStar_SMTEncoding_Term.check_pattern_ok
                                       t
                                      in
                                   (match uu____9919 with
                                    | FStar_Pervasives_Native.None  ->
                                        ((t :: pats1),
                                          (FStar_List.append d decls1))
                                    | FStar_Pervasives_Native.Some
                                        illegal_subterm ->
                                        ((let uu____9936 =
                                            let uu____9942 =
                                              let uu____9944 =
                                                FStar_Syntax_Print.term_to_string
                                                  p
                                                 in
                                              let uu____9946 =
                                                FStar_SMTEncoding_Term.print_smt_term
                                                  illegal_subterm
                                                 in
                                              FStar_Util.format2
                                                "Pattern %s contains illegal sub-term (%s); dropping it"
                                                uu____9944 uu____9946
                                               in
                                            (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                                              uu____9942)
                                             in
                                          FStar_Errors.log_issue
                                            p.FStar_Syntax_Syntax.pos
                                            uu____9936);
                                         (pats1,
                                           (FStar_List.append d decls1))))))
                     pats ([], decls)
                    in
                 (match uu____9791 with
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
        let uu____10006 =
          FStar_All.pipe_left
            (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____10006
        then
          let uu____10011 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____10013 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10011 uu____10013
        else ()  in
      let enc f r l =
        let uu____10055 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10087 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____10087 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____10055 with
        | (decls,args) ->
            let uu____10118 =
              let uu___369_10119 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___369_10119.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___369_10119.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10118, decls)
         in
      let const_op f r uu____10154 =
        let uu____10167 = f r  in (uu____10167, [])  in
      let un_op f l =
        let uu____10190 = FStar_List.hd l  in
        FStar_All.pipe_left f uu____10190  in
      let bin_op f uu___360_10210 =
        match uu___360_10210 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10221 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____10262 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____10287  ->
                 match uu____10287 with
                 | (t,uu____10303) ->
                     let uu____10308 = encode_formula t env  in
                     (match uu____10308 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____10262 with
        | (decls,phis) ->
            let uu____10337 =
              let uu___370_10338 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___370_10338.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___370_10338.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10337, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____10401  ->
               match uu____10401 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____10422) -> false
                    | uu____10425 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____10444 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____10444
        else
          (let uu____10461 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____10461 r rf)
         in
      let eq3_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____10533 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::t1::v0::v1::[] ->
                     let uu____10565 =
                       let uu____10570 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____10571 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____10570, uu____10571)  in
                     FStar_SMTEncoding_Util.mkAnd uu____10565
                 | uu____10572 -> failwith "Impossible")
             in
          uu____10533 r args
        else
          (let uu____10578 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____10578)
         in
      let h_equals_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____10650 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::v0::t1::v1::[] ->
                     let uu____10682 =
                       let uu____10687 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____10688 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____10687, uu____10688)  in
                     FStar_SMTEncoding_Util.mkAnd uu____10682
                 | uu____10689 -> failwith "Impossible")
             in
          uu____10650 r args
        else
          (let uu____10695 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____10695)
         in
      let mk_imp1 r uu___361_10730 =
        match uu___361_10730 with
        | (lhs,uu____10736)::(rhs,uu____10738)::[] ->
            let uu____10779 = encode_formula rhs env  in
            (match uu____10779 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____10794) ->
                      (l1, decls1)
                  | uu____10799 ->
                      let uu____10800 = encode_formula lhs env  in
                      (match uu____10800 with
                       | (l2,decls2) ->
                           let uu____10811 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____10811, (FStar_List.append decls1 decls2)))))
        | uu____10812 -> failwith "impossible"  in
      let mk_ite r uu___362_10840 =
        match uu___362_10840 with
        | (guard,uu____10846)::(_then,uu____10848)::(_else,uu____10850)::[]
            ->
            let uu____10907 = encode_formula guard env  in
            (match uu____10907 with
             | (g,decls1) ->
                 let uu____10918 = encode_formula _then env  in
                 (match uu____10918 with
                  | (t,decls2) ->
                      let uu____10929 = encode_formula _else env  in
                      (match uu____10929 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____10941 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____10971 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l
           in
        f uu____10971  in
      let connectives =
        let uu____11001 =
          let uu____11026 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____11026)  in
        let uu____11069 =
          let uu____11096 =
            let uu____11121 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____11121)  in
          let uu____11164 =
            let uu____11191 =
              let uu____11218 =
                let uu____11243 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____11243)  in
              let uu____11286 =
                let uu____11313 =
                  let uu____11340 =
                    let uu____11365 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____11365)  in
                  [uu____11340;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.c_eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq3_op);
                  (FStar_Parser_Const.c_eq3_lid, h_equals_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11313  in
              uu____11218 :: uu____11286  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11191  in
          uu____11096 :: uu____11164  in
        uu____11001 :: uu____11069  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____11910 = encode_formula phi' env  in
            (match uu____11910 with
             | (phi2,decls) ->
                 let uu____11921 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____11921, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____11923 ->
            let uu____11930 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____11930 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____11969 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____11969 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____11981;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____11983;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____11985;
                 FStar_Syntax_Syntax.lbpos = uu____11986;_}::[]),e2)
            ->
            let uu____12013 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____12013 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____12066::(x,uu____12068)::(t,uu____12070)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12137 = encode_term x env  in
                 (match uu____12137 with
                  | (x1,decls) ->
                      let uu____12148 = encode_term t env  in
                      (match uu____12148 with
                       | (t1,decls') ->
                           let uu____12159 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____12159, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12162)::(msg,uu____12164)::(phi2,uu____12166)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12233 =
                   let uu____12238 =
                     let uu____12239 = FStar_Syntax_Subst.compress r  in
                     uu____12239.FStar_Syntax_Syntax.n  in
                   let uu____12242 =
                     let uu____12243 = FStar_Syntax_Subst.compress msg  in
                     uu____12243.FStar_Syntax_Syntax.n  in
                   (uu____12238, uu____12242)  in
                 (match uu____12233 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12252))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____12263 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____12270)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____12305 when head_redex env head2 ->
                 let uu____12320 = whnf env phi1  in
                 encode_formula uu____12320 env
             | uu____12321 ->
                 let uu____12336 = encode_term phi1 env  in
                 (match uu____12336 with
                  | (tt,decls) ->
                      let tt1 =
                        let uu____12348 =
                          let uu____12350 =
                            FStar_Range.use_range
                              tt.FStar_SMTEncoding_Term.rng
                             in
                          let uu____12351 =
                            FStar_Range.use_range
                              phi1.FStar_Syntax_Syntax.pos
                             in
                          FStar_Range.rng_included uu____12350 uu____12351
                           in
                        if uu____12348
                        then tt
                        else
                          (let uu___371_12355 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___371_12355.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___371_12355.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      let uu____12356 = FStar_SMTEncoding_Term.mk_Valid tt1
                         in
                      (uu____12356, decls)))
        | uu____12357 ->
            let uu____12358 = encode_term phi1 env  in
            (match uu____12358 with
             | (tt,decls) ->
                 let tt1 =
                   let uu____12370 =
                     let uu____12372 =
                       FStar_Range.use_range tt.FStar_SMTEncoding_Term.rng
                        in
                     let uu____12373 =
                       FStar_Range.use_range phi1.FStar_Syntax_Syntax.pos  in
                     FStar_Range.rng_included uu____12372 uu____12373  in
                   if uu____12370
                   then tt
                   else
                     (let uu___372_12377 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___372_12377.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___372_12377.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 let uu____12378 = FStar_SMTEncoding_Term.mk_Valid tt1  in
                 (uu____12378, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____12422 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____12422 with
        | (vars,guards,env2,decls,uu____12461) ->
            let uu____12474 = encode_smt_patterns ps env2  in
            (match uu____12474 with
             | (pats,decls') ->
                 let uu____12517 = encode_formula body env2  in
                 (match uu____12517 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12549;
                             FStar_SMTEncoding_Term.rng = uu____12550;_}::[])::[]
                            when
                            let uu____12567 =
                              FStar_Ident.text_of_lid
                                FStar_Parser_Const.guard_free
                               in
                            uu____12567 = gf -> []
                        | uu____12570 -> guards  in
                      let uu____12575 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____12575, body1,
                        (FStar_List.append decls
                           (FStar_List.append decls' decls'')))))
         in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi  in
       let uu____12586 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____12586 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12595 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____12701  ->
                     match uu____12701 with
                     | (l,uu____12726) -> FStar_Ident.lid_equals op l))
              in
           (match uu____12595 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____12795,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____12887 = encode_q_body env vars pats body  in
             match uu____12887 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____12932 =
                     let uu____12943 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____12943)  in
                   FStar_SMTEncoding_Term.mkForall
                     phi1.FStar_Syntax_Syntax.pos uu____12932
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____12974 = encode_q_body env vars pats body  in
             match uu____12974 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____13018 =
                   let uu____13019 =
                     let uu____13030 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____13030)  in
                   FStar_SMTEncoding_Term.mkExists
                     phi1.FStar_Syntax_Syntax.pos uu____13019
                    in
                 (uu____13018, decls))))
