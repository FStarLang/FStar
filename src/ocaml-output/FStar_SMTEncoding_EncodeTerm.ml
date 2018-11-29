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
  
let (is_app : FStar_SMTEncoding_Term.op -> Prims.bool) =
  fun uu___361_651  ->
    match uu___361_651 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____657 -> false
  
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
                       FStar_SMTEncoding_Term.freevars = uu____705;
                       FStar_SMTEncoding_Term.rng = uu____706;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____731) ->
              let uu____741 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____755 -> false) args (FStar_List.rev xs))
                 in
              if uu____741
              then FStar_SMTEncoding_Env.tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____762,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t  in
              let uu____766 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____774 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars
                           in
                        Prims.op_Negation uu____774))
                 in
              if uu____766
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____781 -> FStar_Pervasives_Native.None  in
        check_partial_applications body (FStar_List.rev vars)
  
let check_pattern_vars :
  'Auu____799 'Auu____800 .
    FStar_SMTEncoding_Env.env_t ->
      (FStar_Syntax_Syntax.bv * 'Auu____799) Prims.list ->
        (FStar_Syntax_Syntax.term * 'Auu____800) Prims.list -> unit
  =
  fun env  ->
    fun vars  ->
      fun pats  ->
        let pats1 =
          FStar_All.pipe_right pats
            (FStar_List.map
               (fun uu____858  ->
                  match uu____858 with
                  | (x,uu____864) ->
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
              let uu____872 = FStar_Syntax_Free.names hd1  in
              FStar_List.fold_left
                (fun out  ->
                   fun x  ->
                     let uu____884 = FStar_Syntax_Free.names x  in
                     FStar_Util.set_union out uu____884) uu____872 tl1
               in
            let uu____887 =
              FStar_All.pipe_right vars
                (FStar_Util.find_opt
                   (fun uu____914  ->
                      match uu____914 with
                      | (b,uu____921) ->
                          let uu____922 = FStar_Util.set_mem b pat_vars  in
                          Prims.op_Negation uu____922))
               in
            (match uu____887 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some (x,uu____929) ->
                 let pos =
                   FStar_List.fold_left
                     (fun out  ->
                        fun t  ->
                          FStar_Range.union_ranges out
                            t.FStar_Syntax_Syntax.pos)
                     hd1.FStar_Syntax_Syntax.pos tl1
                    in
                 let uu____943 =
                   let uu____949 =
                     let uu____951 = FStar_Syntax_Print.bv_to_string x  in
                     FStar_Util.format1
                       "SMT pattern misses at least one bound variable: %s"
                       uu____951
                      in
                   (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                     uu____949)
                    in
                 FStar_Errors.log_issue pos uu____943)
  
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
        | FStar_Syntax_Syntax.Tm_arrow uu____1237 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____1252 ->
            let uu____1259 = FStar_Syntax_Util.unrefine t1  in
            aux true uu____1259
        | uu____1261 ->
            if norm1
            then let uu____1263 = whnf env t1  in aux false uu____1263
            else
              (let uu____1267 =
                 let uu____1269 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let uu____1271 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____1269 uu____1271
                  in
               failwith uu____1267)
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
    | FStar_Syntax_Syntax.Tm_refine (bv,uu____1313) ->
        curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort
    | uu____1318 ->
        let uu____1319 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____1319)
  
let is_arithmetic_primitive :
  'Auu____1333 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____1333 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1356::uu____1357::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1361::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____1364 -> false
  
let (isInteger : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____1395 -> false
  
let (getInteger : FStar_Syntax_Syntax.term' -> Prims.int) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____1418 -> failwith "Expected an Integer term"
  
let is_BitVector_primitive :
  'Auu____1428 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____1428)
        Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____1470)::uu____1471::uu____1472::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____1523)::uu____1524::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____1561 -> false
  
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
          let uu____1879 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue  in
          (uu____1879, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____1881 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse  in
          (uu____1881, [])
      | FStar_Const.Const_char c1 ->
          let uu____1884 =
            let uu____1885 =
              let uu____1893 =
                let uu____1896 =
                  let uu____1897 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1)
                     in
                  FStar_SMTEncoding_Term.boxInt uu____1897  in
                [uu____1896]  in
              ("FStar.Char.__char_of_int", uu____1893)  in
            FStar_SMTEncoding_Util.mkApp uu____1885  in
          (uu____1884, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____1915 =
            let uu____1916 = FStar_SMTEncoding_Util.mkInteger i  in
            FStar_SMTEncoding_Term.boxInt uu____1916  in
          (uu____1915, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.FStar_SMTEncoding_Env.tcenv).FStar_TypeChecker_Env.dsenv
              repr sw FStar_Range.dummyRange
             in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____1937) ->
          let uu____1940 =
            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.string_const s
             in
          (uu____1940, [])
      | FStar_Const.Const_range uu____1941 ->
          let uu____1942 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          (uu____1942, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | c1 ->
          let uu____1944 =
            let uu____1946 = FStar_Syntax_Print.const_to_string c1  in
            FStar_Util.format1 "Unhandled constant: %s" uu____1946  in
          failwith uu____1944

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
        (let uu____1975 =
           FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
             FStar_Options.Medium
            in
         if uu____1975
         then
           let uu____1978 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____1978
         else ());
        (let uu____1984 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2081  ->
                   fun b  ->
                     match uu____2081 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2166 =
                           let x = FStar_Pervasives_Native.fst b  in
                           let uu____2187 =
                             FStar_SMTEncoding_Env.gen_term_var env1 x  in
                           match uu____2187 with
                           | (xxsym,xx,env') ->
                               let uu____2217 =
                                 let uu____2222 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____2222 env1 xx
                                  in
                               (match uu____2217 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x))
                            in
                         (match uu____2166 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____1984 with
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
          let uu____2396 = encode_term t env  in
          match uu____2396 with
          | (t1,decls) ->
              let uu____2407 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____2407, decls)

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
          let uu____2418 = encode_term t env  in
          match uu____2418 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____2433 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____2433, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____2435 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____2435, decls))

and (encode_arith_term :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____2441 = encode_args args_e env  in
        match uu____2441 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____2460 -> failwith "Impossible"  in
            let unary arg_tms1 =
              let uu____2472 = FStar_List.hd arg_tms1  in
              FStar_SMTEncoding_Term.unboxInt uu____2472  in
            let binary arg_tms1 =
              let uu____2487 =
                let uu____2488 = FStar_List.hd arg_tms1  in
                FStar_SMTEncoding_Term.unboxInt uu____2488  in
              let uu____2489 =
                let uu____2490 =
                  let uu____2491 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____2491  in
                FStar_SMTEncoding_Term.unboxInt uu____2490  in
              (uu____2487, uu____2489)  in
            let mk_default uu____2499 =
              let uu____2500 =
                FStar_SMTEncoding_Env.lookup_free_var_sym env
                  head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____2500 with
              | (fname,fuel_args,arity) ->
                  let args = FStar_List.append fuel_args arg_tms  in
                  maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity
                    args
               in
            let mk_l op mk_args ts =
              let uu____2565 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____2565
              then
                let uu____2568 =
                  let uu____2569 = mk_args ts  in op uu____2569  in
                FStar_All.pipe_right uu____2568 FStar_SMTEncoding_Term.boxInt
              else mk_default ()  in
            let mk_nl nm op ts =
              let uu____2607 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____2607
              then
                let uu____2610 = binary ts  in
                match uu____2610 with
                | (t1,t2) ->
                    let uu____2617 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____2617
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____2623 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____2623
                 then
                   let uu____2626 =
                     let uu____2627 = binary ts  in op uu____2627  in
                   FStar_All.pipe_right uu____2626
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
            let uu____2792 =
              let uu____2802 =
                FStar_List.tryFind
                  (fun uu____2826  ->
                     match uu____2826 with
                     | (l,uu____2837) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____2802 FStar_Util.must  in
            (match uu____2792 with
             | (uu____2881,op) ->
                 let uu____2893 = op arg_tms  in (uu____2893, decls))

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
        let uu____2901 = FStar_List.hd args_e  in
        match uu____2901 with
        | (tm_sz,uu____2909) ->
            let uu____2918 = uu____2901  in
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let uu____2927 =
                FStar_Util.smap_try_find env.FStar_SMTEncoding_Env.cache
                  sz_key
                 in
              match uu____2927 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None  ->
                  let t_decls1 = FStar_SMTEncoding_Term.mkBvConstructor sz
                     in
                  ((let uu____2935 =
                      FStar_SMTEncoding_Env.mk_cache_entry env "" [] []  in
                    FStar_Util.smap_add env.FStar_SMTEncoding_Env.cache
                      sz_key uu____2935);
                   t_decls1)
               in
            let uu____2937 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____2963::(sz_arg,uu____2965)::uu____2966::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____3033 =
                    let uu____3034 = FStar_List.tail args_e  in
                    FStar_List.tail uu____3034  in
                  let uu____3037 =
                    let uu____3041 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____3041  in
                  (uu____3033, uu____3037)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____3048::(sz_arg,uu____3050)::uu____3051::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____3118 =
                    let uu____3120 = FStar_Syntax_Print.term_to_string sz_arg
                       in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____3120
                     in
                  failwith uu____3118
              | uu____3130 ->
                  let uu____3145 = FStar_List.tail args_e  in
                  (uu____3145, FStar_Pervasives_Native.None)
               in
            (match uu____2937 with
             | (arg_tms,ext_sz) ->
                 let uu____3164 = encode_args arg_tms env  in
                 (match uu____3164 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____3185 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____3197 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____3197  in
                      let unary_arith arg_tms2 =
                        let uu____3208 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____3208  in
                      let binary arg_tms2 =
                        let uu____3223 =
                          let uu____3224 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3224
                           in
                        let uu____3225 =
                          let uu____3226 =
                            let uu____3227 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____3227  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3226
                           in
                        (uu____3223, uu____3225)  in
                      let binary_arith arg_tms2 =
                        let uu____3244 =
                          let uu____3245 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3245
                           in
                        let uu____3246 =
                          let uu____3247 =
                            let uu____3248 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____3248  in
                          FStar_SMTEncoding_Term.unboxInt uu____3247  in
                        (uu____3244, uu____3246)  in
                      let mk_bv op mk_args resBox ts =
                        let uu____3306 =
                          let uu____3307 = mk_args ts  in op uu____3307  in
                        FStar_All.pipe_right uu____3306 resBox  in
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
                        let uu____3439 =
                          let uu____3444 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____3444  in
                        let uu____3453 =
                          let uu____3458 =
                            let uu____3460 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____3460  in
                          FStar_SMTEncoding_Term.boxBitVec uu____3458  in
                        mk_bv uu____3439 unary uu____3453 arg_tms2  in
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
                      let uu____3700 =
                        let uu____3710 =
                          FStar_List.tryFind
                            (fun uu____3734  ->
                               match uu____3734 with
                               | (l,uu____3745) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____3710 FStar_Util.must  in
                      (match uu____3700 with
                       | (uu____3791,op) ->
                           let uu____3803 = op arg_tms1  in
                           (uu____3803, (FStar_List.append sz_decls decls)))))

and (encode_deeply_embedded_quantifier :
  FStar_Syntax_Syntax.term ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let env1 =
        let uu___369_3813 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___369_3813.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___369_3813.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___369_3813.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___369_3813.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___369_3813.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.cache =
            (uu___369_3813.FStar_SMTEncoding_Env.cache);
          FStar_SMTEncoding_Env.nolabels =
            (uu___369_3813.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name =
            (uu___369_3813.FStar_SMTEncoding_Env.use_zfuel_name);
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___369_3813.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___369_3813.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier = true
        }  in
      let uu____3815 = encode_term t env1  in
      match uu____3815 with
      | (tm,decls) ->
          let vars = FStar_SMTEncoding_Term.free_variables tm  in
          let valid_tm = FStar_SMTEncoding_Term.mk_Valid tm  in
          let key =
            FStar_SMTEncoding_Term.mkForall t.FStar_Syntax_Syntax.pos
              ([], vars, valid_tm)
             in
          let tkey_hash = FStar_SMTEncoding_Term.hash_of_term key  in
          let uu____3837 =
            FStar_Util.smap_try_find env1.FStar_SMTEncoding_Env.cache
              tkey_hash
             in
          (match uu____3837 with
           | FStar_Pervasives_Native.Some uu____3844 -> (tm, decls)
           | uu____3845 ->
               (match tm.FStar_SMTEncoding_Term.tm with
                | FStar_SMTEncoding_Term.App
                    (uu____3852,{
                                  FStar_SMTEncoding_Term.tm =
                                    FStar_SMTEncoding_Term.FreeV uu____3853;
                                  FStar_SMTEncoding_Term.freevars =
                                    uu____3854;
                                  FStar_SMTEncoding_Term.rng = uu____3855;_}::
                     {
                       FStar_SMTEncoding_Term.tm =
                         FStar_SMTEncoding_Term.FreeV uu____3856;
                       FStar_SMTEncoding_Term.freevars = uu____3857;
                       FStar_SMTEncoding_Term.rng = uu____3858;_}::[])
                    ->
                    (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
                       (FStar_Errors.Warning_QuantifierWithoutPattern,
                         "Not encoding deeply embedded, unguarded quantifier to SMT");
                     (tm, decls))
                | uu____3892 ->
                    let uu____3893 = encode_formula t env1  in
                    (match uu____3893 with
                     | (phi,decls') ->
                         let interp =
                           match vars with
                           | [] ->
                               let uu____3910 =
                                 let uu____3915 =
                                   FStar_SMTEncoding_Term.mk_Valid tm  in
                                 (uu____3915, phi)  in
                               FStar_SMTEncoding_Util.mkIff uu____3910
                           | uu____3916 ->
                               let uu____3917 =
                                 let uu____3928 =
                                   let uu____3929 =
                                     let uu____3934 =
                                       FStar_SMTEncoding_Term.mk_Valid tm  in
                                     (uu____3934, phi)  in
                                   FStar_SMTEncoding_Util.mkIff uu____3929
                                    in
                                 ([[valid_tm]], vars, uu____3928)  in
                               FStar_SMTEncoding_Term.mkForall
                                 t.FStar_Syntax_Syntax.pos uu____3917
                            in
                         let ax =
                           let uu____3944 =
                             let uu____3952 =
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 "l_quant_interp"
                                in
                             (interp,
                               (FStar_Pervasives_Native.Some
                                  "Interpretation of deeply embedded quantifier"),
                               uu____3952)
                              in
                           FStar_SMTEncoding_Util.mkAssume uu____3944  in
                         ((let uu____3959 =
                             FStar_SMTEncoding_Env.mk_cache_entry env1 "" []
                               [ax]
                              in
                           FStar_Util.smap_add
                             env1.FStar_SMTEncoding_Env.cache tkey_hash
                             uu____3959);
                          (tm,
                            (FStar_List.append decls
                               (FStar_List.append decls' [ax])))))))

and (encode_term :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____3969 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____3969
       then
         let uu____3974 = FStar_Syntax_Print.tag_of_term t  in
         let uu____3976 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____3978 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____3974 uu____3976
           uu____3978
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____3987 ->
           let uu____4010 =
             let uu____4012 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____4015 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____4017 = FStar_Syntax_Print.term_to_string t0  in
             let uu____4019 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____4012
               uu____4015 uu____4017 uu____4019
              in
           failwith uu____4010
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____4026 =
             let uu____4028 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____4031 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____4033 = FStar_Syntax_Print.term_to_string t0  in
             let uu____4035 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____4028
               uu____4031 uu____4033 uu____4035
              in
           failwith uu____4026
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let e = FStar_Syntax_Util.unfold_lazy i  in
           ((let uu____4045 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____4045
             then
               let uu____4050 = FStar_Syntax_Print.term_to_string t0  in
               let uu____4052 = FStar_Syntax_Print.term_to_string e  in
               FStar_Util.print2 ">> Unfolded (%s) ~> (%s)\n" uu____4050
                 uu____4052
             else ());
            encode_term e env)
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____4058 =
             let uu____4060 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____4060
              in
           failwith uu____4058
       | FStar_Syntax_Syntax.Tm_ascribed (t1,(k,uu____4069),uu____4070) ->
           let uu____4119 =
             match k with
             | FStar_Util.Inl t2 -> FStar_Syntax_Util.is_unit t2
             | uu____4129 -> false  in
           if uu____4119
           then (FStar_SMTEncoding_Term.mk_Term_unit, [])
           else encode_term t1 env
       | FStar_Syntax_Syntax.Tm_quoted (qt,uu____4147) ->
           let tv =
             let uu____4153 =
               let uu____4160 = FStar_Reflection_Basic.inspect_ln qt  in
               FStar_Syntax_Embeddings.embed
                 FStar_Reflection_Embeddings.e_term_view uu____4160
                in
             uu____4153 t.FStar_Syntax_Syntax.pos
               FStar_Pervasives_Native.None
               FStar_Syntax_Embeddings.id_norm_cb
              in
           ((let uu____4187 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding")
                in
             if uu____4187
             then
               let uu____4192 = FStar_Syntax_Print.term_to_string t0  in
               let uu____4194 = FStar_Syntax_Print.term_to_string tv  in
               FStar_Util.print2 ">> Inspected (%s) ~> (%s)\n" uu____4192
                 uu____4194
             else ());
            (let t1 =
               let uu____4202 =
                 let uu____4213 = FStar_Syntax_Syntax.as_arg tv  in
                 [uu____4213]  in
               FStar_Syntax_Util.mk_app
                 (FStar_Reflection_Data.refl_constant_term
                    FStar_Reflection_Data.fstar_refl_pack_ln) uu____4202
                in
             encode_term t1 env))
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_pattern uu____4239) ->
           encode_term t1
             (let uu___370_4257 = env  in
              {
                FStar_SMTEncoding_Env.bvar_bindings =
                  (uu___370_4257.FStar_SMTEncoding_Env.bvar_bindings);
                FStar_SMTEncoding_Env.fvar_bindings =
                  (uu___370_4257.FStar_SMTEncoding_Env.fvar_bindings);
                FStar_SMTEncoding_Env.depth =
                  (uu___370_4257.FStar_SMTEncoding_Env.depth);
                FStar_SMTEncoding_Env.tcenv =
                  (uu___370_4257.FStar_SMTEncoding_Env.tcenv);
                FStar_SMTEncoding_Env.warn =
                  (uu___370_4257.FStar_SMTEncoding_Env.warn);
                FStar_SMTEncoding_Env.cache =
                  (uu___370_4257.FStar_SMTEncoding_Env.cache);
                FStar_SMTEncoding_Env.nolabels =
                  (uu___370_4257.FStar_SMTEncoding_Env.nolabels);
                FStar_SMTEncoding_Env.use_zfuel_name =
                  (uu___370_4257.FStar_SMTEncoding_Env.use_zfuel_name);
                FStar_SMTEncoding_Env.encode_non_total_function_typ =
                  (uu___370_4257.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                FStar_SMTEncoding_Env.current_module_name =
                  (uu___370_4257.FStar_SMTEncoding_Env.current_module_name);
                FStar_SMTEncoding_Env.encoding_quantifier = false
              })
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____4260) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = FStar_SMTEncoding_Env.lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____4268 = head_redex env t  in
           if uu____4268
           then let uu____4275 = whnf env t  in encode_term uu____4275 env
           else
             (let uu____4278 =
                FStar_SMTEncoding_Env.lookup_free_var_name env
                  v1.FStar_Syntax_Syntax.fv_name
                 in
              match uu____4278 with
              | (uu____4289,arity) ->
                  let tok =
                    FStar_SMTEncoding_Env.lookup_free_var env
                      v1.FStar_Syntax_Syntax.fv_name
                     in
                  let aux_decls =
                    if arity > (Prims.parse_int "0")
                    then
                      match tok.FStar_SMTEncoding_Term.tm with
                      | FStar_SMTEncoding_Term.FreeV uu____4299 ->
                          let uu____4305 =
                            let uu____4306 =
                              let uu____4314 =
                                FStar_SMTEncoding_Term.kick_partial_app tok
                                 in
                              let uu____4315 =
                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                  "@kick_partial_app"
                                 in
                              (uu____4314,
                                (FStar_Pervasives_Native.Some
                                   "kick_partial_app"), uu____4315)
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____4306  in
                          [uu____4305]
                      | FStar_SMTEncoding_Term.App (uu____4321,[]) ->
                          let uu____4324 =
                            let uu____4325 =
                              let uu____4333 =
                                FStar_SMTEncoding_Term.kick_partial_app tok
                                 in
                              let uu____4334 =
                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                  "@kick_partial_app"
                                 in
                              (uu____4333,
                                (FStar_Pervasives_Native.Some
                                   "kick_partial_app"), uu____4334)
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____4325  in
                          [uu____4324]
                      | uu____4340 -> []
                    else []  in
                  (tok, aux_decls))
       | FStar_Syntax_Syntax.Tm_type uu____4343 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4345) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.FStar_SMTEncoding_Env.current_module_name
              in
           let uu____4375 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____4375 with
            | (binders1,res) ->
                let uu____4386 =
                  (env.FStar_SMTEncoding_Env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____4386
                then
                  let uu____4393 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____4393 with
                   | (vars,guards,env',decls,uu____4418) ->
                       let fsym =
                         let uu____4437 =
                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                             "f"
                            in
                         (uu____4437, FStar_SMTEncoding_Term.Term_sort)  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____4443 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___371_4452 =
                              env.FStar_SMTEncoding_Env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___371_4452.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___371_4452.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___371_4452.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___371_4452.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___371_4452.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___371_4452.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___371_4452.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___371_4452.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___371_4452.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___371_4452.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___371_4452.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___371_4452.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___371_4452.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___371_4452.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___371_4452.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___371_4452.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___371_4452.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___371_4452.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___371_4452.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___371_4452.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___371_4452.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___371_4452.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___371_4452.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___371_4452.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___371_4452.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___371_4452.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___371_4452.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___371_4452.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___371_4452.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___371_4452.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___371_4452.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___371_4452.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___371_4452.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___371_4452.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___371_4452.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___371_4452.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___371_4452.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___371_4452.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___371_4452.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___371_4452.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___371_4452.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___371_4452.FStar_TypeChecker_Env.nbe)
                            }) res
                          in
                       (match uu____4443 with
                        | (pre_opt,res_t) ->
                            let uu____4464 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____4464 with
                             | (res_pred,decls') ->
                                 let uu____4475 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____4488 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____4488, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____4492 =
                                         encode_formula pre env'  in
                                       (match uu____4492 with
                                        | (guard,decls0) ->
                                            let uu____4505 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____4505, decls0))
                                    in
                                 (match uu____4475 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____4519 =
                                          let uu____4530 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____4530)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t.FStar_Syntax_Syntax.pos
                                          uu____4519
                                         in
                                      let cvars =
                                        let uu____4547 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____4547
                                          (FStar_List.filter
                                             (fun uu____4577  ->
                                                match uu____4577 with
                                                | (x,uu____4585) ->
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
                                      let uu____4604 =
                                        FStar_Util.smap_try_find
                                          env.FStar_SMTEncoding_Env.cache
                                          tkey_hash
                                         in
                                      (match uu____4604 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____4612 =
                                             let uu____4613 =
                                               let uu____4621 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV)
                                                  in
                                               ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                                 uu____4621)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4613
                                              in
                                           (uu____4612,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (FStar_SMTEncoding_Env.use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____4643 =
                                               let uu____4645 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____4645
                                                in
                                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                               uu____4643
                                              in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars
                                              in
                                           let caption =
                                             let uu____4658 =
                                               FStar_Options.log_queries ()
                                                in
                                             if uu____4658
                                             then
                                               let uu____4661 =
                                                 let uu____4663 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env.FStar_SMTEncoding_Env.tcenv
                                                     t0
                                                    in
                                                 FStar_Util.replace_char
                                                   uu____4663 10 32
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____4661
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
                                             let uu____4676 =
                                               let uu____4684 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars
                                                  in
                                               (tsym, uu____4684)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4676
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
                                             let uu____4700 =
                                               let uu____4708 =
                                                 FStar_SMTEncoding_Term.mkForall
                                                   t0.FStar_Syntax_Syntax.pos
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind)
                                                  in
                                               (uu____4708,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name)
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4700
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
                                             let uu____4725 =
                                               let uu____4733 =
                                                 let uu____4734 =
                                                   let uu____4745 =
                                                     let uu____4746 =
                                                       let uu____4751 =
                                                         let uu____4752 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f
                                                            in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____4752
                                                          in
                                                       (f_has_t, uu____4751)
                                                        in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____4746
                                                      in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____4745)
                                                    in
                                                 let uu____4767 =
                                                   mkForall_fuel
                                                     t0.FStar_Syntax_Syntax.pos
                                                    in
                                                 uu____4767 uu____4734  in
                                               (uu____4733,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4725
                                              in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym
                                                in
                                             let uu____4790 =
                                               let uu____4798 =
                                                 let uu____4799 =
                                                   let uu____4810 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp)
                                                      in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____4810)
                                                    in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   t0.FStar_Syntax_Syntax.pos
                                                   uu____4799
                                                  in
                                               (uu____4798,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4790
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
                                           ((let uu____4831 =
                                               FStar_SMTEncoding_Env.mk_cache_entry
                                                 env tsym cvar_sorts t_decls1
                                                in
                                             FStar_Util.smap_add
                                               env.FStar_SMTEncoding_Env.cache
                                               tkey_hash uu____4831);
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
                     let uu____4850 =
                       let uu____4858 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____4858,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____4850  in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)  in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym  in
                     let uu____4877 =
                       let uu____4885 =
                         let uu____4886 =
                           let uu____4897 =
                             let uu____4898 =
                               let uu____4903 =
                                 let uu____4904 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____4904
                                  in
                               (f_has_t, uu____4903)  in
                             FStar_SMTEncoding_Util.mkImp uu____4898  in
                           ([[f_has_t]], [fsym], uu____4897)  in
                         let uu____4924 =
                           mkForall_fuel t0.FStar_Syntax_Syntax.pos  in
                         uu____4924 uu____4886  in
                       (uu____4885, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____4877  in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____4942 ->
           let uu____4949 =
             let uu____4954 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Env.Weak;
                 FStar_TypeChecker_Env.HNF;
                 FStar_TypeChecker_Env.EraseUniverses]
                 env.FStar_SMTEncoding_Env.tcenv t0
                in
             match uu____4954 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____4961;
                 FStar_Syntax_Syntax.vars = uu____4962;_} ->
                 let uu____4969 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____4969 with
                  | (b,f1) ->
                      let uu____4994 =
                        let uu____4995 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____4995  in
                      (uu____4994, f1))
             | uu____5010 -> failwith "impossible"  in
           (match uu____4949 with
            | (x,f) ->
                let uu____5022 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____5022 with
                 | (base_t,decls) ->
                     let uu____5033 =
                       FStar_SMTEncoding_Env.gen_term_var env x  in
                     (match uu____5033 with
                      | (x1,xtm,env') ->
                          let uu____5050 = encode_formula f env'  in
                          (match uu____5050 with
                           | (refinement,decls') ->
                               let uu____5061 =
                                 FStar_SMTEncoding_Env.fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____5061 with
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
                                      let uu____5086 =
                                        let uu____5094 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____5102 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____5094
                                          uu____5102
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____5086
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____5150  ->
                                              match uu____5150 with
                                              | (y,uu____5158) ->
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
                                    let uu____5196 =
                                      FStar_Util.smap_try_find
                                        env.FStar_SMTEncoding_Env.cache
                                        tkey_hash
                                       in
                                    (match uu____5196 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____5204 =
                                           let uu____5205 =
                                             let uu____5213 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV)
                                                in
                                             ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                               uu____5213)
                                              in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____5205
                                            in
                                         (uu____5204,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (FStar_SMTEncoding_Env.use_cache_entry
                                                    cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.FStar_SMTEncoding_Env.current_module_name
                                            in
                                         let tsym =
                                           let uu____5237 =
                                             let uu____5239 =
                                               let uu____5241 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____5241
                                                in
                                             Prims.strcat module_name
                                               uu____5239
                                              in
                                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                             uu____5237
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
                                           let uu____5259 =
                                             let uu____5267 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1
                                                in
                                             (tsym, uu____5267)  in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____5259
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
                                           let uu____5284 =
                                             let uu____5292 =
                                               let uu____5293 =
                                                 let uu____5304 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base)
                                                    in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____5304)
                                                  in
                                               FStar_SMTEncoding_Term.mkForall
                                                 t0.FStar_Syntax_Syntax.pos
                                                 uu____5293
                                                in
                                             (uu____5292,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____5284
                                            in
                                         let t_kinding =
                                           let uu____5318 =
                                             let uu____5326 =
                                               FStar_SMTEncoding_Term.mkForall
                                                 t0.FStar_Syntax_Syntax.pos
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind)
                                                in
                                             (uu____5326,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____5318
                                            in
                                         let t_interp =
                                           let uu____5340 =
                                             let uu____5348 =
                                               let uu____5349 =
                                                 let uu____5360 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding)
                                                    in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____5360)
                                                  in
                                               FStar_SMTEncoding_Term.mkForall
                                                 t0.FStar_Syntax_Syntax.pos
                                                 uu____5349
                                                in
                                             (uu____5348,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement_interpretation"),
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____5340
                                            in
                                         let t_decls1 =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1])
                                            in
                                         ((let uu____5387 =
                                             FStar_SMTEncoding_Env.mk_cache_entry
                                               env tsym cvar_sorts t_decls1
                                              in
                                           FStar_Util.smap_add
                                             env.FStar_SMTEncoding_Env.cache
                                             tkey_hash uu____5387);
                                          (t1, t_decls1))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,uu____5389) ->
           let ttm =
             let uu____5407 =
               FStar_Syntax_Unionfind.uvar_id
                 uv.FStar_Syntax_Syntax.ctx_uvar_head
                in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____5407  in
           let uu____5409 =
             encode_term_pred FStar_Pervasives_Native.None
               uv.FStar_Syntax_Syntax.ctx_uvar_typ env ttm
              in
           (match uu____5409 with
            | (t_has_k,decls) ->
                let d =
                  let uu____5421 =
                    let uu____5429 =
                      let uu____5431 =
                        let uu____5433 =
                          let uu____5435 =
                            FStar_Syntax_Unionfind.uvar_id
                              uv.FStar_Syntax_Syntax.ctx_uvar_head
                             in
                          FStar_Util.string_of_int uu____5435  in
                        FStar_Util.format1 "uvar_typing_%s" uu____5433  in
                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                        uu____5431
                       in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____5429)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____5421  in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____5441 ->
           let uu____5458 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____5458 with
            | (head1,args_e) ->
                let uu____5505 =
                  let uu____5520 =
                    let uu____5521 = FStar_Syntax_Subst.compress head1  in
                    uu____5521.FStar_Syntax_Syntax.n  in
                  (uu____5520, args_e)  in
                (match uu____5505 with
                 | uu____5538 when head_redex env head1 ->
                     let uu____5553 = whnf env t  in
                     encode_term uu____5553 env
                 | uu____5554 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____5577 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5595) when
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
                       FStar_Syntax_Syntax.pos = uu____5617;
                       FStar_Syntax_Syntax.vars = uu____5618;_},uu____5619),uu____5620)
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
                       FStar_Syntax_Syntax.pos = uu____5646;
                       FStar_Syntax_Syntax.vars = uu____5647;_},uu____5648),
                    (v0,uu____5650)::(v1,uu____5652)::(v2,uu____5654)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____5725 = encode_term v0 env  in
                     (match uu____5725 with
                      | (v01,decls0) ->
                          let uu____5736 = encode_term v1 env  in
                          (match uu____5736 with
                           | (v11,decls1) ->
                               let uu____5747 = encode_term v2 env  in
                               (match uu____5747 with
                                | (v21,decls2) ->
                                    let uu____5758 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____5758,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(v0,uu____5761)::(v1,uu____5763)::(v2,uu____5765)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____5832 = encode_term v0 env  in
                     (match uu____5832 with
                      | (v01,decls0) ->
                          let uu____5843 = encode_term v1 env  in
                          (match uu____5843 with
                           | (v11,decls1) ->
                               let uu____5854 = encode_term v2 env  in
                               (match uu____5854 with
                                | (v21,decls2) ->
                                    let uu____5865 =
                                      FStar_SMTEncoding_Util.mk_LexCons v01
                                        v11 v21
                                       in
                                    (uu____5865,
                                      (FStar_List.append decls0
                                         (FStar_List.append decls1 decls2))))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____5867)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____5903)::(rng,uu____5905)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____5956) ->
                     let e0 =
                       let uu____5978 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg
                         env.FStar_SMTEncoding_Env.tcenv head1 uu____5978
                        in
                     ((let uu____5988 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug
                              env.FStar_SMTEncoding_Env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____5988
                       then
                         let uu____5993 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____5993
                       else ());
                      (let e =
                         let uu____6001 =
                           let uu____6006 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____6007 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____6006
                             uu____6007
                            in
                         uu____6001 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____6018),(arg,uu____6020)::[]) -> encode_term arg env
                 | uu____6055 ->
                     let uu____6070 = encode_args args_e env  in
                     (match uu____6070 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____6131 = encode_term head1 env  in
                            match uu____6131 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____6203 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____6203 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____6301  ->
                                                 fun uu____6302  ->
                                                   match (uu____6301,
                                                           uu____6302)
                                                   with
                                                   | ((bv,uu____6332),
                                                      (a,uu____6334)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____6364 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____6364
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____6365 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm
                                             in
                                          (match uu____6365 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type
                                                  in
                                               let e_typing =
                                                 let uu____6380 =
                                                   let uu____6388 =
                                                     FStar_SMTEncoding_Term.mkForall
                                                       t0.FStar_Syntax_Syntax.pos
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____6397 =
                                                     let uu____6399 =
                                                       let uu____6401 =
                                                         let uu____6403 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm
                                                            in
                                                         FStar_Util.digest_of_string
                                                           uu____6403
                                                          in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____6401
                                                        in
                                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                       uu____6399
                                                      in
                                                   (uu____6388,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____6397)
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____6380
                                                  in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing])))))))
                             in
                          let encode_full_app fv =
                            let prims_connectives =
                              let mkBoxLogical t1 =
                                FStar_SMTEncoding_Util.mkApp
                                  ("BoxLogical", [t1])
                                 in
                              let mk_unary_logical_connective interp
                                uu___362_6468 =
                                match uu___362_6468 with
                                | t1::[] ->
                                    let uu____6472 =
                                      let uu____6473 =
                                        FStar_SMTEncoding_Term.mk_Valid t1
                                         in
                                      interp uu____6473  in
                                    mkBoxLogical uu____6472
                                | uu____6474 ->
                                    failwith
                                      "Impossible: expected logical unary connective to be applied to one argument"
                                 in
                              let mk_binary_logical_connective interp
                                uu___363_6507 =
                                match uu___363_6507 with
                                | t1::t2::[] ->
                                    let uu____6512 =
                                      let uu____6513 =
                                        let uu____6518 =
                                          FStar_SMTEncoding_Term.mk_Valid t1
                                           in
                                        let uu____6519 =
                                          FStar_SMTEncoding_Term.mk_Valid t2
                                           in
                                        (uu____6518, uu____6519)  in
                                      interp uu____6513  in
                                    mkBoxLogical uu____6512
                                | uu____6520 ->
                                    failwith
                                      "Impossible: mk_binary_logical_connective expects two arguments only"
                                 in
                              let mk_unary_boolean_connective interp
                                uu___364_6545 =
                                match uu___364_6545 with
                                | t1::[] ->
                                    let uu____6549 =
                                      let uu____6550 =
                                        FStar_SMTEncoding_Term.unboxBool t1
                                         in
                                      interp uu____6550  in
                                    FStar_SMTEncoding_Term.boxBool uu____6549
                                | uu____6551 ->
                                    failwith
                                      "Impossible: expected boolean unary connective to be applied to one argument"
                                 in
                              let mk_binary_boolean_connective interp
                                uu___365_6584 =
                                match uu___365_6584 with
                                | t1::t2::[] ->
                                    let uu____6589 =
                                      let uu____6590 =
                                        let uu____6595 =
                                          FStar_SMTEncoding_Term.unboxBool t1
                                           in
                                        let uu____6596 =
                                          FStar_SMTEncoding_Term.unboxBool t2
                                           in
                                        (uu____6595, uu____6596)  in
                                      interp uu____6590  in
                                    FStar_SMTEncoding_Term.boxBool uu____6589
                                | uu____6597 ->
                                    failwith
                                      "Impossible: expected boolean binary connective to be applied to two arguments"
                                 in
                              let uu____6601 =
                                let uu____6611 =
                                  mk_binary_logical_connective
                                    FStar_SMTEncoding_Util.mkAnd
                                   in
                                (FStar_Parser_Const.and_lid, uu____6611)  in
                              let uu____6623 =
                                let uu____6635 =
                                  let uu____6645 =
                                    mk_binary_logical_connective
                                      FStar_SMTEncoding_Util.mkOr
                                     in
                                  (FStar_Parser_Const.or_lid, uu____6645)  in
                                let uu____6657 =
                                  let uu____6669 =
                                    let uu____6679 =
                                      mk_binary_logical_connective
                                        FStar_SMTEncoding_Util.mkImp
                                       in
                                    (FStar_Parser_Const.imp_lid, uu____6679)
                                     in
                                  let uu____6691 =
                                    let uu____6703 =
                                      let uu____6713 =
                                        mk_binary_logical_connective
                                          FStar_SMTEncoding_Util.mkIff
                                         in
                                      (FStar_Parser_Const.iff_lid,
                                        uu____6713)
                                       in
                                    let uu____6725 =
                                      let uu____6737 =
                                        let uu____6747 =
                                          mk_unary_logical_connective
                                            FStar_SMTEncoding_Util.mkNot
                                           in
                                        (FStar_Parser_Const.not_lid,
                                          uu____6747)
                                         in
                                      let uu____6759 =
                                        let uu____6771 =
                                          let uu____6781 =
                                            mk_binary_boolean_connective
                                              FStar_SMTEncoding_Util.mkAnd
                                             in
                                          (FStar_Parser_Const.op_And,
                                            uu____6781)
                                           in
                                        let uu____6793 =
                                          let uu____6805 =
                                            let uu____6815 =
                                              mk_binary_boolean_connective
                                                FStar_SMTEncoding_Util.mkOr
                                               in
                                            (FStar_Parser_Const.op_Or,
                                              uu____6815)
                                             in
                                          let uu____6827 =
                                            let uu____6839 =
                                              let uu____6849 =
                                                mk_unary_boolean_connective
                                                  FStar_SMTEncoding_Util.mkNot
                                                 in
                                              (FStar_Parser_Const.op_Negation,
                                                uu____6849)
                                               in
                                            [uu____6839]  in
                                          uu____6805 :: uu____6827  in
                                        uu____6771 :: uu____6793  in
                                      uu____6737 :: uu____6759  in
                                    uu____6703 :: uu____6725  in
                                  uu____6669 :: uu____6691  in
                                uu____6635 :: uu____6657  in
                              uu____6601 :: uu____6623  in
                            let uu____6942 =
                              FStar_Util.find_opt
                                (fun uu____6966  ->
                                   match uu____6966 with
                                   | (l,uu____6977) ->
                                       FStar_Ident.lid_equals l
                                         fv.FStar_Syntax_Syntax.v)
                                prims_connectives
                               in
                            match uu____6942 with
                            | FStar_Pervasives_Native.Some (uu____6992,f) ->
                                let uu____7013 = f args  in
                                (uu____7013, decls)
                            | FStar_Pervasives_Native.None  ->
                                let uu____7023 =
                                  FStar_SMTEncoding_Env.lookup_free_var_sym
                                    env fv
                                   in
                                (match uu____7023 with
                                 | (fname,fuel_args,arity) ->
                                     let tm =
                                       maybe_curry_app
                                         t0.FStar_Syntax_Syntax.pos fname
                                         arity
                                         (FStar_List.append fuel_args args)
                                        in
                                     (tm, decls))
                             in
                          let head2 = FStar_Syntax_Subst.compress head1  in
                          let head_type =
                            match head2.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_uinst
                                ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_name x;
                                   FStar_Syntax_Syntax.pos = uu____7054;
                                   FStar_Syntax_Syntax.vars = uu____7055;_},uu____7056)
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
                                   FStar_Syntax_Syntax.pos = uu____7063;
                                   FStar_Syntax_Syntax.vars = uu____7064;_},uu____7065)
                                ->
                                let uu____7070 =
                                  let uu____7071 =
                                    let uu____7076 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____7076
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____7071
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____7070
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____7106 =
                                  let uu____7107 =
                                    let uu____7112 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.FStar_SMTEncoding_Env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____7112
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____7107
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____7106
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____7141,(FStar_Util.Inl t1,uu____7143),uu____7144)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____7191,(FStar_Util.Inr c,uu____7193),uu____7194)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____7241 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____7262 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Env.Weak;
                                     FStar_TypeChecker_Env.HNF;
                                     FStar_TypeChecker_Env.EraseUniverses]
                                     env.FStar_SMTEncoding_Env.tcenv
                                     head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____7262
                                  in
                               let uu____7263 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____7263 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____7279;
                                            FStar_Syntax_Syntax.vars =
                                              uu____7280;_},uu____7281)
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
                                     | uu____7299 ->
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
           let uu____7378 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____7378 with
            | (bs1,body1,opening) ->
                let fallback uu____7403 =
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
                  let uu____7413 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort)
                     in
                  (uu____7413, [decl])  in
                let is_impure rc =
                  let uu____7424 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                      env.FStar_SMTEncoding_Env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____7424 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____7439 =
                          let uu____7452 =
                            FStar_TypeChecker_Env.get_range
                              env.FStar_SMTEncoding_Env.tcenv
                             in
                          FStar_TypeChecker_Util.new_implicit_var
                            "SMTEncoding codomain" uu____7452
                            env.FStar_SMTEncoding_Env.tcenv
                            FStar_Syntax_Util.ktype0
                           in
                        (match uu____7439 with
                         | (t1,uu____7455,uu____7456) -> t1)
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  let uu____7474 =
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                     in
                  if uu____7474
                  then
                    let uu____7479 = FStar_Syntax_Syntax.mk_Total res_typ  in
                    FStar_Pervasives_Native.Some uu____7479
                  else
                    (let uu____7482 =
                       FStar_Ident.lid_equals
                         rc.FStar_Syntax_Syntax.residual_effect
                         FStar_Parser_Const.effect_GTot_lid
                        in
                     if uu____7482
                     then
                       let uu____7487 = FStar_Syntax_Syntax.mk_GTotal res_typ
                          in
                       FStar_Pervasives_Native.Some uu____7487
                     else FStar_Pervasives_Native.None)
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____7495 =
                         let uu____7501 =
                           let uu____7503 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____7503
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____7501)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____7495);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____7508 =
                       (is_impure rc) &&
                         (let uu____7511 =
                            FStar_TypeChecker_Env.is_reifiable_rc
                              env.FStar_SMTEncoding_Env.tcenv rc
                             in
                          Prims.op_Negation uu____7511)
                        in
                     if uu____7508
                     then fallback ()
                     else
                       (let cache_size =
                          FStar_Util.smap_size
                            env.FStar_SMTEncoding_Env.cache
                           in
                        let uu____7522 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____7522 with
                        | (vars,guards,envbody,decls,uu____7547) ->
                            let body2 =
                              let uu____7561 =
                                FStar_TypeChecker_Env.is_reifiable_rc
                                  env.FStar_SMTEncoding_Env.tcenv rc
                                 in
                              if uu____7561
                              then
                                FStar_TypeChecker_Util.reify_body
                                  env.FStar_SMTEncoding_Env.tcenv body1
                              else body1  in
                            let uu____7566 = encode_term body2 envbody  in
                            (match uu____7566 with
                             | (body3,decls') ->
                                 let uu____7577 =
                                   let uu____7586 = codomain_eff rc  in
                                   match uu____7586 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____7605 = encode_term tfun env
                                          in
                                       (match uu____7605 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____7577 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____7639 =
                                          let uu____7650 =
                                            let uu____7651 =
                                              let uu____7656 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____7656, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____7651
                                             in
                                          ([], vars, uu____7650)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          t0.FStar_Syntax_Syntax.pos
                                          uu____7639
                                         in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body
                                         in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            cvars
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____7680 =
                                              let uu____7688 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1
                                                 in
                                              FStar_List.append uu____7688
                                                cvars
                                               in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____7680
                                         in
                                      let tkey =
                                        FStar_SMTEncoding_Term.mkForall
                                          t0.FStar_Syntax_Syntax.pos
                                          ([], cvars1, key_body)
                                         in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey
                                         in
                                      let uu____7715 =
                                        FStar_Util.smap_try_find
                                          env.FStar_SMTEncoding_Env.cache
                                          tkey_hash
                                         in
                                      (match uu____7715 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____7723 =
                                             let uu____7724 =
                                               let uu____7732 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1
                                                  in
                                               ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name),
                                                 uu____7732)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____7724
                                              in
                                           (uu____7723,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (FStar_SMTEncoding_Env.use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____7743 =
                                             is_an_eta_expansion env vars
                                               body3
                                              in
                                           (match uu____7743 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____7752 =
                                                    let uu____7754 =
                                                      FStar_Util.smap_size
                                                        env.FStar_SMTEncoding_Env.cache
                                                       in
                                                    uu____7754 = cache_size
                                                     in
                                                  if uu____7752
                                                  then []
                                                  else
                                                    FStar_List.append decls
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
                                                    let uu____7775 =
                                                      let uu____7777 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash
                                                         in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____7777
                                                       in
                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                      uu____7775
                                                     in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym)
                                                   in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None)
                                                   in
                                                let f =
                                                  let uu____7787 =
                                                    let uu____7795 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    (fsym, uu____7795)  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____7787
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
                                                      let uu____7817 =
                                                        let uu____7818 =
                                                          let uu____7826 =
                                                            FStar_SMTEncoding_Term.mkForall
                                                              t0.FStar_Syntax_Syntax.pos
                                                              ([[f]], cvars1,
                                                                f_has_t)
                                                             in
                                                          (uu____7826,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name)
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____7818
                                                         in
                                                      [uu____7817]
                                                   in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym
                                                     in
                                                  match body3.FStar_SMTEncoding_Term.tm
                                                  with
                                                  | FStar_SMTEncoding_Term.App
                                                      (FStar_SMTEncoding_Term.Var
                                                       "BoxLogical",t1::[])
                                                      ->
                                                      let uu____7845 =
                                                        let uu____7853 =
                                                          let uu____7854 =
                                                            let uu____7865 =
                                                              let uu____7866
                                                                =
                                                                let uu____7871
                                                                  =
                                                                  FStar_SMTEncoding_Term.mk_Valid
                                                                    app
                                                                   in
                                                                (uu____7871,
                                                                  t1)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkEq
                                                                uu____7866
                                                               in
                                                            ([[app]],
                                                              (FStar_List.append
                                                                 vars cvars1),
                                                              uu____7865)
                                                             in
                                                          FStar_SMTEncoding_Term.mkForall
                                                            t0.FStar_Syntax_Syntax.pos
                                                            uu____7854
                                                           in
                                                        (uu____7853,
                                                          (FStar_Pervasives_Native.Some
                                                             a_name), a_name)
                                                         in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____7845
                                                  | uu____7882 ->
                                                      let uu____7883 =
                                                        let uu____7891 =
                                                          let uu____7892 =
                                                            let uu____7903 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app, body3)
                                                               in
                                                            ([[app]],
                                                              (FStar_List.append
                                                                 vars cvars1),
                                                              uu____7903)
                                                             in
                                                          FStar_SMTEncoding_Term.mkForall
                                                            t0.FStar_Syntax_Syntax.pos
                                                            uu____7892
                                                           in
                                                        (uu____7891,
                                                          (FStar_Pervasives_Native.Some
                                                             a_name), a_name)
                                                         in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____7883
                                                   in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f])))
                                                   in
                                                ((let uu____7918 =
                                                    FStar_SMTEncoding_Env.mk_cache_entry
                                                      env fsym cvar_sorts
                                                      f_decls
                                                     in
                                                  FStar_Util.smap_add
                                                    env.FStar_SMTEncoding_Env.cache
                                                    tkey_hash uu____7918);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____7919,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____7920;
                          FStar_Syntax_Syntax.lbunivs = uu____7921;
                          FStar_Syntax_Syntax.lbtyp = uu____7922;
                          FStar_Syntax_Syntax.lbeff = uu____7923;
                          FStar_Syntax_Syntax.lbdef = uu____7924;
                          FStar_Syntax_Syntax.lbattrs = uu____7925;
                          FStar_Syntax_Syntax.lbpos = uu____7926;_}::uu____7927),uu____7928)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____7962;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____7964;
                FStar_Syntax_Syntax.lbdef = e1;
                FStar_Syntax_Syntax.lbattrs = uu____7966;
                FStar_Syntax_Syntax.lbpos = uu____7967;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____7994 ->
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
              let uu____8066 =
                let uu____8071 =
                  FStar_Syntax_Util.ascribe e1
                    ((FStar_Util.Inl t1), FStar_Pervasives_Native.None)
                   in
                encode_term uu____8071 env  in
              match uu____8066 with
              | (ee1,decls1) ->
                  let uu____8096 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____8096 with
                   | (xs,e21) ->
                       let uu____8121 = FStar_List.hd xs  in
                       (match uu____8121 with
                        | (x1,uu____8139) ->
                            let env' =
                              FStar_SMTEncoding_Env.push_term_var env x1 ee1
                               in
                            let uu____8145 = encode_body e21 env'  in
                            (match uu____8145 with
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
            let uu____8175 =
              let uu____8183 =
                let uu____8184 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____8184  in
              FStar_SMTEncoding_Env.gen_term_var env uu____8183  in
            match uu____8175 with
            | (scrsym,scr',env1) ->
                let uu____8194 = encode_term e env1  in
                (match uu____8194 with
                 | (scr,decls) ->
                     let uu____8205 =
                       let encode_branch b uu____8234 =
                         match uu____8234 with
                         | (else_case,decls1) ->
                             let uu____8253 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____8253 with
                              | (p,w,br) ->
                                  let uu____8279 = encode_pat env1 p  in
                                  (match uu____8279 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____8316  ->
                                                   match uu____8316 with
                                                   | (x,t) ->
                                                       FStar_SMTEncoding_Env.push_term_var
                                                         env2 x t) env1)
                                          in
                                       let uu____8323 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____8345 =
                                               encode_term w1 env2  in
                                             (match uu____8345 with
                                              | (w2,decls2) ->
                                                  let uu____8358 =
                                                    let uu____8359 =
                                                      let uu____8364 =
                                                        let uu____8365 =
                                                          let uu____8370 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____8370)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____8365
                                                         in
                                                      (guard, uu____8364)  in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____8359
                                                     in
                                                  (uu____8358, decls2))
                                          in
                                       (match uu____8323 with
                                        | (guard1,decls2) ->
                                            let uu____8385 =
                                              encode_br br env2  in
                                            (match uu____8385 with
                                             | (br1,decls3) ->
                                                 let uu____8398 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____8398,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____8205 with
                      | (match_tm,decls1) ->
                          let uu____8419 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange
                             in
                          (uu____8419, decls1)))

and (encode_pat :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.pat -> (FStar_SMTEncoding_Env.env_t * pattern))
  =
  fun env  ->
    fun pat  ->
      (let uu____8442 =
         FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv
           FStar_Options.Medium
          in
       if uu____8442
       then
         let uu____8445 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____8445
       else ());
      (let uu____8450 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____8450 with
       | (vars,pat_term) ->
           let uu____8467 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____8523  ->
                     fun v1  ->
                       match uu____8523 with
                       | (env1,vars1) ->
                           let uu____8579 =
                             FStar_SMTEncoding_Env.gen_term_var env1 v1  in
                           (match uu____8579 with
                            | (xx,uu____8603,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, []))
              in
           (match uu____8467 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____8696 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____8697 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____8698 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____8706 = encode_const c env1  in
                      (match uu____8706 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____8714::uu____8715 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____8719 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon
                            env1.FStar_SMTEncoding_Env.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____8742 =
                          FStar_TypeChecker_Env.datacons_of_typ
                            env1.FStar_SMTEncoding_Env.tcenv tc_name
                           in
                        match uu____8742 with
                        | (uu____8750,uu____8751::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____8756 ->
                            FStar_SMTEncoding_Env.mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____8792  ->
                                  match uu____8792 with
                                  | (arg,uu____8802) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____8811 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____8811))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____8843) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____8874 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____8899 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____8945  ->
                                  match uu____8945 with
                                  | (arg,uu____8961) ->
                                      let proj =
                                        FStar_SMTEncoding_Env.primitive_projector_by_pos
                                          env1.FStar_SMTEncoding_Env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____8970 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____8970))
                         in
                      FStar_All.pipe_right uu____8899 FStar_List.flatten
                   in
                let pat_term1 uu____9001 = encode_term pat_term env1  in
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
      let uu____9011 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9059  ->
                fun uu____9060  ->
                  match (uu____9059, uu____9060) with
                  | ((tms,decls),(t,uu____9100)) ->
                      let uu____9127 = encode_term t env  in
                      (match uu____9127 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____9011 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____9184 = FStar_Syntax_Util.list_elements e  in
        match uu____9184 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____9215 =
          let uu____9232 = FStar_Syntax_Util.unmeta p  in
          FStar_All.pipe_right uu____9232 FStar_Syntax_Util.head_and_args  in
        match uu____9215 with
        | (head1,args) ->
            let uu____9283 =
              let uu____9298 =
                let uu____9299 = FStar_Syntax_Util.un_uinst head1  in
                uu____9299.FStar_Syntax_Syntax.n  in
              (uu____9298, args)  in
            (match uu____9283 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____9321,uu____9322)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____9374 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or1 t1 =
          let uu____9429 =
            let uu____9446 = FStar_Syntax_Util.unmeta t1  in
            FStar_All.pipe_right uu____9446 FStar_Syntax_Util.head_and_args
             in
          match uu____9429 with
          | (head1,args) ->
              let uu____9493 =
                let uu____9508 =
                  let uu____9509 = FStar_Syntax_Util.un_uinst head1  in
                  uu____9509.FStar_Syntax_Syntax.n  in
                (uu____9508, args)  in
              (match uu____9493 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____9528)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____9565 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____9595 = smt_pat_or1 t1  in
            (match uu____9595 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____9617 = list_elements1 e  in
                 FStar_All.pipe_right uu____9617
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____9647 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____9647
                           (FStar_List.map one_pat)))
             | uu____9670 ->
                 let uu____9675 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____9675])
        | uu____9726 ->
            let uu____9729 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____9729]
         in
      let uu____9780 =
        let uu____9795 =
          let uu____9796 = FStar_Syntax_Subst.compress t  in
          uu____9796.FStar_Syntax_Syntax.n  in
        match uu____9795 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____9835 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____9835 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____9870;
                        FStar_Syntax_Syntax.effect_name = uu____9871;
                        FStar_Syntax_Syntax.result_typ = uu____9872;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____9874)::(post,uu____9876)::(pats,uu____9878)::[];
                        FStar_Syntax_Syntax.flags = uu____9879;_}
                      ->
                      let uu____9940 = lemma_pats pats  in
                      (binders1, pre, post, uu____9940)
                  | uu____9951 -> failwith "impos"))
        | uu____9967 -> failwith "Impos"  in
      match uu____9780 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___372_10004 = env  in
            {
              FStar_SMTEncoding_Env.bvar_bindings =
                (uu___372_10004.FStar_SMTEncoding_Env.bvar_bindings);
              FStar_SMTEncoding_Env.fvar_bindings =
                (uu___372_10004.FStar_SMTEncoding_Env.fvar_bindings);
              FStar_SMTEncoding_Env.depth =
                (uu___372_10004.FStar_SMTEncoding_Env.depth);
              FStar_SMTEncoding_Env.tcenv =
                (uu___372_10004.FStar_SMTEncoding_Env.tcenv);
              FStar_SMTEncoding_Env.warn =
                (uu___372_10004.FStar_SMTEncoding_Env.warn);
              FStar_SMTEncoding_Env.cache =
                (uu___372_10004.FStar_SMTEncoding_Env.cache);
              FStar_SMTEncoding_Env.nolabels =
                (uu___372_10004.FStar_SMTEncoding_Env.nolabels);
              FStar_SMTEncoding_Env.use_zfuel_name = true;
              FStar_SMTEncoding_Env.encode_non_total_function_typ =
                (uu___372_10004.FStar_SMTEncoding_Env.encode_non_total_function_typ);
              FStar_SMTEncoding_Env.current_module_name =
                (uu___372_10004.FStar_SMTEncoding_Env.current_module_name);
              FStar_SMTEncoding_Env.encoding_quantifier =
                (uu___372_10004.FStar_SMTEncoding_Env.encoding_quantifier)
            }  in
          let uu____10006 =
            encode_binders FStar_Pervasives_Native.None binders env1  in
          (match uu____10006 with
           | (vars,guards,env2,decls,uu____10031) ->
               let uu____10044 = encode_smt_patterns patterns env2  in
               (match uu____10044 with
                | (pats,decls') ->
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
                    let env3 =
                      let uu___373_10077 = env2  in
                      {
                        FStar_SMTEncoding_Env.bvar_bindings =
                          (uu___373_10077.FStar_SMTEncoding_Env.bvar_bindings);
                        FStar_SMTEncoding_Env.fvar_bindings =
                          (uu___373_10077.FStar_SMTEncoding_Env.fvar_bindings);
                        FStar_SMTEncoding_Env.depth =
                          (uu___373_10077.FStar_SMTEncoding_Env.depth);
                        FStar_SMTEncoding_Env.tcenv =
                          (uu___373_10077.FStar_SMTEncoding_Env.tcenv);
                        FStar_SMTEncoding_Env.warn =
                          (uu___373_10077.FStar_SMTEncoding_Env.warn);
                        FStar_SMTEncoding_Env.cache =
                          (uu___373_10077.FStar_SMTEncoding_Env.cache);
                        FStar_SMTEncoding_Env.nolabels = true;
                        FStar_SMTEncoding_Env.use_zfuel_name =
                          (uu___373_10077.FStar_SMTEncoding_Env.use_zfuel_name);
                        FStar_SMTEncoding_Env.encode_non_total_function_typ =
                          (uu___373_10077.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                        FStar_SMTEncoding_Env.current_module_name =
                          (uu___373_10077.FStar_SMTEncoding_Env.current_module_name);
                        FStar_SMTEncoding_Env.encoding_quantifier =
                          (uu___373_10077.FStar_SMTEncoding_Env.encoding_quantifier)
                      }  in
                    let uu____10079 =
                      let uu____10084 = FStar_Syntax_Util.unmeta pre  in
                      encode_formula uu____10084 env3  in
                    (match uu____10079 with
                     | (pre1,decls'') ->
                         let uu____10091 =
                           let uu____10096 = FStar_Syntax_Util.unmeta post1
                              in
                           encode_formula uu____10096 env3  in
                         (match uu____10091 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append decls'
                                     (FStar_List.append decls'' decls'''))
                                 in
                              let uu____10106 =
                                let uu____10107 =
                                  let uu____10118 =
                                    let uu____10119 =
                                      let uu____10124 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards)
                                         in
                                      (uu____10124, post2)  in
                                    FStar_SMTEncoding_Util.mkImp uu____10119
                                     in
                                  (pats, vars, uu____10118)  in
                                FStar_SMTEncoding_Term.mkForall
                                  t.FStar_Syntax_Syntax.pos uu____10107
                                 in
                              (uu____10106, decls1)))))

and (encode_smt_patterns :
  FStar_Syntax_Syntax.arg Prims.list Prims.list ->
    FStar_SMTEncoding_Env.env_t ->
      (FStar_SMTEncoding_Term.term Prims.list Prims.list *
        FStar_SMTEncoding_Term.decl Prims.list))
  =
  fun pats_l  ->
    fun env  ->
      let env1 =
        let uu___374_10146 = env  in
        {
          FStar_SMTEncoding_Env.bvar_bindings =
            (uu___374_10146.FStar_SMTEncoding_Env.bvar_bindings);
          FStar_SMTEncoding_Env.fvar_bindings =
            (uu___374_10146.FStar_SMTEncoding_Env.fvar_bindings);
          FStar_SMTEncoding_Env.depth =
            (uu___374_10146.FStar_SMTEncoding_Env.depth);
          FStar_SMTEncoding_Env.tcenv =
            (uu___374_10146.FStar_SMTEncoding_Env.tcenv);
          FStar_SMTEncoding_Env.warn =
            (uu___374_10146.FStar_SMTEncoding_Env.warn);
          FStar_SMTEncoding_Env.cache =
            (uu___374_10146.FStar_SMTEncoding_Env.cache);
          FStar_SMTEncoding_Env.nolabels =
            (uu___374_10146.FStar_SMTEncoding_Env.nolabels);
          FStar_SMTEncoding_Env.use_zfuel_name = true;
          FStar_SMTEncoding_Env.encode_non_total_function_typ =
            (uu___374_10146.FStar_SMTEncoding_Env.encode_non_total_function_typ);
          FStar_SMTEncoding_Env.current_module_name =
            (uu___374_10146.FStar_SMTEncoding_Env.current_module_name);
          FStar_SMTEncoding_Env.encoding_quantifier =
            (uu___374_10146.FStar_SMTEncoding_Env.encoding_quantifier)
        }  in
      let encode_smt_pattern t =
        let uu____10162 = FStar_Syntax_Util.head_and_args t  in
        match uu____10162 with
        | (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____10225::(x,uu____10227)::(t1,uu____10229)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____10296 = encode_term x env1  in
                 (match uu____10296 with
                  | (x1,decls) ->
                      let uu____10307 = encode_term t1 env1  in
                      (match uu____10307 with
                       | (t2,decls') ->
                           let uu____10318 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                           (uu____10318, (FStar_List.append decls decls'))))
             | uu____10319 -> encode_term t env1)
         in
      FStar_List.fold_right
        (fun pats  ->
           fun uu____10362  ->
             match uu____10362 with
             | (pats_l1,decls) ->
                 let uu____10407 =
                   FStar_List.fold_right
                     (fun uu____10442  ->
                        fun uu____10443  ->
                          match (uu____10442, uu____10443) with
                          | ((p,uu____10485),(pats1,decls1)) ->
                              let uu____10520 = encode_smt_pattern p  in
                              (match uu____10520 with
                               | (t,d) ->
                                   let uu____10535 =
                                     FStar_SMTEncoding_Term.check_pattern_ok
                                       t
                                      in
                                   (match uu____10535 with
                                    | FStar_Pervasives_Native.None  ->
                                        ((t :: pats1),
                                          (FStar_List.append d decls1))
                                    | FStar_Pervasives_Native.Some
                                        illegal_subterm ->
                                        ((let uu____10552 =
                                            let uu____10558 =
                                              let uu____10560 =
                                                FStar_Syntax_Print.term_to_string
                                                  p
                                                 in
                                              let uu____10562 =
                                                FStar_SMTEncoding_Term.print_smt_term
                                                  illegal_subterm
                                                 in
                                              FStar_Util.format2
                                                "Pattern %s contains illegal sub-term (%s); dropping it"
                                                uu____10560 uu____10562
                                               in
                                            (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                                              uu____10558)
                                             in
                                          FStar_Errors.log_issue
                                            p.FStar_Syntax_Syntax.pos
                                            uu____10552);
                                         (pats1,
                                           (FStar_List.append d decls1))))))
                     pats ([], decls)
                    in
                 (match uu____10407 with
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
        let uu____10622 =
          FStar_All.pipe_left
            (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____10622
        then
          let uu____10627 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____10629 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10627 uu____10629
        else ()  in
      let enc f r l =
        let uu____10671 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10703 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____10703 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____10671 with
        | (decls,args) ->
            let uu____10734 =
              let uu___375_10735 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___375_10735.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___375_10735.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10734, decls)
         in
      let const_op f r uu____10770 =
        let uu____10783 = f r  in (uu____10783, [])  in
      let un_op f l =
        let uu____10806 = FStar_List.hd l  in
        FStar_All.pipe_left f uu____10806  in
      let bin_op f uu___366_10826 =
        match uu___366_10826 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10837 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____10878 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____10903  ->
                 match uu____10903 with
                 | (t,uu____10919) ->
                     let uu____10924 = encode_formula t env  in
                     (match uu____10924 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____10878 with
        | (decls,phis) ->
            let uu____10953 =
              let uu___376_10954 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___376_10954.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___376_10954.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10953, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____11017  ->
               match uu____11017 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____11038) -> false
                    | uu____11041 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____11060 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____11060
        else
          (let uu____11077 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____11077 r rf)
         in
      let eq3_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____11149 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::t1::v0::v1::[] ->
                     let uu____11181 =
                       let uu____11186 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____11187 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____11186, uu____11187)  in
                     FStar_SMTEncoding_Util.mkAnd uu____11181
                 | uu____11188 -> failwith "Impossible")
             in
          uu____11149 r args
        else
          (let uu____11194 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____11194)
         in
      let h_equals_op r args =
        let n1 = FStar_List.length args  in
        if n1 = (Prims.parse_int "4")
        then
          let uu____11266 =
            enc
              (fun terms  ->
                 match terms with
                 | t0::v0::t1::v1::[] ->
                     let uu____11298 =
                       let uu____11303 = FStar_SMTEncoding_Util.mkEq (t0, t1)
                          in
                       let uu____11304 = FStar_SMTEncoding_Util.mkEq (v0, v1)
                          in
                       (uu____11303, uu____11304)  in
                     FStar_SMTEncoding_Util.mkAnd uu____11298
                 | uu____11305 -> failwith "Impossible")
             in
          uu____11266 r args
        else
          (let uu____11311 =
             FStar_Util.format1
               "eq3_op: got %s non-implicit arguments instead of 4?"
               (Prims.string_of_int n1)
              in
           failwith uu____11311)
         in
      let mk_imp1 r uu___367_11346 =
        match uu___367_11346 with
        | (lhs,uu____11352)::(rhs,uu____11354)::[] ->
            let uu____11395 = encode_formula rhs env  in
            (match uu____11395 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11410) ->
                      (l1, decls1)
                  | uu____11415 ->
                      let uu____11416 = encode_formula lhs env  in
                      (match uu____11416 with
                       | (l2,decls2) ->
                           let uu____11427 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____11427, (FStar_List.append decls1 decls2)))))
        | uu____11428 -> failwith "impossible"  in
      let mk_ite r uu___368_11456 =
        match uu___368_11456 with
        | (guard,uu____11462)::(_then,uu____11464)::(_else,uu____11466)::[]
            ->
            let uu____11523 = encode_formula guard env  in
            (match uu____11523 with
             | (g,decls1) ->
                 let uu____11534 = encode_formula _then env  in
                 (match uu____11534 with
                  | (t,decls2) ->
                      let uu____11545 = encode_formula _else env  in
                      (match uu____11545 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11557 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____11587 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l
           in
        f uu____11587  in
      let connectives =
        let uu____11617 =
          let uu____11642 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____11642)  in
        let uu____11685 =
          let uu____11712 =
            let uu____11737 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____11737)  in
          let uu____11780 =
            let uu____11807 =
              let uu____11834 =
                let uu____11859 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____11859)  in
              let uu____11902 =
                let uu____11929 =
                  let uu____11956 =
                    let uu____11981 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____11981)  in
                  [uu____11956;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.c_eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq3_op);
                  (FStar_Parser_Const.c_eq3_lid, h_equals_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11929  in
              uu____11834 :: uu____11902  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11807  in
          uu____11712 :: uu____11780  in
        uu____11617 :: uu____11685  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____12526 = encode_formula phi' env  in
            (match uu____12526 with
             | (phi2,decls) ->
                 let uu____12537 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____12537, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____12539 ->
            let uu____12546 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____12546 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____12585 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____12585 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____12597;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____12599;
                 FStar_Syntax_Syntax.lbdef = e1;
                 FStar_Syntax_Syntax.lbattrs = uu____12601;
                 FStar_Syntax_Syntax.lbpos = uu____12602;_}::[]),e2)
            ->
            let uu____12629 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____12629 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____12682::(x,uu____12684)::(t,uu____12686)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12753 = encode_term x env  in
                 (match uu____12753 with
                  | (x1,decls) ->
                      let uu____12764 = encode_term t env  in
                      (match uu____12764 with
                       | (t1,decls') ->
                           let uu____12775 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____12775, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12778)::(msg,uu____12780)::(phi2,uu____12782)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12849 =
                   let uu____12854 =
                     let uu____12855 = FStar_Syntax_Subst.compress r  in
                     uu____12855.FStar_Syntax_Syntax.n  in
                   let uu____12858 =
                     let uu____12859 = FStar_Syntax_Subst.compress msg  in
                     uu____12859.FStar_Syntax_Syntax.n  in
                   (uu____12854, uu____12858)  in
                 (match uu____12849 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12868))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____12879 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____12886)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____12921 when head_redex env head2 ->
                 let uu____12936 = whnf env phi1  in
                 encode_formula uu____12936 env
             | uu____12937 ->
                 let uu____12952 = encode_term phi1 env  in
                 (match uu____12952 with
                  | (tt,decls) ->
                      let tt1 =
                        let uu____12964 =
                          let uu____12966 =
                            FStar_Range.use_range
                              tt.FStar_SMTEncoding_Term.rng
                             in
                          let uu____12967 =
                            FStar_Range.use_range
                              phi1.FStar_Syntax_Syntax.pos
                             in
                          FStar_Range.rng_included uu____12966 uu____12967
                           in
                        if uu____12964
                        then tt
                        else
                          (let uu___377_12971 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___377_12971.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___377_12971.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      let uu____12972 = FStar_SMTEncoding_Term.mk_Valid tt1
                         in
                      (uu____12972, decls)))
        | uu____12973 ->
            let uu____12974 = encode_term phi1 env  in
            (match uu____12974 with
             | (tt,decls) ->
                 let tt1 =
                   let uu____12986 =
                     let uu____12988 =
                       FStar_Range.use_range tt.FStar_SMTEncoding_Term.rng
                        in
                     let uu____12989 =
                       FStar_Range.use_range phi1.FStar_Syntax_Syntax.pos  in
                     FStar_Range.rng_included uu____12988 uu____12989  in
                   if uu____12986
                   then tt
                   else
                     (let uu___378_12993 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___378_12993.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___378_12993.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 let uu____12994 = FStar_SMTEncoding_Term.mk_Valid tt1  in
                 (uu____12994, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____13038 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____13038 with
        | (vars,guards,env2,decls,uu____13077) ->
            let uu____13090 = encode_smt_patterns ps env2  in
            (match uu____13090 with
             | (pats,decls') ->
                 let uu____13133 = encode_formula body env2  in
                 (match uu____13133 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____13165;
                             FStar_SMTEncoding_Term.rng = uu____13166;_}::[])::[]
                            when
                            let uu____13183 =
                              FStar_Ident.text_of_lid
                                FStar_Parser_Const.guard_free
                               in
                            uu____13183 = gf -> []
                        | uu____13186 -> guards  in
                      let uu____13191 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____13191, body1,
                        (FStar_List.append decls
                           (FStar_List.append decls' decls'')))))
         in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi  in
       let uu____13202 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____13202 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____13211 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____13317  ->
                     match uu____13317 with
                     | (l,uu____13342) -> FStar_Ident.lid_equals op l))
              in
           (match uu____13211 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____13411,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____13503 = encode_q_body env vars pats body  in
             match uu____13503 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____13548 =
                     let uu____13559 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____13559)  in
                   FStar_SMTEncoding_Term.mkForall
                     phi1.FStar_Syntax_Syntax.pos uu____13548
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars env vars));
            (let uu____13590 = encode_q_body env vars pats body  in
             match uu____13590 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____13634 =
                   let uu____13635 =
                     let uu____13646 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____13646)  in
                   FStar_SMTEncoding_Term.mkExists
                     phi1.FStar_Syntax_Syntax.pos uu____13635
                    in
                 (uu____13634, decls))))
